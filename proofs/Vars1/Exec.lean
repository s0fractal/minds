import Vars1.Pass1
import Vars1.Pass2

/-!
# Executable lens (Passes 1–2) over the kernel's facts

`Facts` is what the rules kernel sees about each cell, plus the authority its own fold
produced: edges with their authorization bit, and `Authorized`. `pass1`/`stale` compute
§4.2 Passes 1–2 by plain recursion over cell indices; `Vars1/ExecProof.lean` proves they
equal the model's `IsPass1` equations, `Superseded`, `Active` and `Stale = lfp Φ`.
The same code is compiled to `vars1exec` and compared with `kernel/lens.wasm`.

Cells are indices `0 … N-1` in forward topological order: every edge, reference and
acceptance payload of `w` names a smaller index (`Facts.Topo`).
-/

namespace Vars1.Exec

structure Edge where
  dst : Nat
  auth : Bool
  deriving Repr, Inhabited

structure CellF where
  isLocal : Bool := false
  isAcc : Bool := false
  isVerdict : Bool := false
  verdictInvalid : Bool := false
  origin : Nat := 0
  authorized : Bool := false
  payload : Option Nat := none
  relies : List Nat := []
  refs : List Nat := []
  sup : List Edge := []
  ret : List Edge := []
  inv : List Edge := []
  deriving Repr, Inhabited

structure Facts where
  n : Nat
  cell : Nat → CellF

/-- Every reference names an older cell. -/
structure Facts.Topo (F : Facts) : Prop where
  sup : ∀ w e, e ∈ (F.cell w).sup → e.dst < w
  ret : ∀ w e, e ∈ (F.cell w).ret → e.dst < w
  inv : ∀ w e, e ∈ (F.cell w).inv → e.dst < w
  refs : ∀ y x, x ∈ (F.cell y).refs → x < y
  payload : ∀ a x, (F.cell a).payload = some x → x < a
  relies : ∀ v d, d ∈ (F.cell v).relies → d < v
  bound : ∀ w, w < F.n ∨ F.cell w = default

/-- Authorized edge `w → v` of a kind's list. -/
def authIn (l : List Edge) (v : Nat) : Bool := l.any fun e => e.dst == v && e.auth

/-- Cells newer than `v`. -/
def above (n v : Nat) : List Nat := (List.range n).filter fun w => v < w

/-- Point update of a function on `Nat`. `noinline` keeps the compiler from moving the stored
value's computation inside the closure (it would be recomputed on every lookup). -/
@[noinline] def upd {α : Type} (g : Nat → α) (k : Nat) (x : α) : Nat → α := fun w => if w = k then x else g w

/-- Fill indices `k-1, …, 0` (newest first) with `step`, each reading the function so far. -/
def fill {α : Type} (step : (Nat → α) → Nat → α) : Nat → (Nat → α) → (Nat → α)
  | 0, g => g
  | k + 1, g => fill step k (upd g k (step g k))

/-- Fill `m` indices `i, i+1, …` (oldest first), each reading the function so far. -/
def fillUpGo {α : Type} (step : (Nat → α) → Nat → α) : Nat → Nat → (Nat → α) → (Nat → α)
  | 0, _, g => g
  | m + 1, i, g => fillUpGo step m (i + 1) (upd g i (step g i))

/-- Fill indices `0, …, k-1` (oldest first). -/
def fillUp {α : Type} (step : (Nat → α) → Nat → α) (k : Nat) (g : Nat → α) : Nat → α :=
  fillUpGo step k 0 g

/-- Materialize `g` on `0 … n-1` as an array (computed once, constant-time lookups). -/
def tab {α : Type} (n : Nat) (g : Nat → α) : Array α := Array.ofFn (n := n) fun i => g i.val

/-- Lookup with a default past the end. -/
def geta {α : Type} [Inhabited α] (a : Array α) (w : Nat) : α := a.getD w default

/-! ## Pass 1 -/

structure S1 where
  acc : Bool := false
  reach : Bool := false
  inv : Bool := false
  ret : Bool := false
  sup : Bool := false
  act : Bool := false
  deriving Repr, Inhabited, DecidableEq

variable (F : Facts)

/-- One Pass 1 cell, reading only newer cells (`above`). -/
def step1 (g0 : Nat → S1) (v : Nat) : S1 :=
  let g := fun w => if v < w then g0 w else default
  let c := F.cell v
  let src := above F.n v
  let live (w : Nat) : Bool := !(g w).inv && (g w).acc
  let inv := src.any fun w => live w && authIn (F.cell w).inv v &&
    (!(F.cell w).isVerdict || (F.cell w).verdictInvalid)
  let ret := src.any fun w => live w && authIn (F.cell w).ret v
  let sup := src.any fun w => authIn (F.cell w).sup v && (live w || (g w).sup)
  let reach := (src.any fun a => (F.cell a).isAcc && (F.cell a).isLocal && (g a).act &&
      (F.cell a).authorized && (F.cell a).payload == some v) ||
    (src.any fun y => (g y).reach && (F.cell y).refs.contains v && (F.cell y).origin == c.origin)
  let acc := c.isLocal || reach
  let act := !inv && !ret && !sup && acc && c.sup.all fun e => authIn c.sup e.dst
  { acc, reach, inv, ret, sup, act }

/-- Pass 1 for every cell. -/
def pass1 : Array S1 := tab F.n (fill (step1 F) F.n fun _ => default)

/-! ## Pass 2 (over the Pass 1 result `P`) -/

/-- `LiveAcceptedScopes(x) ≠ ∅` for stale set `S` (round start), newest first. -/
def stepLive (P : Array S1) (S : Array Bool) (g0 : Nat → Bool) (x : Nat) : Bool :=
  let g := fun w => if x < w then g0 w else false
  let src := above F.n x
  (src.any fun a => (F.cell a).isAcc && (F.cell a).isLocal && (geta P a).act &&
      (F.cell a).authorized && !(geta S a) && (F.cell a).payload == some x) ||
  (src.any fun y => g y && (F.cell y).refs.contains x && (F.cell y).origin == (F.cell x).origin)

def live (P : Array S1) (S : Array Bool) : Array Bool :=
  tab F.n (fill (stepLive F P S) F.n fun _ => false)

/-- The Pass 2 right-hand side: live acceptance `lv`, dependencies read from `D`. -/
def psi (P : Array S1) (lv : Array Bool) (D : Nat → Bool) (v : Nat) : Bool :=
  (geta P v).act &&
    (((F.cell v).relies.any fun d => !(geta P d).act || D d) || (!(F.cell v).isLocal && !(geta lv v)))

/-- One spec round from `S`: live acceptance fixed from `S`, then oldest first, in place. -/
def round (P : Array S1) (S : Array Bool) : Array Bool :=
  let lv := live F P S
  tab F.n (fillUp (psi F P lv) F.n (geta S))

/-- `Stale`: `N` rounds from the empty set. -/
def staleOf (P : Array S1) : Array Bool := Nat.repeat (round F P) F.n (tab F.n fun _ => false)

def stale : Array Bool := staleOf F (pass1 F)

/-- Status byte as the kernel encodes it. -/
def statusByte (P : Array S1) (st : Array Bool) (v : Nat) : Nat :=
  let s := geta P v
  (if s.acc then 1 else 0) + (if s.inv then 2 else 0) + (if !s.inv then 4 else 0) +
  (if s.ret then 8 else 0) + (if s.sup then 16 else 0) + (if s.act then 32 else 0) +
  (if geta st v then 64 else 0)

/-- Every cell's status byte, Pass 1 and Pass 2 computed once. -/
def statuses : List Nat :=
  let P := pass1 F
  let st := staleOf F P
  (List.range F.n).map (statusByte P st)

end Vars1.Exec
