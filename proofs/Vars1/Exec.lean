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

/-! ### Compiled forms of `fill` and `fillUp`

`fill` and `fillUp` build their result as nested `upd` closures, so one lookup walks up to `n` of them, and the lens
looks up every cell from every newer one in each of its `n` rounds: compiled as written, `vars1exec` took seconds at
75 cells and did not finish at the live chain's size. The compiler runs `fillFast` and `fillUpFast` instead, which
keep the values filled so far in an array. `fill_eq_fast` and `fillUp_eq_fast` prove them equal to `fill` and
`fillUp` (`@[csimp]`: the compiler substitutes a constant only by a proved equal one), so what `ExecProof.lean` proves
of `fill` holds of the compiled code. -/

theorem getD_set! {α : Type} (a : Array α) (i w : Nat) (d x : α) (h : i < a.size) :
    (a.set! i x).getD w d = if w = i then x else a.getD w d := by
  simp [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hw : w = i
  · subst hw; simp [h]
  · simp [hw, Ne.symm hw]

theorem size_set! {α : Type} (a : Array α) (i : Nat) (x : α) : (a.set! i x).size = a.size := by
  simp [Array.set!]

theorem getD_ofFn {α : Type} (k : Nat) (g : Nat → α) (w : Nat) :
    (Array.ofFn (n := k) fun j => g j.val).getD w (g w) = g w := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases hw : w < k <;> simp [hw]

def fillFastGo {α : Type} (step : (Nat → α) → Nat → α) (g : Nat → α) : Nat → Array α → Nat → α
  | 0, a => fun w => a.getD w (g w)
  | i + 1, a => fillFastGo step g i (a.set! i (step (fun w => a.getD w (g w)) i))

def fillFast {α : Type} (step : (Nat → α) → Nat → α) (k : Nat) (g : Nat → α) : Nat → α :=
  fillFastGo step g k (Array.ofFn (n := k) fun j => g j.val)

theorem fill_go {α : Type} (step : (Nat → α) → Nat → α) (g : Nat → α) :
    ∀ (i : Nat) (a : Array α) (h : Nat → α), i ≤ a.size → (∀ w, a.getD w (g w) = h w) →
      fill step i h = fillFastGo step g i a
  | 0, a, h, _, hh => by funext w; simp [fill, fillFastGo, hh]
  | i + 1, a, h, hi, hh => by
    have hf : (fun w => a.getD w (g w)) = h := funext hh
    simp only [fill, fillFastGo, hf]
    apply fill_go step g i
    · rw [size_set!]; omega
    · intro w
      rw [getD_set! a i w (g w) _ (by omega), upd]
      by_cases hw : w = i <;> simp [hw, hh]

@[csimp] theorem fill_eq_fast : @fill = @fillFast := by
  funext α step k g
  exact fill_go step g k _ g (by simp) (getD_ofFn k g)

def fillUpFastGo {α : Type} (step : (Nat → α) → Nat → α) (g : Nat → α) : Nat → Nat → Array α → Nat → α
  | 0, _, a => fun w => a.getD w (g w)
  | m + 1, i, a => fillUpFastGo step g m (i + 1) (a.set! i (step (fun w => a.getD w (g w)) i))

def fillUpFast {α : Type} (step : (Nat → α) → Nat → α) (k : Nat) (g : Nat → α) : Nat → α :=
  fillUpFastGo step g k 0 (Array.ofFn (n := k) fun j => g j.val)

theorem fillUp_go {α : Type} (step : (Nat → α) → Nat → α) (g : Nat → α) :
    ∀ (m i : Nat) (a : Array α) (h : Nat → α), i + m ≤ a.size → (∀ w, a.getD w (g w) = h w) →
      fillUpGo step m i h = fillUpFastGo step g m i a
  | 0, _, a, h, _, hh => by funext w; simp [fillUpGo, fillUpFastGo, hh]
  | m + 1, i, a, h, hi, hh => by
    have hf : (fun w => a.getD w (g w)) = h := funext hh
    simp only [fillUpGo, fillUpFastGo, hf]
    apply fillUp_go step g m (i + 1)
    · rw [size_set!]; omega
    · intro w
      rw [getD_set! a i w (g w) _ (by omega), upd]
      by_cases hw : w = i <;> simp [hw, hh]

@[csimp] theorem fillUp_eq_fast : @fillUp = @fillUpFast := by
  funext α step k g
  exact fillUp_go step g k 0 _ g (by simp) (getD_ofFn k g)

/-- Materialize `g` on `0 … n-1` as an array (computed once, constant-time lookups). -/
def tab {α : Type} (n : Nat) (g : Nat → α) : Array α := Array.ofFn (n := n) fun i => g i.val

/-- Lookup with a default past the end. -/
def geta {α : Type} [Inhabited α] (a : Array α) (w : Nat) : α := a.getD w default

/-! ### Tabulating a fill once

`fillFastGo step g k a` is a function of the index looked up, and the compiler gives it that index as a fourth
argument: `tab n (fill step n g)` then ran the whole fill again for each of its `n` entries, `n` steps that each read
up to `n` newer cells, so `vars1exec` took time cubic in the number of cells (34 s on the live chain's 1008). The
lens tabulates every fill it makes, so it calls `tabFill` and `tabFillUp`; the compiler runs `tabFillFast` and
`tabFillUpFast` instead, which fill one array once and read it (`@[csimp]`, proved equal below). -/

/-- The array `fillFastGo` reads from once its `i` steps are done. -/
def fillFastArr {α : Type} (step : (Nat → α) → Nat → α) (g : Nat → α) : Nat → Array α → Array α
  | 0, a => a
  | i + 1, a => fillFastArr step g i (a.set! i (step (fun w => a.getD w (g w)) i))

theorem fillFastGo_arr {α : Type} (step : (Nat → α) → Nat → α) (g : Nat → α) :
    ∀ (i : Nat) (a : Array α), fillFastGo step g i a = fun w => (fillFastArr step g i a).getD w (g w)
  | 0, _ => rfl
  | i + 1, _ => fillFastGo_arr step g i _

/-- The array `fillUpFastGo` reads from once its `m` steps are done. -/
def fillUpFastArr {α : Type} (step : (Nat → α) → Nat → α) (g : Nat → α) : Nat → Nat → Array α → Array α
  | 0, _, a => a
  | m + 1, i, a => fillUpFastArr step g m (i + 1) (a.set! i (step (fun w => a.getD w (g w)) i))

theorem fillUpFastGo_arr {α : Type} (step : (Nat → α) → Nat → α) (g : Nat → α) :
    ∀ (m i : Nat) (a : Array α), fillUpFastGo step g m i a = fun w => (fillUpFastArr step g m i a).getD w (g w)
  | 0, _, _ => rfl
  | m + 1, i, _ => fillUpFastGo_arr step g m (i + 1) _

/-- `fill` tabulated on `0 … k-1`. -/
def tabFill {α : Type} (step : (Nat → α) → Nat → α) (k : Nat) (g : Nat → α) : Array α := tab k (fill step k g)

/-- `fillUp` tabulated on `0 … k-1`. -/
def tabFillUp {α : Type} (step : (Nat → α) → Nat → α) (k : Nat) (g : Nat → α) : Array α := tab k (fillUp step k g)

def tabFillFast {α : Type} (step : (Nat → α) → Nat → α) (k : Nat) (g : Nat → α) : Array α :=
  let a := fillFastArr step g k (Array.ofFn (n := k) fun j => g j.val)
  Array.ofFn (n := k) fun i => a.getD i.val (g i.val)

def tabFillUpFast {α : Type} (step : (Nat → α) → Nat → α) (k : Nat) (g : Nat → α) : Array α :=
  let a := fillUpFastArr step g k 0 (Array.ofFn (n := k) fun j => g j.val)
  Array.ofFn (n := k) fun i => a.getD i.val (g i.val)

@[csimp] theorem tabFill_eq_fast : @tabFill = @tabFillFast := by
  funext α step k g
  simp only [tabFill, tabFillFast, tab, fill_eq_fast, fillFast, fillFastGo_arr]

@[csimp] theorem tabFillUp_eq_fast : @tabFillUp = @tabFillUpFast := by
  funext α step k g
  simp only [tabFillUp, tabFillUpFast, tab, fillUp_eq_fast, fillUpFast, fillUpFastGo_arr]

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
def pass1 : Array S1 := tabFill (step1 F) F.n fun _ => default

/-! ## Pass 2 (over the Pass 1 result `P`) -/

/-- `LiveAcceptedScopes(x) ≠ ∅` for stale set `S` (round start), newest first. -/
def stepLive (P : Array S1) (S : Array Bool) (g0 : Nat → Bool) (x : Nat) : Bool :=
  let g := fun w => if x < w then g0 w else false
  let src := above F.n x
  (src.any fun a => (F.cell a).isAcc && (F.cell a).isLocal && (geta P a).act &&
      (F.cell a).authorized && !(geta S a) && (F.cell a).payload == some x) ||
  (src.any fun y => g y && (F.cell y).refs.contains x && (F.cell y).origin == (F.cell x).origin)

def live (P : Array S1) (S : Array Bool) : Array Bool :=
  tabFill (stepLive F P S) F.n fun _ => false

/-- The Pass 2 right-hand side: live acceptance `lv`, dependencies read from `D`. -/
def psi (P : Array S1) (lv : Array Bool) (D : Nat → Bool) (v : Nat) : Bool :=
  (geta P v).act &&
    (((F.cell v).relies.any fun d => !(geta P d).act || D d) || (!(F.cell v).isLocal && !(geta lv v)))

/-- One spec round from `S`: live acceptance fixed from `S`, then oldest first, in place. -/
def round (P : Array S1) (S : Array Bool) : Array Bool :=
  let lv := live F P S
  tabFillUp (psi F P lv) F.n (geta S)

/-- `Stale`: `N` rounds from the empty set. -/
def staleOf (P : Array S1) : Array Bool := Nat.repeat (round F P) F.n (tab F.n fun _ => false)

/-- `k` rounds of `f` from `x`, stopping early at a round that changes nothing. -/
def repeatFix {α : Type} [DecidableEq α] (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => let y := f x; if y = x then x else repeatFix f k y

theorem repeat_succ' {α : Type} (f : α → α) : ∀ (k : Nat) (x : α), Nat.repeat f (k + 1) x = Nat.repeat f k (f x)
  | 0, _ => rfl
  | k + 1, x => by
    show f (Nat.repeat f (k + 1) x) = f (Nat.repeat f k (f x))
    rw [repeat_succ' f k x]

theorem repeat_fixed {α : Type} (f : α → α) (x : α) (h : f x = x) : ∀ k, Nat.repeat f k x = x
  | 0 => rfl
  | k + 1 => by rw [repeat_succ', h, repeat_fixed f x h k]

theorem repeatFix_eq {α : Type} [DecidableEq α] (f : α → α) : ∀ (k : Nat) (x : α), repeatFix f k x = Nat.repeat f k x
  | 0, _ => rfl
  | k + 1, x => by
    simp only [repeatFix]
    split
    · next h => rw [repeat_succ', h, repeat_fixed f x h k]
    · rw [repeatFix_eq f k, repeat_succ']

/-- Compiled form of `staleOf`: once a round changes nothing, the remaining ones would not either
(`repeatFix_eq`), so the compiler stops there (`@[csimp]`). Rounds before the fixed point are the spec's. -/
def staleOfFast (F : Facts) (P : Array S1) : Array Bool := repeatFix (round F P) F.n (tab F.n fun _ => false)

@[csimp] theorem staleOf_eq_fast : @staleOf = @staleOfFast := by
  funext F P
  simp [staleOf, staleOfFast, repeatFix_eq]

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
