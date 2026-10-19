import Vars1.Fold

/-! `vars1fold`: the model's own §4.1 fold (`Vars1.run` from `Vars1/Fold.lean`), compiled, over the kernel's facts.

One line in: `N P C S g`, then `P` policies (`threshold m key…`), `N` cells
(`schema isLocal isStd birth owner customPol pol0 pol1`, then `sup`, `ret`, `inv` as `count dst…`; policy slots are
index + 1, 0 = none), then `S` seals (`target ctx key commit`). `g` is the genesis scope cell.
Schema codes: 0 other, 1 scope, 2 acceptance, 3 contract, 4 decision, 5 question, 6 verdict, 7 metaSchema.

One line out: the governing scope index, `N` Authorized bits, then one bit per `inv`, `ret`, `sup` edge, cell by
cell in that order — the layout of the kernel's output. -/

open Vars1

structure FCell where
  schema : Schema := .other
  isLocal : Bool := false
  isStd : Bool := false
  birth : Nat := 0
  owner : Bool := false
  custom : Option Nat := none
  pol0 : Nat := 0
  pol1 : Nat := 0
  sup : List Nat := []
  ret : List Nat := []
  inv : List Nat := []
  deriving Inhabited

def schemaOfCode : Nat → Schema
  | 1 => .scope | 2 => .acceptance | 3 => .contract | 4 => .decision
  | 5 => .question | 6 => .verdict | 7 => .metaSchema | _ => .other

def takeN (n : Nat) (ts : List Nat) : Option (List Nat × List Nat) :=
  if ts.length < n then none else some (ts.take n, ts.drop n)

def takeCount (ts : List Nat) : Option (List Nat × List Nat) :=
  match ts with
  | n :: rest => takeN n rest
  | [] => none

partial def parsePols (ts : List Nat) (k : Nat) (acc : Array (Nat × List Nat)) :
    Option (Array (Nat × List Nat) × List Nat) :=
  if k = 0 then some (acc, ts) else
  match ts with
  | thr :: rest => do
    let (keys, rest) ← takeCount rest
    parsePols rest (k - 1) (acc.push (thr, keys))
  | [] => none

partial def parseCells (ts : List Nat) (k : Nat) (acc : Array FCell) : Option (Array FCell × List Nat) :=
  if k = 0 then some (acc, ts) else
  match ts with
  | sc :: loc :: std :: birth :: own :: cp :: p0 :: p1 :: rest => do
    let (sup, rest) ← takeCount rest
    let (ret, rest) ← takeCount rest
    let (inv, rest) ← takeCount rest
    let opt (x : Nat) : Option Nat := if x = 0 then none else some (x - 1)
    let c : FCell := ⟨schemaOfCode sc, loc != 0, std != 0, birth, own != 0, opt cp, p0 - 1, p1 - 1,
      sup, ret, inv⟩
    parseCells rest (k - 1) (acc.push c)
  | _ => none

partial def parseSeals (ts : List Nat) (k : Nat) (acc : Array (Seal Nat Nat × Nat)) :
    Option (Array (Seal Nat Nat × Nat)) :=
  if k = 0 then some acc else
  match ts with
  | t :: c :: key :: cm :: rest => parseSeals rest (k - 1) (acc.push (⟨t, c, key⟩, cm))
  | _ => none

def evalLine (line : String) : String := Id.run do
  let ts := (line.splitOn " ").filter (· ≠ "") |>.map String.toNat!
  let some (hdr, rest) := takeN 5 ts | return "E"
  let (n, np, nc, ns, g) := (hdr[0]!, hdr[1]!, hdr[2]!, hdr[3]!, hdr[4]!)
  let some (pols, rest) := parsePols rest np #[] | return "E"
  let some (cells, rest) := parseCells rest n #[] | return "E"
  let some seals := parseSeals rest ns #[] | return "E"
  let cell (i : Nat) : FCell := cells.getD i default
  let W : World Nat Nat Nat := {
    info := fun i =>
      let c := cell i
      { schema := c.schema, isLocal := c.isLocal, origin := 0, slotName := 0,
        relies := [], attests := [], supersedes := c.sup, retires := c.ret, invalidates := c.inv,
        refs := [], payload := none, ownerPol := c.owner, customPol := c.custom,
        verdictInvalid := false, pol0 := c.pol0, pol1 := c.pol1 }
    member := fun p k => (pols.getD p (0, [])).2.contains k
    quorum := fun E p =>
      let (thr, keys) := pols.getD p (0, [])
      0 < thr && thr ≤ ((E.eraseDups).filter keys.contains).length }
  let commits : List (Commit Nat Nat) := (List.range nc).map fun i =>
    let born := (List.range n).filter fun j => (cell j).birth == i
    { newCells := born
      seals := (seals.toList.filter fun (_, c) => c ≤ i).map (·.1)
      newScope := if i = 0 then none else
        born.find? fun j => (cell j).schema == .scope && (cell j).isLocal }
  let s0 : St Nat Nat := {
    scope := g, present := [], initEnd := fun _ => [],
    authorized := fun a => a == g || (cell a).isStd, edge := fun _ _ _ => false }
  let st := run W s0 commits
  let bit (b : Bool) : String := if b then "1" else "0"
  let mut out := #[toString st.scope]
  for a in List.range n do
    out := out.push (bit (st.authorized a))
  for w in List.range n do
    for (k, l) in [(Kind.invalidates, (cell w).inv), (Kind.retires, (cell w).ret), (Kind.supersedes, (cell w).sup)] do
      for v in l do
        out := out.push (bit (st.edge w v k))
  return " ".intercalate out.toList

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (evalLine line.trim)
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
