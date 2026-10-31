import Vars1.Witness

/-! `vars1witness`: one line in (a store and a derivation, as `experiments/witness/check.py --lean` writes them),
`ACCEPT` or `REJECT` out (`Vars1.Witness.accepts`), `E` for a line it cannot read.

Every number is a natural. Cells are `0 … N-1`; an id the store does not hold gets a number `≥ N`. A list is its
length, then its items.

* `N`, then per cell: `schema` (0 scope, 1 acceptance, 2 contract, 3 decision, 4 question, 5 verdict, 6 metaSchema,
  7 checkpoint, 8 cycleWitness, 9 computation, 10 axiom, 11 other), `isLocal`, `payload+1`, `customPol+1`,
  `attested`, `invalid`, `witnessEmpty`, `reqEmpty`, then the lists `relies`, `attests`, `supersedes`, `retires`,
  `invalidates`;
* `scope`, `pol0`; the policies (a list of `id thr keys`); the seals (a list of `target ctx key`);
* the lines (a list of `rule concl premises`: rule 0 stand, 1 endorse, 2 settle; a conclusion is `0 c`, `1 w k`
  or `2 d`; premises are a list of conclusions);
* the decision. -/

open Vars1 Vars1.Witness

abbrev Parser := StateT (List Nat) Option

def nat : Parser Nat := do
  match ← get with
  | x :: rest => set rest; pure x
  | [] => failure

def flag : Parser Bool := do
  match ← nat with
  | 0 => pure false
  | 1 => pure true
  | _ => failure

def opt : Parser (Option Nat) := do
  let x ← nat
  pure (if x = 0 then none else some (x - 1))

partial def listOf {α : Type} (p : Parser α) : Parser (List α) := do
  let n ← nat
  let rec go : Nat → List α → Parser (List α)
    | 0, acc => pure acc.reverse
    | k + 1, acc => do go k ((← p) :: acc)
  go n []

def schema : Parser Schema := do
  match ← nat with
  | 0 => pure .scope | 1 => pure .acceptance | 2 => pure .contract | 3 => pure .decision
  | 4 => pure .question | 5 => pure .verdict | 6 => pure .metaSchema | 7 => pure .checkpoint
  | 8 => pure .cycleWitness | 9 => pure .computation | 10 => pure .axiom | 11 => pure .other
  | _ => failure

structure Row where
  schema : Schema := .other
  isLocal : Bool := false
  payload : Option Nat := none
  customPol : Option Nat := none
  attested : Bool := false
  invalid : Bool := false
  witnessEmpty : Bool := true
  reqEmpty : Bool := true
  relies : List Nat := []
  attests : List Nat := []
  supersedes : List Nat := []
  retires : List Nat := []
  invalidates : List Nat := []
  deriving Inhabited

def row : Parser Row := do
  let schema ← schema
  let isLocal ← flag
  let payload ← opt
  let customPol ← opt
  let attested ← flag
  let invalid ← flag
  let witnessEmpty ← flag
  let reqEmpty ← flag
  let relies ← listOf nat
  let attests ← listOf nat
  let supersedes ← listOf nat
  let retires ← listOf nat
  let invalidates ← listOf nat
  pure { schema, isLocal, payload, customPol, attested, invalid, witnessEmpty, reqEmpty, relies, attests,
         supersedes, retires, invalidates }

def concl : Parser (Concl Nat Nat) := do
  match ← nat with
  | 0 => pure (.stands (← nat))
  | 1 => do let w ← nat; let k ← nat; pure (.endorsed w k)
  | 2 => pure (.settled (← nat))
  | _ => failure

def line : Parser (Line Nat Nat) := do
  let rule ← match ← nat with
    | 0 => pure Rule.stand
    | 1 => pure Rule.endorse
    | 2 => pure Rule.settle
    | _ => failure
  let c ← concl
  let prem ← listOf concl
  pure { rule, concl := c, prem }

def input : Parser (Store Nat Nat Nat × List (Line Nat Nat) × Nat) := do
  let rows := (← listOf row).toArray
  let scope ← nat
  let pol0 ← nat
  let pols ← listOf (do let id ← nat; let thr ← nat; let keys ← listOf nat; pure (id, thr, keys))
  let seals ← listOf (do let target ← nat; let ctx ← nat; let key ← nat; pure ({ target, ctx, key } : Seal Nat Nat))
  let lines ← listOf line
  let d ← nat
  if !(← get).isEmpty then failure
  let r (c : Nat) : Row := rows.getD c default
  let pol (p : Nat) := pols.find? (·.1 == p)
  let S : Store Nat Nat Nat :=
    { cells := List.range rows.size
      schema := fun c => (r c).schema
      isLocal := fun c => (r c).isLocal
      relies := fun c => (r c).relies
      attests := fun c => (r c).attests
      supersedes := fun c => (r c).supersedes
      retires := fun c => (r c).retires
      invalidates := fun c => (r c).invalidates
      payload := fun c => (r c).payload
      customPol := fun c => (r c).customPol
      verdict := fun c => { attested := (r c).attested, replayed := false, invalid := (r c).invalid,
                            witness := if (r c).witnessEmpty then none else some c, verifier := 0 }
      req := fun c => if (r c).reqEmpty then none else some 0
      seals, scope, pol0
      pols := pols.map (·.1)
      keys := fun p => ((pol p).map (·.2.2)).getD []
      thr := fun p => ((pol p).map (·.2.1)).getD 0 }
  pure (S, lines, d)

def evalLine (s : String) : String :=
  let ts := ((s.replace "\n" " ").splitOn " ").filter (· ≠ "") |>.map String.toNat?
  if ts.any Option.isNone then "E" else
  match (input.run (ts.filterMap id)) with
  | some ((S, lines, d), _) => if accepts S lines d then "ACCEPT" else "REJECT"
  | none => "E"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let l ← stdin.getLine
  if l.isEmpty then return
  stdout.putStrLn (evalLine l)
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
