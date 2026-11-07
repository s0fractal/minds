import Vars1.WitnessComplete

/-! `vars1witness`: one line in (a store and a derivation, as `experiments/witness/check.py --lean` writes them),
`ACCEPT` or `REJECT` out (`Vars1.Witness.accepts`), `E` for a line it cannot read. With `--prove` the line's
derivation is not read: the checker runs on the one `Vars1.Witness.prove` builds from the store alone, to a depth one
more than the store's cells, which bounds both ranks it recurses over (`check.py --lean --prove` writes such a line,
with every seal on the decision's verdicts).

Every number is a natural. Cells are `0 … N-1`; an id the store does not hold gets a number `≥ N`. A list is its
length, then its items.

* `N`, then per cell: `schema` (0 scope, 1 acceptance, 2 contract, 3 decision, 4 question, 5 verdict, 6 metaSchema,
  7 checkpoint, 8 cycleWitness, 9 computation, 10 axiom, 11 other), `isLocal`, `payload+1`, `customPol+1`,
  `ownerPol`, `attested`, `invalid`, `witnessEmpty`, `reqEmpty`, `verifier` (a number naming a verdict's verifier
  id, the same for the same id), then the lists `relies`, `attests`, `supersedes`, `retires`, `invalidates`;
* `scope`, `pol0`; the scopes that governed (a list of `scope pol0`); the policies (a list of `id thr keys`); the
  seals (a list of `target ctx key`);
* the lines (a list of `rule concl premises`: rule 0 stand, 1 endorse, 2 settle, 3 latch, 4 unlatch, 5 dead, 6 eff,
  7 unsup, 8 down; a conclusion is `0 c`, `1 w k`, `2 d`, `3 y x kind`, `4 y x kind` (kind 0 supersedes,
  1 retires, 2 invalidates), `5 x`, `6 y`, `7 w` or `8 b`; premises are a list of conclusions);
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
  ownerPol : Bool := false
  attested : Bool := false
  invalid : Bool := false
  witnessEmpty : Bool := true
  reqEmpty : Bool := true
  verifier : Nat := 0
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
  let ownerPol ← flag
  let attested ← flag
  let invalid ← flag
  let witnessEmpty ← flag
  let reqEmpty ← flag
  let verifier ← nat
  let relies ← listOf nat
  let attests ← listOf nat
  let supersedes ← listOf nat
  let retires ← listOf nat
  let invalidates ← listOf nat
  pure { schema, isLocal, payload, customPol, ownerPol, attested, invalid, witnessEmpty, reqEmpty, verifier, relies, attests,
         supersedes, retires, invalidates }

def kind : Parser Kind := do
  match ← nat with
  | 0 => pure .supersedes | 1 => pure .retires | 2 => pure .invalidates
  | _ => failure

def concl : Parser (Concl Nat Nat) := do
  match ← nat with
  | 0 => pure (.stands (← nat))
  | 1 => do let w ← nat; let k ← nat; pure (.endorsed w k)
  | 2 => pure (.settled (← nat))
  | 3 => do let y ← nat; let x ← nat; let k ← kind; pure (.latch y x k)
  | 4 => do let y ← nat; let x ← nat; let k ← kind; pure (.unlatched y x k)
  | 5 => pure (.dead (← nat))
  | 6 => pure (.eff (← nat))
  | 7 => pure (.unsup (← nat))
  | 8 => pure (.down (← nat))
  | _ => failure

def line : Parser (Line Nat Nat) := do
  let rule ← match ← nat with
    | 0 => pure Rule.stand
    | 1 => pure Rule.endorse
    | 2 => pure Rule.settle
    | 3 => pure Rule.latch
    | 4 => pure Rule.unlatch
    | 5 => pure Rule.dead
    | 6 => pure Rule.eff
    | 7 => pure Rule.unsup
    | 8 => pure Rule.down
    | _ => failure
  let c ← concl
  let prem ← listOf concl
  pure { rule, concl := c, prem }

def input : Parser (Store Nat Nat Nat × List (Line Nat Nat) × Nat) := do
  let rows := (← listOf row).toArray
  let scope ← nat
  let pol0 ← nat
  let ctxs ← listOf (do let c ← nat; let p ← nat; pure (c, p))
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
      ownerPol := fun c => (r c).ownerPol
      verdict := fun c => { attested := (r c).attested, replayed := false, invalid := (r c).invalid,
                            witness := if (r c).witnessEmpty then none else some c, verifier := (r c).verifier }
      req := fun c => if (r c).reqEmpty then none else some 0
      seals, scope, pol0, ctxs
      pols := pols.map (·.1)
      keys := fun p => ((pol p).map (·.2.2)).getD []
      thr := fun p => ((pol p).map (·.2.1)).getD 0 }
  pure (S, lines, d)

def evalLine (prove? : Bool) (s : String) : String :=
  let ts := ((s.replace "\n" " ").splitOn " ").filter (· ≠ "") |>.map String.toNat?
  if ts.any Option.isNone then "E" else
  match (input.run (ts.filterMap id)) with
  | some ((S, lines, d), _) =>
    if accepts S (if prove? then prove S (S.cells.length + 1) d else lines) d then "ACCEPT" else "REJECT"
  | none => "E"

partial def loop (prove? : Bool) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let l ← stdin.getLine
  if l.isEmpty then return
  stdout.putStrLn (evalLine prove? l)
  stdout.flush
  loop prove? stdin stdout

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => loop false (← IO.getStdin) (← IO.getStdout); pure 0
  | ["--prove"] => loop true (← IO.getStdin) (← IO.getStdout); pure 0
  | _ => IO.eprintln "usage: vars1witness [--prove] < lines"; pure 2
