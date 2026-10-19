import Vars1.Exec

/-! `vars1exec`: one line of facts in, one line of status bytes out (see `Vars1.Exec`).

Line: `N`, then per cell `isLocal isAcc isVerdict verdictInvalid origin authorized payload+1`,
`relies`, `refs` (count, items), and `sup`, `ret`, `inv` (count, `dst auth` pairs). -/

open Vars1.Exec

partial def parseCells (ts : List Nat) (k : Nat) (acc : Array CellF) : Option (Array CellF) := do
  if k = 0 then return acc
  let b (x : Nat) : Bool := x != 0
  match ts with
  | l :: a :: vd :: vi :: o :: au :: p :: rest =>
    let (relies, rest) ← takeList rest
    let (refs, rest) ← takeList rest
    let (sup, rest) ← takeEdges rest
    let (ret, rest) ← takeEdges rest
    let (inv, rest) ← takeEdges rest
    let pay : Option Nat := if p = 0 then none else some (p - 1)
    let c : CellF := ⟨b l, b a, b vd, b vi, o, b au, pay, relies, refs, sup, ret, inv⟩
    parseCells rest (k - 1) (acc.push c)
  | _ => none
where
  takeList : List Nat → Option (List Nat × List Nat)
    | n :: rest => if rest.length < n then none else some (rest.take n, rest.drop n)
    | [] => none
  takeEdges : List Nat → Option (List Edge × List Nat)
    | n :: rest =>
      if rest.length < 2 * n then none
      else
        let xs := rest.take (2 * n)
        let rec pairs : List Nat → List Edge
          | d :: a :: t => { dst := d, auth := a != 0 } :: pairs t
          | _ => []
        some (pairs xs, rest.drop (2 * n))
    | [] => none

def evalLine (line : String) : String :=
  let ts := (line.splitOn " ").filter (· ≠ "") |>.map String.toNat!
  match ts with
  | n :: rest =>
    match parseCells rest n #[] with
    | some cells =>
      let F : Facts := { n, cell := fun w => cells.getD w default }
      " ".intercalate ((statuses F).map toString)
    | none => "E"
  | [] => "E"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (evalLine line.trim)
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
