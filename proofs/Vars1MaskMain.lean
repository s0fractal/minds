import Vars1.Mask

/-! `vars1mask`: the F42 oracle of `Vars1/Mask.lean`, compiled. One line in, one line out:

- `M h…` (descriptor atoms in hex) → the mask in decimal, or `E` when a descriptor is outside the admitted domain;
- `R t p mask f…` (`t` 1 for a verdict or acceptance, `p` 1 when its payload is a cell, `mask` in decimal, one flag
  per slot: 0 empty, 1 a cell, 2 anything else) → the reference positions separated by spaces, or `-` for none.

Anything else is `E`. -/

open Vars1.Mask

def hexNibble (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8 else none

partial def hexBytes (cs : List Char) (acc : Array UInt8) : Option ByteArray :=
  match cs with
  | [] => some ⟨acc⟩
  | a :: b :: rest => do
    let hi ← hexNibble a
    let lo ← hexNibble b
    hexBytes rest (acc.push (hi * 16 + lo))
  | _ => none

def answer (line : String) : String :=
  match (line.splitOn " ").filter (· ≠ "") with
  | "M" :: hs =>
    match hs.mapM (fun h => hexBytes h.toList #[]) with
    | none => "E"
    | some ds => if ds.any (descriptorType? · |>.isNone) then "E" else toString (cellMask ds)
  | "R" :: t :: p :: m :: fs =>
    match t.toNat?, p.toNat?, m.toNat?, fs.mapM String.toNat? with
    | some t, some p, some m, some fs =>
      let slot : Nat → Slot := fun | 0 => .empty | 1 => .cell | _ => .other
      match refs (t == 1) (p == 1) m (fs.map slot) with
      | [] => "-"
      | ps => " ".intercalate (ps.map toString)
    | _, _, _, _ => "E"
  | _ => "E"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (answer ((line.replace "\n" "").replace "\r" ""))
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
