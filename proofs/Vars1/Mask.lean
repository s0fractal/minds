/-! F42 (RULES-V2.md §8): an oracle for v2's typed references that does not call the host's parser
(`vars1.schema_cell_mask`). It is written from the spec's own words, VARS-1-SPEC.md §2 and RULES-V2.md §2: a schema
cell's descriptors are UTF8 atoms `name:type`, and its `cell`-typed fields are the reference slots of its instances;
a verdict or an acceptance also references its payload. The tests compare the host with vectors this oracle
produced (`vectors/f42.json`, regenerated and byte-compared in CI by `tools/f42_vectors.py`).

The domain is what schema admission accepts: every descriptor a strict UTF-8 atom whose text has a non-empty name, a
`:`, and a known type. On any other bytes the oracle answers `none`. -/

namespace Vars1.Mask

/-- The field types of VARS-1-SPEC.md §2. -/
def fieldTypes : List String := ["utf8", "u64", "pol1", "root", "digest", "wasm", "kin1", "cell", "hash"]

/-- The type a field descriptor declares, or `none` outside the admitted domain (no `UTF8` prefix, invalid UTF-8,
an empty name, no `:`, a type §2 does not list). The name is the text before the first `:`, the type all after
it. -/
def descriptorType? (raw : ByteArray) : Option String :=
  if raw.size < 4 || (raw.extract 0 4).toList != [0x55, 0x54, 0x46, 0x38] then none else
  match String.fromUTF8? (raw.extract 4 raw.size) with
  | none => none
  | some text =>
    match text.splitOn ":" with
    | name :: rest@(_ :: _) =>
      let type := String.intercalate ":" rest
      if name.isEmpty || !fieldTypes.contains type then none else some type
    | _ => none

/-- Bit `s` is set iff descriptor `s` declares the type `cell`. -/
def cellMask (descriptors : List ByteArray) : Nat :=
  descriptors.zipIdx.foldl (fun m (d, s) => if descriptorType? d == some "cell" then m ||| (1 <<< s) else m) 0

/-- What a slot holds, as the rules read it: the empty hash, a cell the chain has, or anything else. -/
inductive Slot | empty | cell | other
  deriving DecidableEq

/-- The reference positions of an instance (0 the payload, `1 + s` slot `s`): the payload if the instance is a
verdict or an acceptance and its payload is a cell, and every slot whose bit is set in its schema's mask and that
holds a cell (an empty slot references nothing). -/
def refs (payloadTyped : Bool) (payloadIsCell : Bool) (mask : Nat) (slots : List Slot) : List Nat :=
  (if payloadTyped && payloadIsCell then [0] else []) ++
    (slots.zipIdx.filter (fun (v, s) => (mask >>> s) % 2 == 1 && v == .cell)).map (fun (_, s) => s + 1)

theorem cellMask_nil : cellMask [] = 0 := rfl

end Vars1.Mask
