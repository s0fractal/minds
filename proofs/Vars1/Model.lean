/-!
# VARS-1 abstract model (§1.2, §1.3)

No bytes, no git, no crypto. A cell identifier `C` stands for `SHA-256(cell bytes)`;
the content of a cell is a function of its identifier (`CellInfo` below), which is
sound only under SHA-256 injectivity on admitted bytes (see `Vars1/Axioms.lean`).

Keys `K` are Ed25519 public keys, policies `P` are `POL1` atoms. A policy is
abstract: we only use `member` (is a key in the roster) and `quorum` (does a
set of endorsers meet the threshold).
-/

namespace Vars1

/-- The schema families that §4.1/§4.2 distinguish. Everything else is `other`. -/
inductive Schema where
  | scope | acceptance | contract | decision | question | verdict
  | metaSchema | checkpoint | cycleWitness | computation | axiom | other
  deriving DecidableEq, Repr

/-- The three eviction edge kinds that §4.1 step 3 latches. -/
inductive Kind where
  | supersedes | retires | invalidates
  deriving DecidableEq, Repr

/-- The part of a cell that §4 reads. `isLocal` is `origin(c) = scope`
(intrinsic standard schemas count as local). `ownerPol` is `slots[0] = H_OWNER`
for contract/decision cells (`false` = `H_PROVISIONAL`). `customPol` is
`slots[3]` (contract/decision) or `slots[1]` (question) when not `H_EMPTY`.
For a scope cell, `pol0`/`pol1` are `slots[0]`/`slots[1]`.
`payload` is `H_payload` when it names a cell; `refs` are every cell the cell
references: the five morphism fields and the payload and slots the rules read as
references — every one equal to a cell id under v1, the typed ones under v2
(`Vars1/Refs.lean`, RULES-V2.md). Nothing below depends on which reading made the list. -/
structure CellInfo (C P : Type) where
  schema : Schema
  isLocal : Bool
  origin : Nat
  slotName : Nat
  relies : List C
  attests : List C
  supersedes : List C
  retires : List C
  invalidates : List C
  refs : List C
  payload : Option C
  ownerPol : Bool
  customPol : Option P
  verdictInvalid : Bool
  pol0 : P
  pol1 : P

/-- The edge list of a given kind. -/
def CellInfo.edges {C P} (c : CellInfo C P) : Kind → List C
  | .supersedes => c.supersedes
  | .retires => c.retires
  | .invalidates => c.invalidates

/-- A detached seal (§1.3) after signature verification: `(H_target, H_scope_ctx, actor_pubkey)`. -/
structure Seal (C K : Type) where
  target : C
  ctx : C
  key : K

/-- One admitted commit `T_i`: the cells it introduces, the valid seals present
in its tree, and the new local scope cell it introduces (if any). -/
structure Commit (C K : Type) where
  newCells : List C
  seals : List (Seal C K)
  newScope : Option C

/-- The parameters of a VARS-1 world: cell contents and the abstract policy
operations. `quorum E p` is `QuorumMet(E, p)`. -/
structure World (C K P : Type) where
  info : C → CellInfo C P
  member : P → K → Bool
  quorum : List K → P → Bool

end Vars1
