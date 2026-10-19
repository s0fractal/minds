import Vars1.Fold

/-!
# §4.2 Pass 3: witness sets, `Settled`, `Provisional` (definitions only)

Inputs are the results of Passes 1–2 (`active`, `stale`, `authorized`) and the
endorser sets of §4.1 (`cumulative`, `foreignEnd`, `liveScopes`). Book I replay
(`verify_checkpoint_replay`, `term_hash`, `verify_cycle`) is a parameter
`replayOK c v` (witness `c` replays what contract `v` requires). Stage 2
(`Vars1/Pass3Replay.lean`) defines it from the small-step semantics of
`Vars1/Replay.lean` and proves what a `Settled` contract then guarantees.
-/

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

/-- Verdict-specific fields of a cell, kept abstract. -/
structure VerdictInfo (C : Type) where
  /-- `slots[1]` is `H_ATTESTED`, `H_REPLAYED`, `H_VERDICT_INVALID`. -/
  attested : Bool
  replayed : Bool
  invalid : Bool
  /-- `slots[0]` (the checkpoint/cycle witness), `slots[2]` (`verifier_id`). -/
  witness : Option C
  verifier : Nat

/-- Pass 3 inputs. `req v` is `slots[1] ≠ H_EMPTY` of a contract/decision;
`expectedSchema v` is `slots[0]` of a question. -/
structure Pass3In (C K P : Type) where
  active : C → Prop
  stale : C → Prop
  authorized : C → Prop
  cumulative : C → List K
  foreignEnd : C → C → List K
  liveScopes : C → List C
  verdict : C → VerdictInfo C
  req : C → Option Nat
  expectedSchema : C → Schema
  /-- `replayOK c v`: checkpoint or cycle witness `c` meets `v`'s `required_comp`
  and `expected_outcome` (defined in `Pass3Replay`). -/
  replayOK : C → C → Prop
  scopeTip : C

variable (W : World C K P) (X : Pass3In C K P)

/-- `EvalPol(v)`. -/
def evalPol (v : C) : P :=
  match (W.info v).schema with
  | .contract | .decision | .question => ((W.info v).customPol).getD (W.info X.scopeTip).pol0
  | _ => (W.info X.scopeTip).pol0

/-- `WitnessEndorsers(w)`. -/
def witnessEndorsers (w : C) : List K :=
  if (W.info w).isLocal then X.cumulative w
  else (X.liveScopes w).flatMap (X.foreignEnd w)

/-- Live: `Active ∧ ¬Stale`. -/
def Live (c : C) : Prop := X.active c ∧ ¬ X.stale c

/-- The contradictory-verdict exclusion: a live invalid verdict on `v` by the same verifier,
endorsed by someone in `EvalPol(v)`. -/
def Contradicted (cells : List C) (v w : C) : Prop :=
  ∃ b ∈ cells, Live X b ∧ (W.info b).schema = .verdict ∧ (W.info b).payload = some v ∧
    (X.verdict b).invalid = true ∧ (X.verdict b).verifier = (X.verdict w).verifier ∧
    ∃ k ∈ witnessEndorsers W X b, W.member (evalPol W X v) k = true

/-- Membership in `W_max(v)`. -/
def InWmax (cells : List C) (v w : C) : Prop :=
  w ∈ cells ∧ Live X w ∧ v ∈ (W.info w).attests ∧
  match (W.info v).schema with
  | .contract | .decision =>
      ¬ Contradicted W X cells v w ∧ (W.info w).schema = .verdict ∧
      (W.info w).payload = some v ∧
      (match X.req v with
       | none => (X.verdict w).witness = none ∧ (X.verdict w).attested = true
       | some _ => (X.verdict w).replayed = true ∧
           ∃ c, (X.verdict w).witness = some c ∧ Live X c ∧ X.replayOK c v)
  | .question => (W.info w).schema = X.expectedSchema v
  | _ => False

/-- `Settled(v)` (§4.2 Pass 3). `QuorumMet` is counted over the endorsers of
witnesses that satisfy `InWmax` (passed as `wmax`, a decidable presentation). -/
def Settled (wmax : C → List C) (v : C) : Prop :=
  Live X v ∧
  match (W.info v).schema with
  | .metaSchema | .scope => X.authorized v
  | .contract | .decision | .question =>
      W.quorum ((wmax v).flatMap (witnessEndorsers W X)) (evalPol W X v) = true
  | _ => True

/-- `Provisional(v)`. -/
def Provisional (wmax : C → List C) (v : C) : Prop :=
  Live X v ∧ ¬ Settled W X wmax v

/-- A `wmax` presentation is faithful when it lists exactly the `W_max` members. -/
def WmaxFaithful (cells : List C) (wmax : C → List C) : Prop :=
  ∀ v w, w ∈ wmax v ↔ InWmax W X cells v w

end Vars1
