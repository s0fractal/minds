import Vars1.Pass3
import Vars1.Replay

/-!
# Stage 2 in Pass 3: a `Settled` contract carries a full replay

`replayWitness` is the §4.2 Pass 3 witness condition for `required_comp ≠ H_EMPTY`,
defined from the lineage verifier of `Vars1/Replay.lean`:

* a `schema.checkpoint` `c` with `c.slots[0] = H_req`, `c.slots[4] = H_NORMAL_FORM`,
  `verify_checkpoint_replay(c) = REPLAYED` over its whole lineage, and
  `term_hash(decode_state(c.H_payload).term) = H_exp`; or
* a `schema.cycle_witness` `c` with `c.slots[0] = H_req`, `H_exp = H_CYCLE_PROVEN`,
  and `verify_cycle` (left abstract: `cycleOK`).

`settled_full_replay` (replay soundness lifted to Pass 3): if `v` is a `Settled` contract or
decision with `required_comp = r`, some live witness either is a checkpoint reached
by **one** advance from `SR.start r` by its `spent_total`, sitting at a normal form
whose term hash is `H_exp`, or is a cycle witness for `H_exp = H_CYCLE_PROVEN`.
-/

set_option linter.unusedSectionVars false

namespace Vars1

open Replay

variable {C K P : Type} [DecidableEq C] [DecidableEq K] {M : Machine} [DecidableEq M.S]

/-- The replay-side parameters of Pass 3. -/
structure ReplayCtx (C : Type) (M : Machine) where
  ck : Ckpts C Nat M
  maxAtp : Nat
  host : M.S → Nat → Option (M.S × Nat)
  /-- lineage walk bound (`vars1.py` walks to the root and raises on a cycle) -/
  fuel : Nat
  /-- `term_hash(decode_state(·).term)` -/
  termHash : M.S → Nat
  /-- `v.slots[2]` (`H_exp`) -/
  expected : C → Nat
  cycleProven : Nat
  /-- `sigma_resume.verify_cycle(...) == "CYCLE_PROVEN"` (not modelled) -/
  cycleOK : C → Prop

variable (W : World C K P) (X : Pass3In C K P) (Q : ReplayCtx C M)

/-- The Pass 3 witness condition for `required_comp ≠ H_EMPTY`. -/
def replayWitness (c v : C) : Prop :=
  match X.req v with
  | none => False
  | some r =>
      ((W.info c).schema = .checkpoint ∧ Q.ck.comp c = r ∧ Q.ck.claimsNF c = true ∧
        verify Q.ck Q.maxAtp Q.host Q.fuel c = .replayed ∧
        Q.termHash (Q.ck.state c) = Q.expected v) ∨
      ((W.info c).schema = .cycleWitness ∧ Q.expected v = Q.cycleProven ∧ Q.cycleOK c)

/-- Pass 3 with the replay oracle. -/
def withReplay : Pass3In C K P := { X with replayOK := replayWitness W X Q }

/-- `QuorumMet(∅, p)` is false for every policy: `POL1` thresholds are `≥ 1`
(§3.2 typed slots). -/
def QuorumNonempty : Prop := ∀ p, W.quorum [] p = false

/-- **A `Settled` contract with `required_comp` carries a full replay.** -/
theorem settled_full_replay (cells : List C) (wmax : C → List C) (v : C) (r : Nat)
    (hf : WmaxFaithful W (withReplay W X Q) cells wmax)
    (hq : QuorumNonempty W)
    (hs : HostSound Q.host)
    (hschema : (W.info v).schema = .contract ∨ (W.info v).schema = .decision)
    (hreq : X.req v = some r)
    (hset : Settled W (withReplay W X Q) wmax v) :
    ∃ c, Live X c ∧
      ((Q.ck.comp c = r ∧
        adv M (Q.ck.start r) (Q.ck.spent c) = (Q.ck.state c, Q.ck.spent c) ∧
        (M.step (Q.ck.state c)).isNF = true ∧
        Q.termHash (Q.ck.state c) = Q.expected v) ∨
       (Q.expected v = Q.cycleProven ∧ Q.cycleOK c)) := by
  obtain ⟨-, hquo⟩ := hset
  have hwit : ∃ w, w ∈ wmax v := by
    cases hw : wmax v with
    | nil =>
      exfalso
      rcases hschema with h | h <;> simp [h, hw, hq _] at hquo
    | cons w _ => exact ⟨w, by simp⟩
  obtain ⟨w, hw⟩ := hwit
  obtain ⟨-, -, -, hrest⟩ := (hf v w).1 hw
  have hreq' : (withReplay W X Q).req v = some r := hreq
  have key : ∃ c, Live X c ∧ replayWitness W X Q c v := by
    rcases hschema with h | h <;>
    · rw [h] at hrest
      obtain ⟨-, -, -, hm⟩ := hrest
      rw [hreq'] at hm
      obtain ⟨-, c, -, hl, hok⟩ := hm
      exact ⟨c, hl, hok⟩
  obtain ⟨c, hl, hok⟩ := key
  refine ⟨c, hl, ?_⟩
  unfold replayWitness at hok
  rw [hreq] at hok
  rcases hok with ⟨-, hcomp, hnf, hver, hterm⟩ | ⟨-, hexp, hcyc⟩
  · left
    refine ⟨hcomp, ?_, ?_, hterm⟩
    · have := verify_sound Q.ck Q.maxAtp Q.host hs Q.fuel c hver
      rwa [hcomp] at this
    · have h1 := verify_replayOne Q.ck Q.maxAtp Q.host Q.fuel c hver
      exact (replayOne_sound Q.ck Q.maxAtp Q.host hs h1).2.2 hnf
  · exact Or.inr ⟨hexp, hcyc⟩

/-- At Pass 3: a checkpoint with a `NOT_ASSESSED` ancestor is never a
`REPLAYED` witness of the checkpoint branch. -/
theorem not_assessed_ancestor_no_witness {c q v : C} (hl : Lin Q.ck q c)
    (hq : replayOne Q.ck Q.maxAtp Q.host q = .notAssessed ∨
      verify Q.ck Q.maxAtp Q.host Q.fuel q = .notAssessed)
    (hw : replayWitness W X Q c v) :
    (W.info c).schema = .cycleWitness ∧ Q.expected v = Q.cycleProven ∧ Q.cycleOK c := by
  unfold replayWitness at hw
  split at hw
  · exact hw.elim
  · rcases hw with ⟨-, -, -, hver, -⟩ | h
    · exact absurd hver (not_assessed_ancestor_blocks Q.ck Q.maxAtp Q.host (g := Q.fuel) hl hq)
    · exact h

end Vars1
