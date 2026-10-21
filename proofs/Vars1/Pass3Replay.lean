import Vars1.Pass3
import Vars1.Replay
import Vars1.Cycle

/-!
# Stage 2 in Pass 3: a `Settled` contract carries a full replay

`replayWitness` is the §4.2 Pass 3 witness condition for `required_comp ≠ H_EMPTY`,
defined from the lineage verifier of `Vars1/Replay.lean`:

* a `schema.checkpoint` `c` with `c.slots[0] = H_req`, `c.slots[4] = H_NORMAL_FORM`,
  `verify_checkpoint_replay(c) = REPLAYED` over its whole lineage, and
  `term_hash(decode_state(c.H_payload).term) = H_exp`; or
* a `schema.cycle_witness` `c` with `c.slots[0] = H_req`, `H_exp = H_CYCLE_PROVEN`,
  and `verify_cycle` returning `CYCLE_PROVEN`, defined as `checkCycle` of `Vars1/Cycle.lean` on the witness's
  entry state (`id(entry state)`, a function of the cell under SHA-256 injectivity), `entry_spent`,
  `cycle_actions` and `cycle_cost`.

`settled_full_replay` (replay soundness lifted to Pass 3): if `v` is a `Settled` contract or
decision with `required_comp = r`, some live witness either is a checkpoint reached
by **one** advance from `SR.start r` by its `spent_total`, sitting at a normal form
whose term hash is `H_exp`, or is a cycle witness of `r` for `H_exp = H_CYCLE_PROVEN` from whose start no budget
reaches a normal form.

`settled_cycle_no_normal_form` (the `H_CYCLE_PROVEN` branch): a `Settled` contract or decision with
`required_comp = r` and `expected_outcome = H_CYCLE_PROVEN` means that from `SR.start r` every number of actions
fires and, at every budget, the run stops only paused: never at a normal form, never at a blocked reference. The one
hypothesis beyond the stage-2 ones is that no term hash equals `H_CYCLE_PROVEN` (SHA-256 domain separation: a term
hash is the id of a Book I node, `H_CYCLE_PROVEN` the id of the atom `UTF8CYCLE_PROVEN`).
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
  /-- a cycle witness's entry state: the state its payload `id(entry state)` names -/
  cycEntry : C → M.S
  /-- `slots[1]` (`entry_spent`), `slots[2]` (`cycle_actions`), `slots[3]` (`cycle_cost`) -/
  cycEntrySpent : C → Nat
  cycActions : C → Nat
  cycCost : C → Nat
  /-- the ceiling `verify_cycle` applies (`sigma_glyph.VERIFIER_LIMITS["max_atp"]`) -/
  cycMaxAtp : Nat

variable (W : World C K P) (X : Pass3In C K P) (Q : ReplayCtx C M)

/-- `verify_cycle_witness_replay(c) == "CYCLE_PROVEN"`: `verify_cycle` from the root of the witness's own
computation (`c.slots[0]`). -/
def cycleOK (c : C) : Prop :=
  checkCycle M Q.cycMaxAtp (Q.ck.start (Q.ck.comp c)) (Q.cycEntry c) (Q.cycEntrySpent c) (Q.cycActions c)
    (Q.cycCost c) = .proven

/-- The Pass 3 witness condition for `required_comp ≠ H_EMPTY`. -/
def replayWitness (c v : C) : Prop :=
  match X.req v with
  | none => False
  | some r =>
      ((W.info c).schema = .checkpoint ∧ Q.ck.comp c = r ∧ Q.ck.claimsNF c = true ∧
        verify Q.ck Q.maxAtp Q.host Q.fuel c = .replayed ∧
        Q.termHash (Q.ck.state c) = Q.expected v) ∨
      ((W.info c).schema = .cycleWitness ∧ Q.ck.comp c = r ∧ Q.expected v = Q.cycleProven ∧ cycleOK Q c)

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
       (Q.ck.comp c = r ∧ Q.expected v = Q.cycleProven ∧
        ∀ b, (M.step (adv M (Q.ck.start r) b).1).isFire = true)) := by
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
  rcases hok with ⟨-, hcomp, hnf, hver, hterm⟩ | ⟨-, hcomp, hexp, hcyc⟩
  · left
    refine ⟨hcomp, ?_, ?_, hterm⟩
    · have := verify_sound Q.ck Q.maxAtp Q.host hs Q.fuel c hver
      rwa [hcomp] at this
    · have h1 := verify_replayOne Q.ck Q.maxAtp Q.host Q.fuel c hver
      exact (replayOne_sound Q.ck Q.maxAtp Q.host hs h1).2.2 hnf
  · unfold cycleOK at hcyc
    rw [hcomp] at hcyc
    exact Or.inr ⟨hcomp, hexp, (cycle_proven_no_normal_form M hcyc).2⟩

/-- **The `H_CYCLE_PROVEN` branch.** A `Settled` contract or decision with `required_comp = r` and
`expected_outcome = H_CYCLE_PROVEN` means that from `SR.start r` every number of actions fires, and at every budget
the run ends paused: no budget gives a normal form or a blocked reference. -/
theorem settled_cycle_no_normal_form (cells : List C) (wmax : C → List C) (v : C) (r : Nat)
    (hf : WmaxFaithful W (withReplay W X Q) cells wmax)
    (hq : QuorumNonempty W)
    (hdis : ∀ s, Q.termHash s ≠ Q.cycleProven)
    (hschema : (W.info v).schema = .contract ∨ (W.info v).schema = .decision)
    (hreq : X.req v = some r)
    (hexp : Q.expected v = Q.cycleProven)
    (hset : Settled W (withReplay W X Q) wmax v) :
    (∀ m, (steps M m (Q.ck.start r)).isSome) ∧
      ∀ b, (M.step (adv M (Q.ck.start r) b).1).isFire = true := by
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
  have key : ∃ c, replayWitness W X Q c v := by
    rcases hschema with h | h <;>
    · rw [h] at hrest
      obtain ⟨-, -, -, hm⟩ := hrest
      rw [hreq'] at hm
      obtain ⟨-, c, -, -, hok⟩ := hm
      exact ⟨c, hok⟩
  obtain ⟨c, hok⟩ := key
  unfold replayWitness at hok
  rw [hreq] at hok
  rcases hok with ⟨-, -, -, -, hterm⟩ | ⟨-, hcomp, -, hcyc⟩
  · exact absurd (hterm.trans hexp) (hdis _)
  · unfold cycleOK at hcyc
    rw [hcomp] at hcyc
    exact cycle_proven_no_normal_form M hcyc

/-- At Pass 3: a checkpoint with a `NOT_ASSESSED` ancestor is never a
`REPLAYED` witness of the checkpoint branch. -/
theorem not_assessed_ancestor_no_witness {c q v : C} (hl : Lin Q.ck q c)
    (hq : replayOne Q.ck Q.maxAtp Q.host q = .notAssessed ∨
      verify Q.ck Q.maxAtp Q.host Q.fuel q = .notAssessed)
    (hw : replayWitness W X Q c v) :
    ∃ r, X.req v = some r ∧ (W.info c).schema = .cycleWitness ∧ Q.expected v = Q.cycleProven ∧
      cycleOK Q c := by
  unfold replayWitness at hw
  split at hw
  · exact hw.elim
  · rename_i r hr
    rcases hw with ⟨-, -, -, hver, -⟩ | ⟨h1, -, h2, h3⟩
    · exact absurd hver (not_assessed_ancestor_blocks Q.ck Q.maxAtp Q.host (g := Q.fuel) hl hq)
    · exact ⟨r, hr, h1, h2, h3⟩

end Vars1
