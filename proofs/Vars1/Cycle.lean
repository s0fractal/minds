import Vars1.Replay
import ResumeCycle

/-!
# What an accepted cycle witness means at the gate (§3 check 4, §4.2 Pass 3 `H_CYCLE_PROVEN`)

A `schema.cycle_witness` cell claims that a computation never reaches a normal form: from the root, an advance by
`entry_spent` reaches an entry state, and from there `cycle_actions` actions costing `cycle_cost` return to the same
state. The gate checks it with `sigma_resume.verify_cycle`. That checker, written over the abstract machine
(`checkCycle`, `runN`, `steps`), and what its `CYCLE_PROVEN` establishes (`checkCycle_sound`, `cycle_fires_forever`,
`cycle_no_stop`, `cycle_proven_no_normal_form`) are sigma-glyph's `ResumeCycle.lean`, copied in `SigmaEval/` at tag
v1.0.0: they were written here and moved there on 2026-11-01. What stays here is the gate's part:

* `gateCycle` — the gate's verdict: `checkCycle`, but a well-shaped witness whose entry is above the host ceiling is
  `NOT_ASSESSED`, not refused (§5: a transition beyond the ceiling is admitted on structure alone).

Theorems:
* `gateCycle_proven_iff` — the gate proves exactly what `checkCycle` proves.
* `replayed_nf_excludes_cycle` — no computation has both a `REPLAYED` checkpoint claiming `H_NORMAL_FORM` and a
  proven cycle witness.
-/

set_option linter.unusedSectionVars false

namespace Vars1.Replay

open SigmaResume

variable (M : Machine) [DecidableEq M.S]

/-- The gate's verdict on a cycle witness (§3 check 4, vars1.py `gate_cycle_witness`): `checkCycle`, except that a
well-shaped witness whose entry costs more than the host ceiling is `NOT_ASSESSED` rather than refused, as any
transition beyond the ceiling is (§5): replaying its prefix is beyond this host, not shown wrong. -/
def gateCycle (maxAtp : Nat) (start entry : M.S) (entrySpent n cost : Nat) : CycleStatus :=
  if n ≠ 0 ∧ n ≤ cost ∧ maxAtp < entrySpent then .notAssessed
  else checkCycle M maxAtp start entry entrySpent n cost

/-- The gate proves exactly what `verify_cycle` proves: the entry ceiling only turns refusals into `NOT_ASSESSED`. -/
theorem gateCycle_proven_iff {maxAtp : Nat} {start entry : M.S} {entrySpent n cost : Nat} :
    gateCycle M maxAtp start entry entrySpent n cost = .proven ↔ checkCycle M maxAtp start entry entrySpent n cost = .proven := by
  unfold gateCycle
  by_cases h : n ≠ 0 ∧ n ≤ cost ∧ maxAtp < entrySpent
  · rw [if_pos h]
    constructor
    · intro h'; cases h'
    · intro hc
      have hz : ¬ (n = 0 ∨ cost = 0) := by omega
      have hl : ¬ cost < n := by omega
      unfold checkCycle at hc
      rw [if_neg hz, if_neg hl] at hc
      by_cases hca : maxAtp < cost
      · rw [if_pos hca] at hc; cases hc
      · rw [if_neg hca, if_pos h.2.2] at hc; cases hc
  · rw [if_neg h]

variable {C R : Type} [DecidableEq R] {M}

/-- **A normal form and a cycle exclude each other.** No computation has both a `REPLAYED` checkpoint claiming
`H_NORMAL_FORM` and a cycle witness `verify_cycle` accepts. -/
theorem replayed_nf_excludes_cycle (L : Ckpts C R M) (maxAtp : Nat) (host : M.S → Nat → Option (M.S × Nat))
    (hs : HostSound host) {f : Nat} {c : C} (hv : verify L maxAtp host f c = .replayed) (hnf : L.claimsNF c = true)
    {maxAtp' : Nat} {entry : M.S} {entrySpent n cost : Nat} :
    checkCycle M maxAtp' (L.start (L.comp c)) entry entrySpent n cost ≠ .proven := by
  intro hcyc
  have hadv := verify_sound L maxAtp host hs f c hv
  have hstop := (replayOne_sound L maxAtp host hs (verify_replayOne L maxAtp host f c hv)).2.2 hnf
  have hfire := (cycle_proven_no_normal_form M hcyc).2 (L.spent c)
  rw [hadv] at hfire
  rw [isFire_not_isNF hfire] at hstop
  cases hstop

end Vars1.Replay
