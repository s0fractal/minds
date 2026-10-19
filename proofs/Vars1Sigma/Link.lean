import EvalMachine
import Vars1.Replay

/-!
# Stage 2 link: the abstract `Machine` instantiated with Book I's `EvalMachine.step`

`sigma-glyph/proofs/EvalMachine.lean` (pinned in `README.md`) mechanizes
`sigma_glyph.step5`, the transition `sigma_resume` runs: `step t remaining store`
returns `.nf`, `.exhausted`, `.unresolved` or `.step t' cost`. It takes the
remaining budget as an argument, while `Vars1.Replay.Machine.step` does not.
The link is the property `sigma_resume.py`'s header states in prose ("which action
it picks does not depend on the remaining budget, only whether it is
affordable"), proved here for the Lean model:

* `step_nf_any` — a normal form is a normal form at every budget;
* `step_fire_any` — a fired action fires, unchanged, at every budget that covers
  its cost;
* `step_cost_le_size` — an action from `t` costs at most `size t + 2`.

So `bookStep (st, t) := step t (size t + 2) st` is the budget-free transition, and
`run_eq_adv` shows that `sigma_resume._run` (without host fences), written over
`EvalMachine.step` exactly as Python writes it, equals `Replay.adv bookMachine`.
`book_verify_sound` is replay soundness for the real Book I transition.

A state is `(store, term)`: the store is the `Environment` that
`ComputationRoot` fixes (an SGS1 state names its `computation_id`).
-/

namespace Vars1.Sigma

open EvalMachine
open Vars1.Replay

deriving instance DecidableEq for Term

theorem step_nf_any (t : Term) (r : Nat) (st : Store) (h : step t r st = .nf) (R : Nat) :
    step t R st = .nf := by
  fun_induction step t r st <;> grind [step]

theorem step_fire_any (t : Term) (r : Nat) (st : Store) (t' : Term) (c : Nat)
    (h : step t r st = .step t' c) (R : Nat) (hR : c ≤ R) : step t R st = .step t' c := by
  fun_induction step t r st generalizing t' c <;> grind [step, step_nf_any, size_pos]

theorem force_size (h : MachineBytes.Bytes) (st : Store) (v : Term) (hv : force h st = some v) :
    size v ≤ 3 := by
  unfold force at hv
  split at hv
  · cases hv; simp [size]
  split at hv
  · cases hv; simp [size]
  split at hv
  · cases hv; simp [size]
  split at hv
  · cases hv
  split at hv
  · cases hv; simp [size]
  · rename_i n _; cases hv; cases n <;> simp [ofNode, size]

theorem step_cost_le_size (t : Term) (r : Nat) (st : Store) (t' : Term) (c : Nat)
    (h : step t r st = .step t' c) : c ≤ size t + 2 := by
  fun_induction step t r st generalizing t' c <;> grind [size, force_size]

/-- The budget-free Book I transition on `(store, term)`. An unaffordable answer
cannot occur at budget `size t + 2` (it would need a cost above the bound); it is
mapped to `blocked`, never to `nf`, so `isNF` is never granted by it. -/
def bookStep (s : Store × Term) : Act (Store × Term) :=
  match step s.2 (size s.2 + 2) s.1 with
  | .nf => .nf
  | .unresolved => .blocked
  | .exhausted => .blocked
  | .step t' c => .fire (s.1, t') c

theorem bookStep_cost_pos (s s' : Store × Term) (c : Nat) (h : bookStep s = .fire s' c) :
    0 < c := by
  unfold bookStep at h
  cases hs : step s.2 (size s.2 + 2) s.1 with
  | step t' c' =>
    rw [hs] at h
    have := step_cost_pos _ _ _ _ _ hs
    cases h; omega
  | nf => rw [hs] at h; cases h
  | unresolved => rw [hs] at h; cases h
  | exhausted => rw [hs] at h; cases h

/-- Book I as a `Replay.Machine`. -/
def bookMachine : Machine where
  S := Store × Term
  step := bookStep
  cost_pos := bookStep_cost_pos

instance : DecidableEq bookMachine.S := inferInstanceAs (DecidableEq (Store × Term))

/-- `sigma_resume._run` over `EvalMachine.step`, without host fences (resource
checks, recursion depth, `max_actions`): ask `step` with what is left of the
budget; stop on anything but a fired action. -/
def run (st : Store) : Nat → Term → Nat → Nat → Term × Nat
  | 0, t, _, sp => (t, sp)
  | f + 1, t, av, sp =>
      match step t (av - sp) st with
      | .step t' c => run st f t' av (sp + c)
      | _ => (t, sp)

/-- **The Python-shaped run is the abstract `adv`.** With fuel above the budget
(each action costs ≥ 1), `_run` from `spent = sp` with `b` available returns the
state and spending of `adv bookMachine`. -/
theorem run_eq_adv (st : Store) :
    ∀ (b f : Nat) (t : Term) (sp : Nat), b < f →
      run st f t (sp + b) sp =
        ((adv bookMachine (st, t) b).1.2, sp + (adv bookMachine (st, t) b).2) := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro f t sp hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [adv_eq]
    simp only [run, Nat.add_sub_cancel_left]
    -- nothing fires at budget `b` unless the budget-free step fires the same action
    have lift : ∀ t'' c'', step t b st = .step t'' c'' →
        step t (size t + 2) st = .step t'' c'' ∧ c'' ≤ b := fun t'' c'' hb =>
      ⟨step_fire_any _ _ _ _ _ hb _ (step_cost_le_size _ _ _ _ _ hb), step_cost_le _ _ _ _ _ hb⟩
    cases hR : step t (size t + 2) st with
    | nf =>
      simp [bookMachine, bookStep, hR, step_nf_any _ _ _ hR b]
    | unresolved =>
      cases hb : step t b st with
      | step t'' c'' => have := (lift _ _ hb).1; rw [hR] at this; cases this
      | _ => simp [bookMachine, bookStep, hR]
    | exhausted =>
      cases hb : step t b st with
      | step t'' c'' => have := (lift _ _ hb).1; rw [hR] at this; cases this
      | _ => simp [bookMachine, bookStep, hR]
    | step t' c =>
      have hc := step_cost_pos _ _ _ _ _ hR
      simp only [bookMachine, bookStep, hR]
      by_cases hcb : c ≤ b
      · rw [step_fire_any _ _ _ _ _ hR b hcb]
        simp only [hcb, if_true]
        have e : sp + b = (sp + c) + (b - c) := by omega
        rw [e, ih (b - c) (by omega) f t' (sp + c) (by omega)]
        simp only [bookMachine, Prod.mk.injEq, true_and]; omega
      · simp only [hcb, if_false]
        cases hb : step t b st with
        | step t'' c'' =>
          obtain ⟨h2, h3⟩ := lift _ _ hb
          rw [hR] at h2; cases h2; omega
        | _ => simp

/-- `isNF` of the budget-free step is the Python probe's `NORMAL_FORM` with zero
actions, at whatever credit the probe is given. -/
theorem bookStep_isNF_iff (st : Store) (t : Term) (r : Nat) :
    (bookStep (st, t)).isNF = true ↔ step t r st = .nf := by
  unfold bookStep
  constructor
  · intro h
    split at h <;> simp_all [Act.isNF]
    rename_i hnf; exact step_nf_any _ _ _ hnf r
  · intro h
    rw [step_nf_any _ _ _ h]; rfl

/-- `adv` never changes the environment. -/
theorem adv_store (s : bookMachine.S) (b : Nat) : (adv bookMachine s b).1.1 = s.1 := by
  induction b using Nat.strongRecOn generalizing s with
  | _ b ih =>
    rw [adv_eq]
    simp only [bookMachine, bookStep]
    cases hs : step s.2 (size s.2 + 2) s.1 with
    | step t' c =>
      have := step_cost_pos _ _ _ _ _ hs
      simp only
      split
      · exact ih (b - c) (by omega) _
      · rfl
    | _ => simp

variable {C R : Type} [DecidableEq R]

/-- **Replay soundness for Book I.** If the lineage verifier, with any sound host, returns
`REPLAYED` for `c`, then one `_run` of `EvalMachine.step` from `SR.start` of `c`'s
computation, with `spent_total(c)` available, spends exactly `spent_total(c)` and
ends at `c`'s term (in `c`'s environment). -/
theorem book_verify_sound (L : Ckpts C R bookMachine) (maxAtp : Nat)
    (host : bookMachine.S → Nat → Option (bookMachine.S × Nat)) (hs : HostSound host)
    (f : Nat) (c : C) (h : verify L maxAtp host f c = .replayed) :
    run (L.state c).1 (L.spent c + 1) (L.start (L.comp c)).2 (L.spent c) 0 =
      ((L.state c).2, L.spent c) := by
  have hv := verify_sound L maxAtp host hs f c h
  have hst : (L.start (L.comp c)).1 = (L.state c).1 := by
    have := adv_store (L.start (L.comp c)) (L.spent c); rw [hv] at this; exact this.symm
  have := run_eq_adv (L.state c).1 (L.spent c) (L.spent c + 1) (L.start (L.comp c)).2 0
    (by omega)
  rw [Nat.zero_add] at this
  rw [this, ← hst]
  have e : ((L.start (L.comp c)).1, (L.start (L.comp c)).2) = L.start (L.comp c) := rfl
  rw [e, hv]; simp

end Vars1.Sigma
