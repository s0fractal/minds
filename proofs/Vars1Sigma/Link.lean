import ResumeLink
import Vars1.Replay
import Vars1.Cycle

/-!
# Stage 2 link: VARS replay soundness for Book I's `EvalMachine.step`

`sigma-glyph/proofs/EvalMachine.lean` mechanizes `sigma_glyph.step5`, the transition `sigma_resume` runs.
sigma-glyph's `ResumeLink.lean` (copied in `SigmaEval/` at tag v1.0.0; written here, moved there on 2026-11-01)
instantiates the abstract machine with it: `bookStep (st, t) := step t (size t + 2) st` is the budget-free transition
(`step_nf_any`, `step_fire_any`, `step_cost_le_size`), `run_eq_adv` shows that `sigma_resume._run` (without host
fences), written over `EvalMachine.step` exactly as Python writes it, equals `adv bookMachine`, and
`book_cycle_no_normal_form` is what an accepted cycle witness means for Book I. (No Book I term with a state cycle is
known, so it says what an accepted witness would mean; the richer profile `ski+Y+M+W` is not mechanized.)

What stays here is the VARS part: `book_verify_sound`, replay soundness of the lineage verifier for the real Book I
transition. A state is `(store, term)`: the store is the `Environment` that `ComputationRoot` fixes (an SGS1 state
names its `computation_id`).
-/

namespace Vars1.Sigma

open EvalMachine
open SigmaResume
open Vars1.Replay

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
