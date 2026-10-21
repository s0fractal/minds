# VARS-1 proofs

Lean 4 (`v4.31.0`, core only, no Mathlib). Models the fold (§4.1) and the lens (§4.2) of
`VARS-1-SPEC.md` abstractly — no bytes, git or crypto — and proves their invariants.

```
lake build              # library Vars1
lake build vars1exec    # the executable lens, compiled (used by test_vars1_props.py, invariant I9)
lake build vars1fold    # the model's own fold, compiled (invariant I10)
lake build vars1cycle   # the model's cycle checker, compiled (invariant I12)
lake build Vars1Sigma   # link to sigma-glyph's Book I evaluator (three files copied in SigmaEval/)
```

Zero `sorry`, no `axiom` declarations. `#print axioms` shows only `propext`, `Quot.sound`
and, for some theorems, `Classical.choice`.

## Theorems

| File | Theorem | Statement |
|---|---|---|
| `Fold.lean` | `stateAt_mono` | latches only grow along the chain; InitialEndorsers never change after birth |
| | `stateAt_append` | the state at the start of `T_i` does not depend on later commits |
| | `step_epoch_binding` | a commit's latches depend only on seals under its own scope `S_i` |
| | `endorser_signed` | under unforgeability, every counted endorser signed `(id(u), id(S_i))` |
| `Pass1.lean` | `unique_active_binding` | under §1.2 Rule 6, two local non-scope cells with one name are never both Active |
| `Scope.lean` | `governed_superseded`, `unique_active_scope` | under the gate's rotation rule, a scope that no longer governs is superseded by a later scope; an Active local scope is the governing one |
| `Pass2.lean`, `Lfp.lean` | `Φ_mono`, `stale_fixed`, `stale_least` | the Pass 2 operator is monotone; `Stale` is its least fixed point |
| | `sweep_reaches_stale` | the spec's round (live acceptance first, then an in-place sweep) reaches `Stale` within `|cells|+1` rounds, in any cell order |
| `Replay.lean` | `adv_seg` | segmentation invariance of budgeted advance |
| | `verify_sound` | `REPLAYED` for `c` ⟹ one advance from `ComputationRoot` by `spent_total(c)` reaches exactly `c`'s state |
| | `not_assessed_ancestor_blocks` | a `NOT_ASSESSED` ancestor prevents `REPLAYED` at any fuel |
| `ReplayAttack.lean` | `pre_lineage_unsound` | a verifier that trusts an unverified parent is unsound (explicit counterexample) |
| `Cycle.lean` | `checkCycle_sound` | `checkCycle` (`sigma_resume.verify_cycle` over the abstract machine) returns `CYCLE_PROVEN` ⟹ one advance from the start by `entry_spent` reaches exactly the entry, and `n ≥ 1` actions from the entry return to it at `cycle_cost` |
| | `cycle_proven_no_normal_form` | then from the start every number of actions fires, and at every budget the run ends paused: never a normal form, never a blocked reference |
| | `replayed_nf_excludes_cycle` | no computation has both a `REPLAYED` checkpoint claiming `H_NORMAL_FORM` and an accepted cycle witness |
| `Pass3Replay.lean` | `settled_full_replay` | a Settled contract with `required_comp` has a live witness: a full replay from root to a normal form with the expected term hash, or a cycle witness of the same computation for `H_CYCLE_PROVEN` from whose start no budget reaches a normal form |
| | `settled_cycle_no_normal_form` | a Settled contract with `required_comp = r` and `expected_outcome = H_CYCLE_PROVEN`: from `SR.start r` every number of actions fires and no budget gives a normal form or a blocked reference |
| `Vars1Sigma/Link.lean` | `run_eq_adv`, `book_verify_sound` | the abstract machine instantiated with `EvalMachine.step`; replay soundness for Book I |
| | `book_cycle_no_normal_form` | for Book I: an accepted cycle witness means `_run` of `EvalMachine.step` from the start, at any budget, stops at a term that is a normal form at no budget (no Book I term with a state cycle is known) |
| `ExecProof.lean` | `pass1_correct` | the executable Pass 1 (`Exec.lean`) satisfies `IsPass1`, and its `sup`/`act` bits are the model's `Superseded`/`Active`, on the world its facts describe |
| | `stale_correct` | the executable Pass 2 is the model's `Stale = lfp Φ` |

## Executable lens

`Exec.lean` computes lens Passes 1–2 from the facts the rules kernel sees — cell structure from its input,
`Authorized` and edge authorization from its fold's output — and `ExecProof.lean` proves it equal to the model
(hypotheses: every reference names an older cell, which the kernel enforces; no cell is both an acceptance and a
verdict). It is compiled as `vars1exec`, and the property suite checks on every admitted tip that its status bytes
equal `kernel/lens.wasm`'s (I9). So the kernel's Passes 1–2 are compared with proved code, not with another
unproved implementation. Reverting `Superseded`'s transitivity in `Exec.lean` breaks the proof and fails I9.

## Cycle witnesses

`Cycle.lean` defines `checkCycle`, `sigma_resume.verify_cycle` (sigma-glyph 0.8.0) written over the abstract machine
in its order: positive `n ≤ cost`; the period's cost against the host ceiling (`NOT_ASSESSED`); the prefix `advance`
by `entry_spent`, whose own admission ceiling turns `entry_spent > max_atp` into a refusal (`PREFIX_MISMATCH`, not
`NOT_ASSESSED`); the prefix must spend exactly `entry_spent`, stop `PAUSED` and stop at the entry; the period, `_run`
with `max_actions = n` and `cost` available, must do `n` actions, spend `cost` and return to the entry. It is compiled
as `vars1cycle` over finite transition tables, and the property suite checks on generated tables and witnesses, true
ones and their neighbours, that `verify_cycle` with the table substituted for `STEP`, and `vars1.py`'s glue in gate
and Pass 3 modes, give its verdict (I12). So the gate's cycle check is compared with the checker the theorem is
about, not trusted. A mutant of the model that changes a verdict but not soundness (prefix admission read as
`NOT_ASSESSED`; the ceiling checked before `n = 0`) fails I12; one that weakens it breaks the proof.

## Hypotheses (explicit, not axioms)

- SHA-256 is injective on admitted bytes, so a cell is a function of its id.
- A valid seal was signed by its key holder over `(target, ctx)`.
- §1.2 Rule 6 holds at every admitted commit (the gate enforces it).
- Rotations are admitted as §3 check 1 requires (`RotationAdmitted`), every local scope cell present has governed at
  some commit, and scope cells are Effective and Accepted (no edge may invalidate or retire a scope cell).
- `HostSound`: host resource fences only stop a replay; they never alter a reported result.
- `QuorumMet(∅, p)` is false (`POL1` threshold ≥ 1).
- For `settled_cycle_no_normal_form`: no term hash equals `H_CYCLE_PROVEN` (a term hash is the id of a Book I node,
  `H_CYCLE_PROVEN` the id of the atom `UTF8CYCLE_PROVEN`).

## Not linked

- `EvalMachine.step` to the Python `step5` (only the differential bridge in sigma-glyph).
- `sigma_resume._run` to `run`: the loop is transcribed by hand.
- SGS1 bytes to `(Store, Term)`; `term_hash`; `ComputationRoot` to the start state.
- The rich runtime profile (`ski+Y+M+W`) is not mechanized; it is the profile with known state cycles (`M M`,
  `Y I`), so for it `cycle_proven_no_normal_form` holds of any machine but no Lean transition is instantiated.
- `sigma_resume.verify_cycle` to `checkCycle`: tied by differential testing (I12) on finite tables, not by a proof
  about the Python. Its checks on documents (witness shape and integer domain, `computation_id` against the chosen
  root, the root's environment, runtime and cost model) and its host fences (resource checks, recursion depth,
  absent evidence: refusals) are outside the model; they only refuse. The tables do not reach those fences.
- A cycle witness's payload to its entry state: the gate compares `id(state)`, the model compares states (SHA-256
  injectivity).
- `kernel/lens.wasm`'s Passes 1–2 are tied to the proved executable lens by differential testing (I9), not by a
  proof about the Rust or wasm code.
- The kernel's fold is tied to `Fold.lean` by differential testing: `vars1fold` compiles the model's own `run`
  (no transcription) over facts read from the kernel's input, and the property suite checks on every admitted tip
  that its governing scope, Authorized bits and edge authorizations equal the kernel's (I10). Making the model let
  an author invalidate alone is caught by I10.

## Mutants

Each of these breaks the build: dropping the authorized-supersedes clause of `Active`;
non-transitive `Superseded`; dropping `¬Superseded` from `Active`; live acceptance from Stale
acceptances; recomputing live acceptance mid-round; unlatching edges; re-fixing InitialEndorsers;
pooling seals across scopes; a verifier that ignores the parent's status (also refuted by
`pre_lineage_unsound`); dropping the `spent_total`, state or normal-form checks; counting a host
local outcome as `REPLAYED`; replaying from the start regardless of the parent; in `checkCycle`, dropping the
return-to-entry, actions-done, prefix-spent, entry-state or `n = 0` check, or miscounting `runN`'s actions; in Pass 3,
a cycle witness of another computation.
