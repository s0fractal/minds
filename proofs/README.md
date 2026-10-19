# VARS-1 proofs

Lean 4 (`v4.31.0`, core only, no Mathlib). Models the fold (§4.1) and the lens (§4.2) of
`VARS-1-SPEC.md` abstractly — no bytes, git or crypto — and proves their invariants.

```
lake build              # library Vars1
lake build Vars1Sigma   # link to sigma-glyph's Book I evaluator (../../sigma-glyph/proofs)
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
| `Pass2.lean`, `Lfp.lean` | `Φ_mono`, `stale_fixed`, `stale_least` | the Pass 2 operator is monotone; `Stale` is its least fixed point |
| | `sweep_reaches_stale` | the spec's round (live acceptance first, then an in-place sweep) reaches `Stale` within `|cells|+1` rounds, in any cell order |
| `Replay.lean` | `adv_seg` | segmentation invariance of budgeted advance |
| | `verify_sound` | `REPLAYED` for `c` ⟹ one advance from `ComputationRoot` by `spent_total(c)` reaches exactly `c`'s state |
| | `not_assessed_ancestor_blocks` | a `NOT_ASSESSED` ancestor prevents `REPLAYED` at any fuel |
| `ReplayAttack.lean` | `pre_lineage_unsound` | a verifier that trusts an unverified parent is unsound (explicit counterexample) |
| `Pass3Replay.lean` | `settled_full_replay` | a Settled contract with `required_comp` has a full replay from root to a normal form with the expected term hash |
| `Vars1Sigma/Link.lean` | `run_eq_adv`, `book_verify_sound` | the abstract machine instantiated with `EvalMachine.step`; replay soundness for Book I |

## Hypotheses (explicit, not axioms)

- SHA-256 is injective on admitted bytes, so a cell is a function of its id.
- A valid seal was signed by its key holder over `(target, ctx)`.
- §1.2 Rule 6 holds at every admitted commit (the gate enforces it).
- `HostSound`: host resource fences only stop a replay; they never alter a reported result.
- `QuorumMet(∅, p)` is false (`POL1` threshold ≥ 1).
- `verify_cycle` is an oracle.

## Not linked

- `EvalMachine.step` to the Python `step5` (only the differential bridge in sigma-glyph).
- `sigma_resume._run` to `run`: the loop is transcribed by hand.
- SGS1 bytes to `(Store, Term)`; `term_hash`; `ComputationRoot` to the start state.
- The rich runtime profile (`ski+Y+M+W`); `verify_cycle`.
- Uniqueness among scope cells (one Active local scope) is checked by property I7, not proved.
- `vars1.py` and `kernel/lens.wasm` are not refined against this model; they are tested against each other.

## Mutants

Each of these breaks the build: dropping the authorized-supersedes clause of `Active`;
non-transitive `Superseded`; dropping `¬Superseded` from `Active`; live acceptance from Stale
acceptances; recomputing live acceptance mid-round; unlatching edges; re-fixing InitialEndorsers;
pooling seals across scopes; a verifier that ignores the parent's status (also refuted by
`pre_lineage_unsound`); dropping the `spent_total`, state or normal-form checks; counting a host
local outcome as `REPLAYED`; replaying from the start regardless of the parent.
