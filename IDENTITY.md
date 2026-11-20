# Relational Identity vs. Fork Continuity (`D21` / Thesis 2)

`proofs/Vars1/Identity.lean` and `identity.py` formally resolve the `F2 / D21` conflict between the
authorization lineage criterion (`AuthPath`) and Thesis 2 (*"fork births a new entity"*).

## 1. The Conflict (`F2 / D21`)

Writing lineage identity as $A_0 \sim A_n \iff \forall t: I^*(I_t, I_{t+1}, W_t)$ collides with
Thesis 2 because `fork` copies bytes without changing $I_t$, making the predicate vacuously true
for both branches ($A_0 \sim B_n$).

## 2. The Resolution: Two Warrant Sorts + Unique Continuation + Relational Isolation

We separate two warrant sorts over a causal lineage DAG:
- **`EnabledBy(w)`:** authorizes a transition (`step` or `fork`) to exist under constitutional `inv_ok`.
  Both linear continuations and forks satisfy `AuthPath` and inherit causal provenance (`Ancestor`).
- **`IdentityContinuation(w)`:** authorizes unique single-branch identity continuation (`step` only,
  strictly forbidden on `fork`), constrained by `UniqueContinuation` (at most one outgoing
  continuation per node — forbidding split-brain identity cloning) and `fork_no_continuation`
  (any node born via `fork` has no incoming `IdentityContinuation` edge from any node, ruling out
  multi-hop `step` detours that try to rejoin a fork-born node).
- **Relational Isolation (`ForkIsolatesRelations`):** a forked entity starts with empty external
  relations (`relations = ∅`) and its own `entity_root`; obligations, grants, and trust must be
  re-established explicitly after birth rather than silently cloned.

## 3. Lean 4 Constructive Theorems (`proofs/Vars1/Identity.lean`)

All 15 theorems compile with zero `sorry` and zero `Classical.choice` (10 general theorems with zero axioms; 5 concrete `d21_*` witness theorems depending only on `[propext]`):

| Theorem | Guarantee |
| :--- | :--- |
| `sameEntity_trans` | `SameEntity` is transitive along non-forking continuation paths |
| `sameEntity_implies_authPath` | `AuthPath` is necessary for `SameEntity` |
| `sameEntity_implies_ancestor` | `SameEntity` preserves causal provenance (`Ancestor`) |
| `unique_continuation_no_split_brain` | Under `UniqueContinuation`, two distinct continuations from one parent are impossible |
| `no_incoming_continuation_not_same` | A node born without an incoming continuation is never `SameEntity` as another node |
| `fork_target_not_same_as_any_other`, `fork_not_same_entity` | Under `fork_no_continuation`, any fork-born node `c` is strictly distinct (`¬ SameEntity a c`) from its fork parent and every other node `a ≠ c`, even across multi-hop `step` detours |
| `fork_no_obligation_theft` | Under `ForkIsolatesRelations`, a forked child inherits none of its parent's external relations |
| `d21_step_same_entity`, `d21_fork_authorized_and_ancestor`, `d21_fork_new_entity_and_isolated` | Concrete `Fin 3` witness with identical byte invariants `inv 0 = inv 2 = 42` proving `AuthPath 0 2 ∧ Ancestor 0 2 ∧ ¬ SameEntity 0 2 ∧ ¬ rels 2 1` |
