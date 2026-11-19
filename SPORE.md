# Metered Portable Agent Spores (`spore.py` & `proofs/Vars1/Spore.lean`)

First executable and formally proved implementation of [AGENT-SPORE-DIRECTION.md](AGENT-SPORE-DIRECTION.md) (`AS-1`–`AS-8`),
built directly over `minds`'s hash-pinned Book I evaluator (`sigma_resume`) and pure Ed25519 signing.

## What is proved in Lean 4 (`proofs/Vars1/Spore.lean`)

Zero `sorry`, zero `Classical.choice` — every theorem depends only on Lean core (`propext`, `Quot.sound`):

| Theorem | Design Intent | Property |
| --- | --- | --- |
| `tree_conserves_atp` | AS-2 | Across any recursive tree of spawned child spores, `total_spent_atp + total_remaining_atp = initial.atp` |
| `tree_conserves_fetches` | AS-2 | Across any recursive spawn tree, `total_spent_fetches + total_remaining_fetches = initial.fetches` |
| `tree_nodes_bounded` | AS-2 | Total leaf/continuation executions in a spawn tree never exceed `initial.spawns + 1` |
| `spawn_depth_strictly_decreases` | AS-2 | Every valid child spawn strictly decreases recursion depth (`child.depth < parent.depth`) |
| `retell_never_inflates` | AS-5 | Forwarding a result to another agent never raises any partiality dimension (`retell p ≤ p`) |
| `retell_never_verified_here` | AS-5 | Retelling never preserves `verifiedHere` (`(retell p).historyLink ≠ .verifiedHere`) |
| `retell_idempotent` | AS-5 | Retelling across multiple hops is idempotent (`retell (retell p) = retell p`) |
| `meet_le_left`, `meet_le_right` | AS-4 | Composing parent and child partiality via meet never exceeds either operand |
| `revision_trans` | AS-6 | Any counterexample hitting `deps1 ⊆ deps2` forces revision of the dependent result |

## What is implemented and tested (`spore.py`, `test_spore.py`)

- **AS-1 (Unfold on demand):** `SporeExecutor` fetches only atoms reachable from `input_term_hash`, `env_hashes`, and
  `required_deps` via SHA-256-verified `remote_fetch`. Missing unneeded branches never block; missing needed atoms yield
  `NOT_ASSESSED` + `PARTIAL(missing_hashes=[...])`; corrupted bytes fail immediately with `INTEGRITY_FAILED`.
- **AS-2 (Bounded recursion & portable checkpoints):** `Budget(atp, fetches, spawns, depth)` enforces strict budget
  partitioning (`spawn_partition`) and emits signed, content-addressed `SporeCheckpoint`s on `ATP_EXHAUSTED` or
  `MISSING_DEPENDENCY`, resumable by another agent without recomputing prior ATP steps.
- **AS-3 (Separate identities):** `task_id` (independent of local budget), `execution_id`, `checkpoint_id`, and
  `result_id` are distinct canonical SHA-256 digests.
- **AS-4 & AS-5 (6D partiality & no retelling inflation):** `PartialityVector` tracks `(integrity, authenticity,
  slice_completeness, execution, history_link, reliance)` separately; `receive_result` checks signature, `task_id`,
  `subject`, `rules_hash`, `trust_context`, and `trusted_executors`, always applying `retell()`.
- **AS-6 (Counterexample-driven revision):** `revise_on_counterexample` computes the shortest causal path from a
  counterexample hash to `task_id` and emits an immutable `RevisionRecord(REASSESS_REQUIRED | UNAFFECTED)` while
  preserving the prior `SporeResult` as history.
- **AS-8 (Pure metered computation only):** Only `book1/sigma-resume` with declared capabilities (`fetch_by_hash`,
  `spawn_spore`) is admitted; native runtimes or ungranted capabilities are refused before any fetch runs.
- **End-to-end 3-agent experiment (`test_spore.py` `test_11`):** Agent A → Agent B (small ATP budget, fetches needed
  Book I atoms on demand, stops at `ATP_EXHAUSTED` checkpoint) → Agent C (verifies context & signature, resumes from
  B's checkpoint with zero recomputation of B's ATP to `NORMAL_FORM = H_K`, honestly recording `WITNESSED` /
  `CONDITIONAL`) → counterexample hits inner dependency → C emits `RevisionRecord` with exact 5-hop causal path.

## Running

```sh
(cd proofs && lake build Vars1.Spore)
.venv/bin/python -m unittest -v test_spore
.venv/bin/python test_spore.py --mutants     # 12/12 curated mutants killed
```

## Limits (honest residual)

- Transport (`remote_fetch`) is an abstract content-addressed callback here; HTTP/P2P wire framing and discovery are
  outside this module.
- `test_spore.py` is imported into `test_vars1.py` so CI runs all 12 tests automatically; `spore.py` is not yet wired
  into `claims.json` or `refs/vars/heads/minds` admission rules (it sits cleanly beside VARS-1 without altering any
  kernel hash or consensus rule).
