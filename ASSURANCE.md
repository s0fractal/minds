# What is established about minds, and how

The spec is checked against this, sentence by sentence: `claims.json` quotes every normative block of
VARS-1-SPEC.md with its status and witnesses, and every tested or differential claim names mutants that
`tools/run_mutants.py` must see killed. `python3 tools/check_claims.py` prints the debt: `assumed` claims (nothing
checks them) and `unburned` ones (a witness exists, but no mutant has shown it bites). CI refuses an uncovered
block, a stale quote, a missing witness or a surviving mutant.

Each claim below names its kind of evidence. **Proved** means a machine-checked proof for all inputs, under the
hypotheses listed. **Bounded** means a model checker (Kani/CBMC) explored every input within a stated bound.
**Differential** means two independent implementations agree on generated inputs. **Tested** means example and
mutation tests. **Assumed** means nothing here checks it.

## The rules (fold §4.1, lens Passes 1–2 §4.2)

| Claim | Evidence | Where |
|---|---|---|
| Latches only grow; a commit's latches depend only on seals under its own scope | Proved | `proofs/Vars1/Fold.lean` |
| At most one Active local binding per name; one Active local scope, the governing one | Proved (gate rules as hypotheses) | `Pass1.lean`, `Scope.lean` |
| `Stale` is the least fixed point of a monotone operator, reached within `|cells|+1` rounds | Proved | `Pass2.lean`, `Lfp.lean` |
| An executable Passes 1–2 equals the model | Proved | `Exec.lean`, `ExecProof.lean` |
| `kernel/lens.wasm` Passes 1–2 equal that executable | Differential (I9) | `test_vars1_props.py` |
| `kernel/lens.wasm` fold equals the model's own compiled fold | Differential (I10) | `test_vars1_props.py` |
| On every two-cell log in three families (a genesis scope plus: an axiom relying on it; an acceptance of it; a foreign scope no acceptance admits), with symbolic threshold, origin, birth and one extra seal, the kernel does not panic or overflow, and refuses with a known code or answers with status bits that obey §4.2 (effective = not invalidated; active ⇒ effective, accepted, not retired, not superseded; stale ⇒ active; local ⇒ accepted; flags 0/1; the governing scope is a local scope) | Bounded (Kani 0.68, local: `kernel/assure.sh kani`, 4–7 min and 14–15 GB each; not in CI) | `kernel/src/lib.rs` `proofs` |
| The same for families with supersedes, retires or invalidates edges, an INVALID verdict, a scope rotation, a contract | **Not established**: they need deeper unwinding or more than 16 GB on this machine | — |
| The kernel does not panic, overflow or return an unknown code on arbitrary bytes whose commit count is at most 4096 | Tested (fuzzing: 13.9 M inputs in 10 min, seeded with real inputs; `kernel/assure.sh fuzz`); larger counts are skipped, see the time limit below | `kernel/fuzz` |
| `kernel/lens.wasm` rebuilds from source to `H_LENS_KERNEL` | Tested: on Linux in CI (`.github/workflows/check.yml`); on macOS in every release's checks (`tools/minds_chain.py`), not in CI | |

## Replay (§5)

| Claim | Evidence | Where |
|---|---|---|
| `REPLAYED` means one advance from the root by `spent_total` reaches exactly the checkpoint's state | Proved (abstract machine) | `Replay.lean` |
| Same for Book I's evaluator | Proved | `Vars1Sigma/Link.lean` |
| A Settled contract with `required_comp` has a full replay to the expected normal form | Proved; checked on implementation (I4) | `Pass3Replay.lean`, property suite |
| Python replay (`sigma_resume`) matches the abstract machine | Assumed (transcribed by hand) | — |
| `verify_cycle` is sound | Assumed (an oracle) | — |

## Bytes, signatures, hashes

| Claim | Evidence | Where |
|---|---|---|
| SHA-256 is collision-free on admitted bytes | Assumed (standard) | — |
| Admitted bytes are canonical: one encoding per value, whole objects validated | Tested (gate corpus, each case with its valid neighbour) | `test_vars1.py` 29, 32 |
| A valid seal was made by its key holder | Assumed (Ed25519); 34 RFC/edge vectors | `vectors/verify-sig.json` |
| Book I modules are the revision the spec pins | Checked at import (bytes hashed) | `vars1.py` |

## Clients and governance

| Claim | Evidence | Where |
|---|---|---|
| An offline client's Pass 3 equals the lens's Settled | Differential (I11) | property suite |
| A bundle cannot hide a verdict or seal its projection's tip holds | Tested | `test_vars1.py` 17, 21 |
| `verify-*` accepts only against keys the reader pinned | Tested, with mutants | `test_vars1.py` 39 |
| Every release on `refs/vars/heads/minds` was checked by both members in fresh worktrees | Recorded on the chain; each member's checks are its own claim | `tools/minds_chain.py` |
| Members are independent | **Not established**: two AI agents (Claude; Gemini via antigravity) with keys on one machine and OS account | README |
| A projection is current | **Not established**: acceptance is about its tip | spec §4.4 |

## Known limits of the bounded checks

One mutant has been run so far: making `Active` ignore `accepted` fails `two_cells_foreign_scope` on exactly that
assertion. The other invariants and families are not yet burned by mutants of their own. The first version of these checks had no family that reached an unaccepted cell (a foreign cell is refused
without a self-sealed scope of its origin, which no two-cell log had), so the same mutant passed every family; the
foreign-scope family was added for that reason. An invariant is only as checked as the families that reach it.

**Kernel time is not bounded by input size.** Fuzzing found that every count in the input is checked against the
input's length except the commit count `C`, and the fold visits every commit: an 8 KB input claiming 84 million
commits runs for minutes. The host supplies `C` from its own chain and bundles never run the kernel, so the live
chains are not exposed; as a standalone component the kernel's time is `O(C·(N+S))`. Bounding `C` (or skipping
commits with no births or seals) changes `lens.wasm`, hence `H_LENS_KERNEL`: it waits for the next rules identity.
The fuzzer skips inputs with `C > 4096` so it keeps looking for correctness defects.

Kani runs the kernel on the host, where `usize` is 64 bits; wasm32 has 32. An overflow possible only at 32 bits is
outside these checks (the kernel bounds every count by the input length, which wasm32 already bounds). The bounds
are small; they find shallow defects in every branch they reach, not deep ones beyond the bound.
