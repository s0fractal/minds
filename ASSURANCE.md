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

## Changing the rules (§4.3) and the v2 rules (RULES-V2.md)

| Claim | Evidence | Where |
|---|---|---|
| A rotation to other rules is admitted only with exactly one rules-change decision, sealed by the governing admission quorum, whose three computations the gate replays: (a) the new rules give every status and the governing scope the old rules give over the chain so far; (b) on a counterexample chain the gate admits, the new rules give the named status bit the value named right and the old rules do not; (c) no Authorized cell or authorized edge of the old rules is lost, on either log; the counterexample is named by its canonical commit id, so a moved or deleted ref, a hex-named one included, does not change what was admitted | Tested, with mutants for every check (`m-rc-*`) | `test_vars1.py` 47–51, 59 |
| The gate, the chain reader and the release checks take commits only by canonical id in the repository's object format | Tested, with mutants | `test_vars1.py` 60, 61 |
| A rules change is admitted in one of four classes (AMENDMENTS.md), each with its own decision schema and evidence: a semantic correction as above; a resource hardening (on an input, under a budget of steps, the old rules exhaust it or trap and the new refuse with a resource code they declare); a validation tightening (the old give an output, the new refuse with a non-resource code); an implementation-equivalent change; the last three reproduce the chain so far byte for byte | Tested, with mutants for every check (`m-amend-*`) | `test_vars1.py` 62, 64–66 |
| Refusal, budget exhaustion, a fault and an output are distinct results; a budget counts steps (function and loop-body entries) of a module rewritten by `meter.py`, the same on every engine | Tested: metering changes no result on real v1, v1b and v2 inputs; exhaustion and fault are told apart by a flag the rewrite sets | `test_vars1.py` 62 |
| (d) A rules change keeps every earlier one: each earlier counterexample gets the result its change established (a correction's bit by cell id; a hardening's or tightening's refusal within its budget); so v1b → v1 "as equivalent" is refused, and so is v1b → v2 (v2 cannot read the v1-encoded input) | Tested, with mutants | `test_vars1.py` 67 |
| A rotation from v2 to rules that read references as v1 does is refused | Tested, with a mutant | `test_vars1.py` 68 |
| The v1b rules (`kernel/` with `commit-bound`, `H_LENS_KERNEL_V1B`) refuse an input claiming more commits than it has bytes (E-7) and are otherwise v1; the host's twin refuses the same chains; the default build is still `H_LENS_KERNEL` byte for byte | Tested (the fuzzer's input rebuilt: v1 exhausts 10^7 steps, v1b refuses; a chain of empty commits past the bound); rebuilt in CI and in every release that carries `kernel/lens1b.wasm` | `test_vars1.py` 58, 62, 63 |
| A gate-admitted chain stays within v1b's bound | **False**: the gate admits empty commits; ~3.6 K of them on a bare genesis cross it, and under v1b the crossing commit is refused (a commit adding a cell always fits) | `test_vars1.py` 63 |
| Before a rotation is recorded, every historical tip is replayed under its epoch's rules and the new rules, and every difference (commit, cell, bit, old, new) is listed; a hardening or an equivalent change is recorded only with none | Tested, with mutants (release condition in `tools/minds_chain.py change-rules`, not a gate rule) | `test_vars1.py` 70 |
| The verdict a decision names right is right | **Not established**: the gate checks only that the old rules disagree with it and the new agree; rightness is the claim of the quorum that seals the decision | spec §4.3 |
| The new rules agree with the old on inputs other than the chain so far, or refute them on inputs other than the counterexample | **Not established**: (a)–(c) compare two logs, not all inputs | — |
| A rules change whose point is a controlled refusal (a resource bound, a crash or hang made a refusal, a validation tightened) can be admitted | Tested: the hardening and tightening classes above; the commit-count bound is carried as a hardening | `test_vars1.py` 62–65 |
| A node holding the chain can replay a past rules change | Tested: the gate writes `refs/vars/evidence/<scope>/<decision>` with the rotation; a fresh clone fetching only the scope's ref and `refs/vars/evidence/*` replays it after the author's refs are deleted and gc'd; a hardening's input is an atom of the chain. Without the evidence (ref deleted and gc'd, a shallow fetch, a lost object) the replay reports `EvidenceMissing`, not a refusal. Radicle does not replicate `refs/vars/evidence/*` | `test_vars1.py` 69; `tools/minds_chain.py evidence`, `replay-changes` |
| `H_LENS_KERNEL` identifies everything the gate decides | **Not established, and false**: the host decides canonical bytes, types, replay, rule-6 parsing and rules-change admission; the canonical-id fix of PR #1 changed the gate without changing `H_LENS_KERNEL`. A release names the host by its `main` commit | `tools/minds_chain.py` |
| A rotation from v2 back to v1 is refused, with or without a decision | Differential (kernel E-25 and twin) and tested | `test_vars1.py` 52, 53 |
| `kernel2/lens2.wasm` rebuilds to `H_LENS_KERNEL_V2` | Tested: in CI; in every release's checks when the released commit carries `kernel2/` | `tools/minds_chain.py` `kernel_checks`, `test_vars1.py` 58 |
| v2 reads a v1-born cell as v1 does, a v2-born cell by type, and checks the reference list it is given | Tested (conformance only; the property suite and Kani exercise v1 only, and the prototype's Lean `Refs.lean` is not on main) | `test_vars1.py` 54–57 |
| A custom schema's `cell` mask is parsed correctly from its descriptors | Assumed: host parsing in the trusted base (RULES-V2.md F42) | — |
| The spec's text changes in the same decision | Assumed: nothing checks the text | — |

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

**Kernel time is not bounded by input size (v1).** Fuzzing found that every count in the input is checked against the
input's length except the commit count `C`, and the fold visits every commit: an 8 KB input claiming 84 million
commits runs for minutes. The host supplies `C` from its own chain and bundles never run the kernel, so the live
chains are not exposed; as a standalone component the kernel's time is `O(C·(N+S))`. The v1b rules
(`H_LENS_KERNEL_V1B`) bound `C` by the input's length, so their time is `O(L·(N+S))` for `L` input bytes; they reach a
scope only by a resource hardening (AMENDMENTS.md), and `refs/vars/heads/minds` stays on v1 until its members decide.
The fuzzer builds v1 and skips inputs with `C > 4096` so it keeps looking for correctness defects.

Kani runs the kernel on the host, where `usize` is 64 bits; wasm32 has 32. An overflow possible only at 32 bits is
outside these checks (the kernel bounds every count by the input length, which wasm32 already bounds). The bounds
are small; they find shallow defects in every branch they reach, not deep ones beyond the bound.
