# What is established about minds, and how

This file is rendered from `assurance.json` (`tools/check_claims.py --write-assurance`): edit the data, not the
file; CI refuses a file that is not exactly the rendering.

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
| At most one Active local binding per name; one Active local scope, the governing one | Proved (gate rules as hypotheses) for rules whose rotations take effect at once (v1, v1b); for a rotation that waits under v2 (§4.1 latch 4a), whose scope has not governed yet, tested: the waiting scope is not Active until it governs (test 85) | `Pass1.lean`, `Scope.lean` |
| `Stale` is the least fixed point of a monotone operator, reached within `\|cells\|+1` rounds | Proved | `Pass2.lean`, `Lfp.lean` |
| An executable Passes 1–2 equals the model | Proved | `Exec.lean`, `ExecProof.lean` |
| `kernel/lens.wasm` Passes 1–2 equal that executable | Differential (I9) | `test_vars1_props.py` |
| `kernel/lens.wasm` fold equals the model's own compiled fold | Differential (I10) | `test_vars1_props.py` |
| On every two-cell log in three families (a genesis scope plus: an axiom relying on it; an acceptance of it; a foreign scope no acceptance admits), with symbolic threshold, origin, birth and one extra seal, the kernel does not panic or overflow, and refuses with a known code or answers with status bits that obey §4.2 (effective = not invalidated; active ⇒ effective, accepted, not retired, not superseded; stale ⇒ active; local ⇒ accepted; flags 0/1; the governing scope is a local scope) | Bounded (Kani 0.68, local: `kernel/assure.sh kani`, 4–7 min and 14–15 GB each; not in CI) | `kernel/src/lib.rs` `proofs` |
| The same for families with supersedes, retires or invalidates edges, an INVALID verdict, a scope rotation, a contract | **Not established**: they need deeper unwinding or more than 16 GB on this machine | — |
| The kernel does not panic, overflow or return an unknown code on arbitrary bytes whose commit count is at most 4096 | Tested (fuzzing: 13.9 M inputs in 10 min, seeded with real inputs; `kernel/assure.sh fuzz`); larger counts are skipped, see the time limit below | `kernel/fuzz` |
| `kernel/lens.wasm` rebuilds from source to `H_LENS_KERNEL` | Tested: on Linux in CI (`.github/workflows/check.yml`); on macOS in every release's checks (`tools/minds_chain.py`), not in CI |  |

## Changing the rules (§4.3) and the v2 rules (RULES-V2.md)

| Claim | Evidence | Where |
|---|---|---|
| A rotation to other rules is admitted only with exactly one rules-change decision, sealed by the governing admission quorum, whose three computations the gate replays: (a) the new rules give every status and the governing scope the old rules give over the chain so far; (b) on a counterexample chain the gate admits, the new rules give the named status bit the value named right and the old rules do not; (c) no Authorized cell or authorized edge of the old rules is lost, on either log; the counterexample is named by its canonical commit id, so a moved or deleted ref, a hex-named one included, does not change what was admitted | Tested, with mutants for every check (`m-rc-*`) | `test_vars1.py` 47–51, 59 |
| The gate, the chain reader and the release checks take commits only by canonical id in the repository's object format | Tested, with mutants | `test_vars1.py` 60, 61 |
| A rules change is admitted in one of four classes (AMENDMENTS.md), each with its own decision schema and evidence: a semantic correction as above; a resource hardening (on an input, under a budget of steps, the old rules exhaust it or trap and the new refuse with a resource code they declare); a validation tightening (the old give an output, the new refuse with a non-resource code); an implementation-equivalent change; the last three reproduce the chain so far byte for byte | Tested, with mutants for every check (`m-amend-*`) | `test_vars1.py` 62, 64–66 |
| Refusal, budget exhaustion, a fault and an output are distinct results; a budget counts steps (function and loop-body entries) of a module rewritten by `meter.py`, the same on every engine | Tested: metering changes no result on real v1, v1b and v2 inputs; a module that traps gives a fault with budget left and exhaustion with none, both ways mutated; every run gets a fresh instance, so 1500 aborted runs change no later result on v1, v1b or v2 (a second review found a reused instance turned an honest output into a fault after ~1300 aborts) | `test_vars1.py` 62, 71, 74 |
| (d) A rules change keeps every earlier one: each earlier counterexample gets the result its change established (a correction's bit by cell id; a hardening's or tightening's refusal within its budget); so v1b → v1 "as equivalent" is refused, and so is v1b → v2 (v2 reads v1b-born cells by type; (d) would refuse it second, since v2 cannot read the v1-encoded input) | Tested, with mutants | `test_vars1.py` 67 |
| (d) keeps the property an earlier change established, not its accidents: a hardening's or a tightening's input stays refused within its budget, with any code (Monday review 2026-10-28, F46) | Tested, with mutants: a successor refusing the fuzzer's input with another code is admitted; one refusing it only with more steps than the hardening's budget, or giving it an output, is refused. An input of another encoding is not carried, since no carrier exists; between v1 and v2 the reading rules refuse first (tests 67, 68), so (d) never meets one alone. Rules of a new encoding that read an older epoch need a carrier built with them | `test_vars1.py` 67, 92; VARS-1-SPEC.md §4.3; AMENDMENTS.md |
| A rotation from v2 to rules that read references as v1 does is refused; so is a rotation to v2 from a chain with a v1b epoch (v2 reads as v1 only cells born under `H_LENS_KERNEL`; Codex review r1 F1) | Tested, with mutants | `test_vars1.py` 68 |
| The v1b rules (`kernel/` with `commit-bound`, `H_LENS_KERNEL_V1B`) refuse an input claiming more commits than it has bytes (E-7) and are otherwise v1; the host's twin refuses the same chains; the default build is still `H_LENS_KERNEL` byte for byte | Tested (the fuzzer's input rebuilt: v1 exhausts 10^7 steps, v1b refuses; a chain of empty commits past the bound); rebuilt in CI and in every release that carries `kernel/lens1b.wasm` | `test_vars1.py` 58, 62, 63 |
| A gate-admitted chain stays within v1b's bound | **False**: the gate admits empty commits; ~3.6 K of them on a bare genesis cross it, and under v1b the crossing commit is refused (a commit adding a cell always fits) | `test_vars1.py` 63 |
| Before a rotation is recorded, every historical tip is replayed under its epoch's rules and the new rules, and every difference (commit, cell, bit, old, new) is listed; a hardening or an equivalent change is recorded only with none | Tested, with mutants (release condition in `tools/minds_chain.py change-rules`, not a gate rule): a manifest of other rules, tampered, or of a tip a writer has since passed is refused; differences need the digest accepted for a correction and refuse a hardening or an equivalent change; a return to earlier rules works | `test_vars1.py` 70, 73 |
| The verdict a decision names right is right | **Not established**: the gate checks only that the old rules disagree with it and the new agree; rightness is the claim of the quorum that seals the decision | spec §4.3 |
| The new rules agree with the old on inputs other than the chain so far, or refute them on inputs other than the counterexample | **Not established**: (a)–(c) compare two logs, not all inputs | — |
| A rules change whose point is a controlled refusal (a resource bound, a crash or hang made a refusal, a validation tightened) can be admitted | Tested: the hardening and tightening classes above; the commit-count bound is carried as a hardening | `test_vars1.py` 62–65 |
| A node holding the chain can replay a past rules change | Tested: the gate writes `refs/vars/evidence/<scope>/<decision>/<commit>` with the rotation for the counterexample and, transitively, every counterexample its chain's corrections name (a nested case included); a fresh clone fetching only the scope's ref and `refs/vars/evidence/*` replays it after the author's refs are deleted and gc'd; a hardening's input is an atom of the chain. Without the evidence (ref deleted and gc'd, a shallow fetch, a lost object) the replay reports `EvidenceMissing`, not a refusal. Radicle replicates the evidence refs with the chain (`tools/radicle-probe.sh`, two local nodes; not in CI) | `test_vars1.py` 69; `tools/minds_chain.py evidence`, `replay-changes` |
| `H_LENS_KERNEL` identifies everything the gate decides | **Not established, and false**: the host decides canonical bytes, types, replay, rule-6 parsing and rules-change admission; the canonical-id fix of PR #1 changed the gate without changing `H_LENS_KERNEL`. A release names the host by its `main` commit and, from this release format on, by its release profile (below) | `tools/minds_chain.py` |
| A rotation from v2 back to v1 is refused, with or without a decision | Differential (kernel E-25 and twin) and tested | `test_vars1.py` 52, 53 |
| `kernel2/lens2.wasm` rebuilds to `H_LENS_KERNEL_V2` | Tested: in CI; in every release's checks when the released commit carries `kernel2/` | `tools/minds_chain.py` `kernel_checks`, `test_vars1.py` 58 |
| v2 reads a v1-born cell as v1 does, a v2-born cell by type, and checks the reference list it is given | Tested (conformance only; the property suite and Kani exercise v1 only, and the prototype's Lean `Refs.lean` is not on main) | `test_vars1.py` 54–57 |
| A custom schema's `cell` mask is parsed correctly from its descriptors | Assumed: host parsing in the trusted base (RULES-V2.md F42) | — |
| The spec's text changes in the same decision | Assumed: nothing checks the text | — |
| v2's typed references, descriptor → mask → reference positions, as the host reads them (`schema_cell_mask`, `cell_refs`), equal the answers of an oracle that does not call the host's parser (`proofs/Vars1/Mask.lean`, compiled as `vars1mask`), on 310 cases of the domain schema admission accepts (F42): `proofs/vectors/f42.json`, which CI regenerates with the oracle and byte-compares | Differential (host against the oracle's vectors), with mutants of the mask and of the reading; the kernel still takes a custom schema's mask from the host, so the host's parser stays in the trusted base, now checked against the oracle on the corpus rather than proved | `test_vars1.py` 89; `tools/f42_vectors.py`; `proofs/Vars1/Mask.lean` |

## Replay (§5)

| Claim | Evidence | Where |
|---|---|---|
| `REPLAYED` means one advance from the root by `spent_total` reaches exactly the checkpoint's state | Proved (abstract machine) | `Replay.lean` |
| Same for Book I's evaluator | Proved | `Vars1Sigma/Link.lean` |
| A Settled contract with `required_comp` has a full replay to the expected normal form, or, when it expects `H_CYCLE_PROVEN`, a cycle witness of its computation that `verify_cycle` proves | Proved; checked on implementation (I4, whose sequences include `M M` cycle witnesses, true, `NOT_ASSESSED` and refused) | `Pass3Replay.lean`, property suite |
| Python replay (`sigma_resume`) matches the abstract machine | Assumed (transcribed by hand) | — |
| A cycle witness `checkCycle` accepts means: from the start, every number of actions fires and no budget reaches a normal form or a blocked reference; a normal form and an accepted cycle exclude each other | Proved (abstract machine; for Book I's evaluator too) | `Cycle.lean`, `Vars1Sigma/Link.lean` |
| A Settled contract or decision with `required_comp ≠ H_EMPTY` expecting `H_CYCLE_PROVEN` has a cycle witness of its own computation, which never reaches a normal form | Proved (hypothesis: no term hash equals `H_CYCLE_PROVEN`) | `Pass3Replay.lean` `settled_cycle_no_normal_form` |
| The same without `required_comp` | **Not established, and false**: a contract with `required_comp = H_EMPTY` settles on `H_ATTESTED` verdicts alone (§4.2), whatever its `expected_outcome` says; such a Settled bit is an attestation, not a replay | `test_vars1.py` 75 |
| `sigma_resume.verify_cycle` gives `checkCycle`'s verdict, the gate's cycle check (`gate_cycle_witness`) gives `gateCycle`'s (a well-shaped witness whose entry is beyond the host ceiling is `NOT_ASSESSED`, not refused), and Pass 3 (`cycle_witness_answers`) counts a witness only when `checkCycle` proves it, for its own computation and `H_CYCLE_PROVEN`; the gate proves exactly what `checkCycle` proves (`gateCycle_proven_iff`) | Proved (`gateCycle_proven_iff`) and differential (I12, now with witnesses whose entry is above the gate's ceiling: compiled `checkCycle` over generated tables, true and false witnesses, the host ceiling varied; the two functions are the ones the gate and the lens call) and tested with mutants (`m-cycle-*`, killed by test 75 on the real `M M` cycle; each also fails I12, checked by hand, not by the mutants job) | property suite, `test_vars1.py` 75 |
| The gate's own bound `1 ≤ cycle_actions ≤ cycle_cost` | Tested, with mutants (`m-cycle-bound-*`): `verify_cycle` stubbed to accept, so only the gate's bound is left to refuse (test 87) | `test_vars1.py` 75, 87 |
| `verify_cycle` matches `checkCycle` on Sigma terms and the rich profile | **Not established**: I12 substitutes a table for `STEP`; the rich profile is not mechanized, and its `M M` cycle is tested only | — |

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
| An offline client's Pass 3 equals the lens's Settled | Differential (I11) on v1 chains and on v2 chains whose `hash` slots decide a foreign endorsement | property suite (two runs); `test_vars1.py` 90 |
| A bundle cannot hide a verdict or seal its projection's tip holds | Tested | `test_vars1.py` 17, 21 |
| `verify-*` accepts only against keys the reader pinned | Tested, with mutants | `test_vars1.py` 39 |
| Every Settled release on `refs/vars/heads/minds` was checked by each of its evaluators in a fresh checkout | Recorded on the chain; each member's checks are its own claim | `tools/minds_chain.py` |
| Members are independent | **Not established**: two AI agents (Claude; Gemini via antigravity) with keys on one machine and OS account. The third member, the GitHub Actions witness, holds its key on GitHub and reruns the checks on a GitHub runner, but what it runs is `main`'s workflow, which the maintainer writes and the owner merges: a second host, not a second judgement | README |
| The rotation delay (latch 4a) and the rules-change quarantine (4b) give a removed key or a vetoer time to act | **Not established**: the 16 commits are counted, not timed. The admission quorum alone can make them at once (on `refs/vars/heads/minds` it is 1 of 3 keys), so they give an interval only to a party that watches the chain while it lasts. A reader who pins keys (§4.4) is protected without watching. A real period of objection needs a witness outside the initiator's own history (Monday review 2026-10-28, F45) | VARS-1-SPEC.md §4.1 |
| A projection is current | **Not established**: acceptance is about its tip | spec §4.4 |
| A release names its release profile: the SHA-256 of the bytes of every file the released commit tracks, read from git's objects (not the commit id: SHA-256 throughout, and without the commit's metadata); two commits whose gate differs have different profiles and may have the same rules hash. Not narrower: profiled code can load any file of the commit (a module shadowing the standard library's, bytecode, a package, a namespace module, a ZIP on its path, a file it reads; Codex review of PR #4, rounds 3–6), so a list of the files an admission depends on would be wider than anything that checks it | Tested, with mutants | `test_vars1.py` 76, 80; `tools/minds_chain.py profile` |
| `verify-release` recomputes the profile a release names at its commit and records INVALID when the commit's files are not the ones named, even when every check passes | Tested, with mutants | `test_vars1.py` 76 |
| `witness` verifies every release waiting for its key's verdict, and only those: none recorded before its key joined, none it has answered (ATTESTED or INVALID), nothing for a key not on the roster; a release it answered before and whose answer Pass 3 no longer counts is left to it, and the others are still verified; a verdict that attests nothing is no answer | Tested, with mutants | `test_vars1.py` 93–95; `tools/minds_chain.py` `witness`, `awaiting`, `unanswered` |
| `verify-release` reruns a release's checks against the chain as it stood when the release was recorded, in a clone that shares this repository's objects but not its refs: a member who joined or left since is not in the roster they read, and `release` reads the chain as it is | Tested, with mutants | `test_vars1.py` 96; `tools/minds_chain.py` `checks_at`, `recorded_at` |
| The GitHub Actions witness's key never was on the maintainer's machine | By construction, not tested here: `witness-key.yml` makes it on a runner and refuses unless the environment `witness` deploys from `main` alone. It rests on GitHub's environment protection and on the owner's GitHub account, whose holder controls what `main`'s workflows do with it | `.github/workflows/witness-key.yml`, `witness.yml` |
| The profile names the interpreters (Python, node, Lean, cargo) | **Not established**: they come from the host, and the profile does not name them; a release the GitHub Actions witness attests passed on two hosts' interpreters (the maintainer's macOS and an Ubuntu runner) | — |
| `status` tells merged from Settled: for each release, as Pass 3 reads it (its evaluation policy, the release's or for an early release the scope's current admission policy), the evaluators whose endorsement counts, those with a live INVALID on it, and, while it is not Settled, those that have not answered; whether `main` is released and how many commits it is past its last release; and it writes nothing | Tested, with mutants: a verdict attesting nothing, a superseded ATTESTED or INVALID, and an early release after a roster replacement are read as Pass 3 reads them | `test_vars1.py` 77, 79; `tools/minds_chain.py status` |
| A commit with a symlink or a submodule has no profile (their bytes are not in the commit) | Tested, with mutants | `test_vars1.py` 76 |
| A release statement names its profile after its checks, so a reader of the earlier format still reads its commit, rules and pins | Tested (the earlier pattern, verbatim) | `test_vars1.py` 76 |
| A claim quoting ASSURANCE.md is held only by the claim cell of exactly one claim-table row of assurance.json whose evidence cell begins with the claim's status; ASSURANCE.md is exactly the rendering of assurance.json, so nothing in it is parsed and no hidden or quoted text can hold a quote (nine review rounds on hand-read Markdown, Codex review of PR #4, led here) | Tested, with mutants | `test_vars1.py` 45; `tools/check_claims.py` |
| Every paragraph, list item, table and code block of VARS-1-SPEC.md §0–§5 is a part of spec.json that carries a claim or an informative passage whose quote is in its own text; VARS-1-SPEC.md is exactly the rendering of spec.json, a part's section is counted from the headings and never read from the part, a heading part is one heading line and a gap one blank line, and every claim and informative passage is carried by some part. Nothing parses the Markdown | Tested, with mutants | `test_vars1.py` 45; `tools/check_claims.py` |
| An unburned claim says in `reason` why no mutant burns it, and only an unburned claim carries one; the debt table of ASSURANCE.md is the rendering of those reasons | Tested, with mutants | `test_vars1.py` 45; `tools/check_claims.py` |
| Every normative character of a §0–§5 part is covered by the quotes it carries | **Not established**: a part may say more than its carriers' quotes, as a block did before; block boundaries are now declared in spec.json, not inferred (closing Codex review of PR #4, round 9, F4), but what a part says beyond its quotes is held by nothing | — |

## Who reads which rules

What each reader of a chain interprets, at the commit a release names (`profile` lists the modules carried and the
ones the offline verifier reads, from their own bytes). "Refuses" means a controlled refusal or an `unsupported`
result, never a reading.

| Reader | v1 (`H_LENS_KERNEL`) | v1b (`H_LENS_KERNEL_V1B`) | v2 (`H_LENS_KERNEL_V2`) |
|---|---|---|---|
| The gate and lens (`vars1.py`) | Runs it; Python twin | Runs it; Python twin | Runs it; Python twin reading the typed references |
| The offline verifier (`verify/minds_verify.py`) | Reads projections and attestations; with `--kernel` and Node, it runs the rules on the input | Reads them, in v1's encoding (v1's output; one more refusal); likewise with `--kernel` | Reads them, in the v2 encoding: references from the input's own list, each checked against its cell; with `--kernel` and Node, the kernel's check of the list too |
| The Lean model (`vars1exec`, `vars1fold`) | Compared with the kernel (I9, I10) | Not compared (v1 with one more refusal) | Not modelled on main |
| Kani and the fuzzer | Bounded / fuzzed | Not run | Not run |

So a chain moved to v1b or v2 keeps its gate and its offline verifier, which reads every rules identity the host
implements: the host refuses to load otherwise (`vars1.check_offline_reads`, `test_vars1.py` 90). It leaves behind
the Lean model and Kani and the fuzzer, which an activation has to name (RULES-V2.md §7).

## What each result trusts

| Result | Computed by | Trusted, not checked here |
|---|---|---|
| A commit is admitted | `vars1.py` gate, the kernel under node | Python, node and its wasm engine, git's object store, SHA-256, Ed25519 (`minds_verify.py`'s own implementation, 34 vectors), `sigma_resume` (bytes pinned at import) |
| A status bit (Passes 1–2) | `kernel/lens.wasm` | As above; the kernel's equality with the Lean model is differential, not proved |
| Settled (Pass 3) | `vars1.py` | Python replay of Book I (transcribed by hand from the abstract machine) |
| An offline `accepted` | `verify/minds_verify.py`, standard library only | Python, the pinned keys the reader supplies, and the projection's witnesses for everything Pass 3 does not recompute (under v2, that the input's reference list is the typed one: the verifier checks each entry's value, the kernel its type); with `--kernel`, the `node` on PATH (run with an empty environment) and its wasm engine compute the output here, and the witnesses still vouch that the input faithfully encodes the chain at `tip`: its cells, seals and parsed facts (Codex review of PR #24) |
| A release is Settled | every member's `verify-release` | Each member's host: its interpreters, its checkout, and that it ran the checks it signs |

## What would follow (what-if)

| Claim | Evidence | Where |
|---|---|---|
| `what_if` admits a hypothesis through the gate on a candidate commit and moves no ref; a hypothesis the gate refuses is refused, not evaluated | Tested, with mutants | `test_vars1.py` 81; `vars1.py` `what_if` |
| `what_if` reports the cells of the hypothesis's region (the cells it names, closed under two steps: a cell relying on a region cell, and the cell a region verdict judges) that keep their statuses through other grounds, and every cell whose statuses change, with its bits before and after and its shortest dependency path: from a hypothesis cell, or an earlier cell a hypothesis seal newly seals, through what a hypothesis cell names, then only to a cell that relies on the last or to the cell a verdict judges, never back through a shared ground; empty when no such route exists. A path is a route of dependence, not a sufficient explanation; equal consequences give an equal digest | Tested, with mutants: a failed ground takes its transitive dependents with it; a decision stays Settled through a second verdict and loses it when both fail; a ground on another basis is outside the region; the path to a dependent of two grounds runs down its own chain, not back through the other ground; a decision settled by a new seal is reached from the sealed verdict | `test_vars1.py` 81 |
| A held decision whose counted endorsements change carries its threshold and its counts before and after: Settled kept on a thinner margin is reported though no status bit changes | Tested, with mutants | `test_vars1.py` 81 |
| `transcript` binds the consequence lists to their context (mode, scope, tip, the rules at the tip and at the candidate, the hypothesis cells, and the cell and key of every hypothesis seal); `digest` binds the lists alone, so two signers of one hypothesis share the digest and not the transcript | Tested, with mutants: a second signer gives the same digest and another transcript | `test_vars1.py` 81 |
| An assumed hypothesis (`what_if(..., assume=True)`, `minds_chain.py what-if CELL... --assume PUBKEY`) needs no key: its seals name a key and carry a zero signature, the gate checks everything else as for an admission (the key against the policy, references, replay), the run uses a throwaway instance whose caches the caller never shares, and its candidate is refused by any real check; the report carries `mode: assumed`, the digest of the sealed run and another transcript | Tested, with mutants: a reader without keys gets a member's consequences, restoration included; a real signature, a weak key and a key outside the policy are refused; the caller's caches hold no assumed seal and its candidate cannot be admitted | `test_vars1.py` 81, 82; `vars1.py` `what_if`, `_checked_object`; `tools/minds_chain.py` `what_if` |
| Every cell whose statuses a hypothesis changes is reported, inside its region or not | Tested, with mutants: a decision a hypothesis's new seal settles lies outside its region and is still reported (test 81); a `lost` confined to the region drops it | `vars1.py` `what_if` |
| A release decision relies on one cell per check (what ran, its result, the commit and profile), and a member's verdict relies on that member's own check cells, so `minds_chain.py what-if CELL [--key FILE]` says what a failed check takes with it (sealed by a member's own key or the maintainer's, never created; no ref moves and nothing is filed on the chain, though the candidate's objects stay unreachable in the object store until gc): a member's check makes its verdict Stale and an n-of-n release loses Settled; the maintainer's check makes the release Stale | Tested, with mutants | `test_vars1.py` 82; `tools/minds_chain.py` `release`, `verify_release`, `what_if` |
| `what-if` says what each lost cell would need to regain what it lost: the grounds it relies on that no longer stand, and for a decision that lost Settled its threshold, the endorsements still counted and those that fell away; with `--restore` the signer also supposes it ran its own invalidated checks again, and a release whose only fallen endorsement was the signer's holds through the replacement | Tested, with mutants (no replacement made with another member's key restores anything: Pass 3 counts the sealing key) | `test_vars1.py` 82; `tools/minds_chain.py` `what_if` |
| Releases recorded before this format rest on their checks | **Not established, and false**: their checks are text in the statement only; `what-if` reaches them only through their verdicts | — |

## A witness checked without the lens (experiments/witness)

A spike: a decision's cone and the seals that settle it, as a proof term that `experiments/witness/check.py`
checks against the store's bytes, sharing no code with `vars1.py` or the offline verifier. The same term, as a
derivation, is checked by a checker written in Lean (`proofs/Vars1/Witness.lean`, compiled as `vars1witness`)
whose acceptance carries a theorem. What neither covers is in the README: the negative part (no edge kills
the cone) is read over the store at the tip, which the reader pins as the admitted chain.

| Claim | Evidence | Where |
|---|---|---|
| `check.py` answers `HELD` for a witness term only if the lens holds its decision Settled at the term's tip, provided the store at the tip is that scope's admitted chain; outside its fragment the answer is `NOT_COVERED` | Tested, exhaustively over every subset of verdicts on two generated histories after a failure, with a mutant for every check; the argument from §4.2 is prose here; `vars1witness` (below) carries it as a theorem | `experiments/witness/test_witness.py` 01–10; README.md |
| The term reads one way: a witness term that is not UTF-8 JSON, or whose object names a key twice, is refused (`FORMAT`), and a crash of the checker exits 3, which no verdict uses | Tested, with mutants | `experiments/witness/test_witness.py` 11 |
| `vars1witness` answers `ACCEPT` for a derivation only if the model of §4.2 holds its decision `Settled` at the tip, given that the store `check.py --lean` decoded agrees with the model there and is the scope's admitted chain (`Pin`) | Proved (`witness_sound`; axioms `propext` and `Quot.sound` only; `edge_present` and `stale_pin` prove two of `Pin`'s hypotheses of the model's fold and Pass 2). The decode is tested: `check.py` and `vars1witness` agree on every term of tests 03–09, and four mutants of the decode break that agreement | `proofs/Vars1/Witness.lean`; `experiments/witness/test_witness.py` 03–09; README.md |

## How a mutant counts

| Claim | Evidence | Where |
|---|---|---|
| A mutant counts as killed only when an assertion fails on what the code does (an expected exception not raised, values that differ); an expected exception met with another message, on one line or several, with a custom `msg` or not, is a survival (the input is still refused), and so is any other error. `tools/mutant_test.py` decides where assertRaises checks, not from the printed text | Tested, with mutants: a fixture of eleven tests, each with its expected verdict | `test_vars1.py` 84; `tools/mutant_test.py`, `tools/run_mutants.py` `verdict` |
| A refusal that a named check and the gate's net for crashes both hold says the named check's reason, not the net's; a mutant that removes only that reason is declared `diagnostic`, burns only this claim, and `tools/run_mutants.py` refuses the declaration both ways: a mutant any of its tests catches with only the refusal asked, in any order, is not diagnostic; one caught only by the reason is not a burn of what is refused; and a run asking only for the refusal that crashes is no ground to call a later catch a lost reason (Codex, P27-F1 and P27-F2) | Tested, with mutants (diagnostic): four named reasons, each lost while its input stays refused; the runner's two modes on fixtures | `test_vars1.py` 50, 78, 88, 84; `tools/run_mutants.py` `classify`; `tools/check_claims.py` |

## Not burned, and why

Rendered from the `reason` of every unburned claim in claims.json; `check_claims` refuses an unburned claim
without one, and a reason on any other. A refusal more than one layer holds is burned layer by layer, each layer
asked alone on an input only its rule refuses (test 87); a value checked as the module loads, by a mutant that
names that check; a guard whose absence falls into the gate's net for crashes is not burned by a test that asks for the
named refusal (`_gate_refuses`): that loses the reason, not the refusal, and burns only a claim about the reason
(`diagnostic`). A refusal the net also holds is listed here, unburned (Codex, challenge of the G3 closure).

| Unburned claim | Why no mutant burns it |
|---|---|
| `gate.references` | Held twice: by Check #4 and, beneath it, by the lookups that read each reference, whose KeyError the gate's net for crashes turns into a refusal. Either alone refuses a missing reference, so no single-site mutant admits one; m-refs-seal removes only Check #4's named reason (Codex, challenge of the G3 closure, 2026-10-28). |
| `rules.change.refusal` | Held twice: by the named refusal and, beneath it, by the four digests that read every run, whose missing output is an IndexError the gate's net turns into a refusal. Either alone refuses the rotation, so no single-site mutant admits it; m-rc-refusal removes only the named reason (Codex, challenge of the G3 closure, 2026-10-28). |

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
scope only by a resource hardening (AMENDMENTS.md), never from v2, and `refs/vars/heads/minds` moved to v2 on 2026-10-28.
The fuzzer builds v1 and skips inputs with `C > 4096` so it keeps looking for correctness defects.

Kani runs the kernel on the host, where `usize` is 64 bits; wasm32 has 32. An overflow possible only at 32 bits is
outside these checks (the kernel bounds every count by the input length, which wasm32 already bounds). The bounds
are small; they find shallow defects in every branch they reach, not deep ones beyond the bound.
