# Witness spike: a proof term for "this decision is in force"

A spike, not a feature: does Curry–Howard say anything literal about minds? It does, on a fragment.

The lens computes `Stale` as the least fixed point of a monotone operator (§4.2, proved in `proofs/Vars1/Pass2.lean`
and `Lfp.lean`). The positive part of the rules says two things:
- a cell stands while what it relies on stands;
- a decision is Settled while enough policy keys seal ATTESTED verdicts on it.

Where no edge touches a decision's cone, being in force amounts to having a derivation:
- if the decision is in force, its cone and enough sealed verdicts exist (completeness);
- if they exist, it is in force (soundness: What HELD establishes, below).

For the checker written in Lean both directions are proved on that fragment (The Lean checker, below). For
`check.py` they are argued and tested.

Curry–Howard adds that the derivation can be an object: a term that a checker type-checks.

Here the term is the decision's **cone** together with its **endorsements**:
- the cone is the decision and the verdicts that count, closed under `relies`;
- the endorsements are seals, by distinct keys of the decision's evaluator policy, on ATTESTED verdicts that judge
  the decision.

`prove.py` makes such a term from the lens. `check.py` checks it at a commit and answers `HELD`, `REFUSED` or
`NOT_COVERED`. A checker written in Lean checks the same term as a derivation, and its acceptance carries a theorem
(The Lean checker, below). `check.py` uses no code of minds:
- its constants are the spec's tables;
- its parsers and its Ed25519 check are its own;
- it uses the standard library only.

Where Curry–Howard stops is the finding. The term proves what holds. That nothing kills the cone (no notice, no
retirement, no supersession, no INVALID verdict that withdraws a named key) is not part of any term: it is read over
the whole store at the tip, a closed-world assumption.

```
python3 -I experiments/witness/check.py REPO TERM.json [--scope-cell HEX]
python3 -I experiments/witness/check.py --lean REPO TERM.json [--scope-cell HEX] | proofs/.lake/build/bin/vars1witness
```

The term must read one way. A term that is not UTF-8 JSON, or whose object names a key twice, is `REFUSED`
(`FORMAT`): Python keeps the last value of a repeated key and other readers the first, so it has no single reading;
`NaN`, `Infinity` and `-Infinity`, which Python's json reads, are not JSON.
Exit 0 is `HELD`, 1 `REFUSED` or `NOT_COVERED`, 2 a wrong command line; 3 is an error of the checker, which no
verdict uses (an uncaught Python error would exit 1, the code of a refusal).

```json
{"format": "minds.witness.held@1", "scope": "proj", "tip": "<commit id>", "decision": "<cell id>",
 "cone": ["<cell id>", "..."], "endorsements": [{"verdict": "<cell id>", "seal": "<seal id>"}]}
```

## What HELD establishes

`HELD` means that the decision is Settled at the tip under the v1 or the v2 rules, provided the store at the tip is that
scope's admitted chain. The argument below follows §4.2. For `check.py` it is prose, which test 04 checks; for the Lean
checker it is a theorem.

1. **Every cone cell is Active.**
   - It is local, so it is Accepted.
   - No cell of the store invalidates, retires or supersedes it, so it is Effective, not Retired and not Superseded.
   - It supersedes nothing, so every supersedes edge it has is authorized, vacuously.
2. **No cone cell is Stale.** The cone is closed under `relies` and all its cells are Active. The rounds of Pass 2
   start from the empty set, so no round can add a cone cell.
3. **The decision is Settled.**
   - It requires no computation.
   - Each endorsing verdict is in the cone, so it is Active and not Stale. It is a verdict on the decision, ATTESTED,
     and attests the decision.
   - No endorsement is withdrawn. §4.2 withdraws a key's endorsement through a verdict by a live INVALID verdict on
     the decision under the same verifier id that the key seals, and by no other: a verifier id is free text. The
     checker finds every INVALID verdict on the decision under an endorsing verdict's id and sealed by the endorsing
     key. If one meets the stand conditions of step 1 down its `relies` (so it is live), the term is `REFUSED`
     (`WITHDRAWN`); if one does not, whether it withdraws is the lens's to say (`NOT_COVERED`, `INVALID_VERDICT`).
   - Each seal is in the store at the tip, under the only scope cell, and verifies. Its key is one of `EvalPol(d)`:
     the decision's own policy, else the scope's admission policy.
   - The distinct keys meet the threshold.

**What HELD does not say.** It is about Settled, not Grounded (§4.2). A decision can be HELD while a decision in its cone
is not Settled: the `stand` rule reads `Active` and not Stale, as the lens's Pass 2 does. To ask whether what it rests on
is settled too, read `grounded` in the lens, or `grounded_at_tip` of an attestation bundle.

**What is checked from bytes.**
- Every object hashes to its name.
- Every signature verifies.
- The policy keys are fixed by the decision's id, which covers its policy atom's id, and by the scope cell the reader
  pins.
- The threshold is met.

**What is read over the store, and holds only if the store is complete.** There is no kill edge, no INVALID verdict
that an endorsing key seals under its verdict's verifier id, no second scope and no foreign cell. `check.py` runs no
gate: that the tip is the admitted chain is the reader's pin.

**One gate rule is relied on, not rechecked.** Evaluator keys lie within the admission roster (§3 step 3). So a seal
by an evaluator key is an admitted endorsement.

## The Lean checker

`proofs/Vars1/Witness.lean` holds a checker, `accepts`, and a theorem, `witness_sound`: if `accepts` holds for a
derivation, the model of §4.2 (`proofs/Vars1`) holds its decision `Settled` at the tip. The checker is compiled as
`vars1witness` (`lake build vars1witness`). It depends on the axioms `propext` and `Quot.sound` only.

A derivation is a list of lines. Each names its rule, its conclusion and its premises, and every premise is the
conclusion of an earlier line, as in open-ontologies' `OOCert.horn_certificate_sound`.

| rule | concludes | checks |
|---|---|---|
| `stand c` | `c` stands (`Active`, not `Stale`) | `c` is a local cell of the store; no cell of the store invalidates, retires or supersedes it; it supersedes nothing; its premises are exactly that each cell it relies on stands |
| `endorse w k` | `k` is among `w`'s endorsers | a seal of the store on the local cell `w`, under the scope cell, by `k`, a key of the admission roster |
| `settle d` | `d` is `Settled` | `d` is a contract or decision that requires no computation; `d` stands; each endorsement among its premises is on a standing ATTESTED verdict, with an empty witness slot, that judges and attests `d`, by a key of `d`'s evaluator policy that no INVALID verdict of the store withdraws (one on `d`, under the verdict's verifier id, that the key seals, or a foreign one); the distinct keys meet its threshold |

`check.py --lean` writes the line `vars1witness` reads: the store at the tip, decoded by `check.py`, and the term as
a derivation. The decoder writes a `stand` line per cone cell, after the cells it relies on, an `endorse` line per
endorsement and one `settle` line. It writes only the seals that verify: the term's, and every one on an INVALID
verdict, from which the checker reads what each withdraws. The Lean checker answers `ACCEPT` or `REJECT`.

The Lean checker does not ask whether an INVALID verdict is live. A withdrawal the model would not make only leaves a
key uncounted, so soundness holds; where it matters, `check.py` answers `NOT_COVERED` and the Lean checker `REJECT`.

**What the theorem assumes** (`Pin`, hypotheses, not axioms):
- **The decode is faithful.** On every cell of the store, the model agrees with what `check.py` decoded in the
  fields the checker reads, a verdict's verifier id among them. A cell is present exactly when the store holds it. A
  decoded policy meets its quorum with threshold many distinct keys.
- **The decode holds every seal of an INVALID verdict.** Each cumulative endorser of a local INVALID verdict has a
  seal of the store on it, under a scope that governed, by a key of its roster: the absence of a withdrawal is read
  from them, so it is part of the negative part.
  Hashes, the cell layout and the signatures are `check.py`'s. They are tested, not proved.
- **The store at the tip is the admitted chain.** This is the reader's pin, as for `check.py`, and it has these parts:
  - the Pass 1 equations hold;
  - an edge latches only from a present cell (`edge_present` proves this of the fold);
  - `Stale` satisfies the Pass 2 equation (`stale_pin` proves this of the model's `Stale`);
  - a verified seal under the scope cell, by a roster key, on a local cell is among that cell's cumulative
    endorsers (§4.1).

The proof never uses that `Stale` is the least fixed point. Each cell that stands is proved not stale from the cells
it relies on, which earlier lines conclude. So soundness holds for any solution of the Pass 2 equation.

The Lean checker checks one thing that `check.py` leaves to the gate: a counted verdict's witness slot is empty. On an
admitted chain it holds, so the two checkers do not differ there.

**Completeness** (`proofs/Vars1/WitnessComplete.lean`). `prove` builds a derivation from the store alone:
- stand lines for the decision and for every verdict that counts for it (an ATTESTED verdict with an empty witness slot
  that judges and attests it, and that meets the stand conditions down its `relies`);
- an endorse line for every key of the decision's evaluator policy with a seal on such a verdict, under a scope of the
  chain and by a key of that scope's roster;
- the settle line.

`witness_complete`: if the model holds the decision `Settled`, `accepts` takes that derivation. With
`witness_sound`, `accepts_iff_settled`: on the fragment the checker decides `Settled`. Axioms `propext` and
`Quot.sound` only.

The fragment (`Fragment`) is where the checker's rules read as the model's:
- the decision requires no computation;
- every INVALID verdict on it is local and live (the model withdraws a key only through a live one; the checker does
  not ask);
- its live cone (the decision, the verdicts of `W_max`, what they rely on) holds local cells that supersede nothing
  and that no cell of the store invalidates, retires or supersedes (the model counts only an authorized edge from an
  Effective cell; the checker refuses any).

Completeness needs the decode to be complete, where soundness needs it faithful (`PinComplete`):
- what a live cell relies on is live (`stale_complete` proves it of Pass 2 `Stale`);
- the store holds a seal for every cumulative endorser of a local cell, under a scope of the chain, by a key of its
  roster;
- a policy that meets its quorum does so with threshold many distinct keys of it;
- the decision's evaluator policy is among the decoded ones.

It also needs a rank of `relies` that bounds the prover's depth. Cells are named by the hash of their contents, so
none relies on one that names it.

`check.py --lean --prove` writes the store with every seal that verifies on a verdict of the decision, and no
derivation; `vars1witness --prove` runs `prove` on it, to a depth one more than the store's cells, then `accepts`.

**Rotations.** A seal counts under the scope that governed the commit that admitted it (§4.1: each is checked under
its own commit's scope), so after a rotation the seals made before it still count. The checker reads the governing
chain from the store: the one scope cell no other supersedes (which must be the reader's pin, if one is given), then
the one scope each supersedes, back to the genesis. Cell ids name their content, so the chain has no cycle, and with
one such tip every scope cell lies on it. A seal counts if its scope is on the chain and its key is in that scope's
admission roster; `Pin` states that such a seal is among the cell's cumulative endorsers, which the gate makes true by
admitting a seal on a local cell only under the governing scope. Under v2 a rotation can wait (§4.1 latches 4a, 4b);
only the newest can, since a new scope is refused while one waits, and it waits only if it drops a key or changes the
rules. The fragment leaves those out. The rules version matters nowhere else here: v2 changes which values are
references, and that decides only the acceptance of foreign cells, which the fragment has none of.


Outside the fragment the answer is `NOT_COVERED` and never `HELD`: there, the lens decides.

| code | when |
|---|---|
| `SCOPES` | not exactly one scope cell that no other supersedes (two: a vetoed rules change) |
| `WAITING` | under v2 the newest rotation drops a key or changes the rules, so it may still wait; or the pinned scope is superseded |
| `RULES` | a scope of the chain names rules other than v1 and v2 |
| `FOREIGN` | the store holds a cell of another origin |
| `COMPUTATION` | the decision requires a computation, which replay decides |
| `INVALID_VERDICT` | an INVALID verdict on the decision, under an endorsing verdict's verifier id and sealed by the endorsing key, does not meet the stand conditions: whether it is live, and so withdraws the key, the lens decides |
| `KILL_EDGE` | a cone cell is invalidated, retired or superseded by any cell, or supersedes one |

The fragment is small, and the reason is the finding again. Test 08 shows decisions that the lens settles and the
checker leaves `NOT_COVERED`:
- a ground whose notice was itself invalidated;
- an INVALID verdict that would withdraw a named key and is itself Stale;
- a rotation under v2 that drops a key without that key's seal, so it waits.

An INVALID verdict that withdraws one key, and leaves the others, is inside (test 15).

To prove that an edge *does not count*, a term would need a proof that its source is itself invalidated, or that it
is unauthorized: negation in strata, not a Horn derivation. A decision rebound by `supersedes`, which real chains do,
is outside too. The live minds chain is inside: its v1 epochs, its rotation to v2 and its joins under both are
rotations of the fragment, and test 13 holds every decision the lens settles there.

`REFUSED` means the term is wrong. Its codes:

| code | the term is wrong because |
|---|---|
| `FORMAT` | it is not in the term format |
| `TIP` | the tip is not a full commit id that names itself as a commit |
| `STORE` | an entry is not a store object, or an object does not hash to its name |
| `SCOPE` | the store's scope is not the term's, or the pin is not a scope cell of the store |
| `DECISION` | the decision is not a contract or decision cell |
| `CONE_MISSING` | the cone names a cell the store does not hold |
| `CONE_OPEN` | the cone is not closed under `relies`, or lacks the decision or an endorsing verdict |
| `VERDICT` | an endorsement is not an ATTESTED verdict on the decision |
| `SEAL` | a seal is not on its verdict, is under a scope that did not govern, or does not verify |
| `KEY` | a seal's key is not in the roster of the scope it is under, or not in the evaluator policy |
| `WITHDRAWN` | an endorsement is withdrawn: an INVALID verdict on the decision under its verdict's verifier id, sealed by its key and meeting the stand conditions |
| `THRESHOLD` | there are too few distinct policy keys |

## Evidence

`test_witness.py` holds the tests; chains are admitted through the real gate. Every check in tests 03–09, 12, 13 and 15 runs both
checkers on the same term and requires that `vars1witness` answers `ACCEPT` exactly when `check.py` answers `HELD`. It
does so wherever the Lean checker is built, and fails where `MINDS_REQUIRE_LEAN=1` and it is not, as in CI. `histories.py` generates the
histories: a project of three maintainers whose ground fails, the generator of the withdrawn G6 pilot
(`experiments/g6/RETIRED.md`).

| test | what it checks |
|---|---|
| 01 | RFC 8032 vectors and vars1's own signatures verify. A changed message, S + L, a key of small order and a non-canonical y do not. |
| 02 | `check.py` imports the standard library only, and its constants equal vars1's. |
| 03 | Before the failure, every decision of a history of each size (S and L) gets a witness that is HELD. |
| 04 | **Soundness, exhaustively on two histories after the failure.** A decision the lens settles gets a HELD witness; one it does not gets none. No term over any subset of a decision's verdicts, each with its whole cone, is HELD for a decision the lens does not settle. There are 222 such terms. Of the 93 for lost decisions, none is HELD: 86 are NOT_COVERED (`KILL_EDGE`) and 7 REFUSED (`THRESHOLD`). Of the 129 for settled decisions, 59 are HELD, 58 REFUSED (`THRESHOLD`, one key) and 12 NOT_COVERED (a stale verdict in the subset). |
| 05 | A lost decision cannot be passed off by leaving the fallen ground, or a stale verdict, out of the cone. |
| 06–07 | A wrong term is refused for its own reason, including verdicts that judge or attest another decision, a NOT_ASSESSED verdict, a custom-schema cell shaped like a verdict, and a key outside the evaluator policy. |
| 08 | Outside the fragment the answer is NOT_COVERED: a withdrawn notice in the cone, a Stale INVALID verdict that would withdraw a named key, a rotation under v2 that waits, rules other than v1 and v2, two scope cells superseding one. A decision left not Active by an unauthorized supersedes edge is not HELD. |
| 09 | A store the gate never saw: a seal that does not verify, a seal under another scope, bytes that do not hash to their name, a missing object, an entry outside `cas/`, a decision requiring a computation, a foreign cell. |
| 10 | `check.py`, copied alone into an empty folder and run with `-I`, works. |
| 11 | A term that names its decision twice, the held one last, is refused, and so is one that names a seal twice. So are a truncated term, one that is not UTF-8, one that is not an object, and one holding `NaN` or an infinity, which Python's json reads and JSON does not have. A crash exits 3. |
| 12 | Rotations under v1 and v2: decisions approved before and after a key joins are HELD, seals read under the scope that governed each; a pin of the replaced scope is NOT_COVERED (`WAITING`); after a v1 rotation drops a key, that key's earlier seal counts and a seal by it under the new scope is refused (`KEY`). |
| 13 | **The live chain** `refs/vars/heads/minds` at its tip: the prover finds a witness for exactly the decisions the lens settles, and both checkers hold each (34 of 46 at `57035e8`). CI requires the chain. |
| 14 | **Completeness.** `vars1witness --prove`, given only the store, accepts exactly the decisions whose `prove.py` term is HELD, on both histories before the failure and after it, and exactly the decisions the lens settles on the live chain (34 of 47 at `7c6899b`). Outside the fragment it does not accept what the lens settles: a withdrawn notice in the cone, a Stale INVALID verdict that the checker counts as withdrawing a key. |
| 15 | **INVALID verdicts withdraw their own keys only.** Against d's 2-of-3 policy: cy's INVALID verdict under its own verifier id withdraws cy's endorsement (a term naming it is REFUSED, `WITHDRAWN`; ana's and bo's are HELD); cy's under ana's id withdraws nothing (all three HELD); ana's and bo's, each under its own, leave one key (REFUSED, and no witness). `vars1witness --prove` accepts exactly where the lens settles. |

**Mutants.** `mutants.json` has one mutant per check: 51, all killed. Seven of them break the decode that `check.py
--lean` writes: kill edges dropped, INVALID verdicts not marked, verifier ids not written, an INVALID verdict's seals
not written, seals written without verifying, a seal's scope replaced, only the tip's scope written as one that
governed. Another writes the prover no seals (`m-prove-seals`). Of the withdrawal, each part has one: INVALID verdicts
not read, the verifier id or the key not compared, and the stand conditions taken as always met or never. The agreement of the two checkers kills them. `--mutants` runs the named tests unmutated first and
refuses a red baseline. It then runs each mutant without a bytecode cache and requires its test to fail on an
assertion.

**Measured once, on the maintainer's machine** (`measure.py`, not a target), on the L history after its failure:
- 17 of the 30 decisions are settled, and every one of the 17 has a HELD witness;
- a cone holds 5, 9 or 13 cells (minimum, median, maximum) of the store's 154;
- `check.py` takes a median 0.146 s per decision;
- the lens, cold, takes 0.265 s for every status at once.

The witness is small, but checking it is no faster: it reads the whole store. What it gains is independence (no
kernel, no vars1.py, no witnesses' word) and an explanation (which cells and which keys hold the decision).

## What it does not establish

- **The negative part.** `HELD` rests on the store at the tip being the admitted chain. `check.py` runs no gate.
- **The Ed25519 check.** It is this file's own, tested against the RFC vectors and vars1's signatures. It is not
  audited. Weak keys are refused by `[8]A = 0`.
- **The guards on a forged store's object layout** (cell length, HVEC order, POL1 bounds, UTF8) keep the checker
  total. They are not claims and no mutant burns them.
- **A proof of `check.py`.** Its soundness is tested, not proved. What is proved is the Lean checker, sound given
  `Pin` and complete on its fragment given `PinComplete`. The decode that both checkers read the store through (hashes, layout, Ed25519) is Python, tested and not
  proved.
- **The cost of a check.** The check is linear in the store, not in the term: the term is short, but its negative part
  reads everything.

## What would take it further (not done)

`ASSURANCE.md` carries what this spike establishes as four claims: `assurance.witness-held` and
`assurance.witness-one-reading` (tested), `assurance.witness-lean` (proved; roadmap G7) and
`assurance.witness-complete` (proved).

- **The decode in Lean.** `vars1witness` reads what `check.py` decoded. Reading the git tree, hashing (Book I's
  `SigmaEval/Sha256.lean`) and parsing cells in Lean would leave Ed25519 as the only part of the decode outside it.

- **The negative part as data.** A projection's kernel input already commits, by a witnessed digest, to every cell
  and seal at its tip. Read from there instead of a git store, the absences would rest on the projection's witnesses
  instead of on the reader's store. That is where `verify/minds_verify.py`'s attestation bundles are.
- **Edges that do not count.** INVALID verdicts that withdraw only their own keys are inside (test 15). A term could
  also carry, for each edge into the cone, a proof that it does not count: its source is invalidated, or the edge is
  unauthorized. That is stratified negation, and it would bring rebinding, withdrawn notices and Stale INVALID verdicts
  into the fragment. Both kinds of proof can be read from the store at the tip: §4.1 counts every seal on an edge's
  source under the governing scope, not only one commit's, so whether an edge latched under a scope of the chain is
  decided by the seals under it there are. The exception is the author clause of supersedes and retires, which reads
  the target's InitialEndorsers, fixed at its birth commit. Test 14's two cases outside the fragment are where it
  would start.
