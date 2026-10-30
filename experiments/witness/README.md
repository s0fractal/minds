# Witness spike: a proof term for "this decision is in force"

A spike, not a feature: does Curry–Howard say anything literal about minds? It does, on a fragment.

The lens computes `Stale` as the least fixed point of a monotone operator (§4.2, proved in `proofs/Vars1/Pass2.lean`
and `Lfp.lean`). The positive part of the rules says two things:
- a cell stands while what it relies on stands;
- a decision is Settled while enough policy keys seal ATTESTED verdicts on it.

Where no edge touches a decision's cone, being in force amounts to having a derivation. This is argued below, not
proved:
- if the decision is in force, its cone and enough sealed verdicts exist (completeness);
- if they exist, it is in force (soundness: What HELD establishes, below).

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
retirement, no supersession, no INVALID verdict) is not part of any term: it is read over the whole store at the tip,
a closed-world assumption.

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

`HELD` means that the decision is Settled at the tip under the v1 rules, provided the store at the tip is that scope's
admitted chain. The argument below follows §4.2. For `check.py` it is prose, which test 04 checks; for the Lean
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
   - No INVALID verdict judges the decision, so no verifier is excluded.
   - Each seal is in the store at the tip, under the only scope cell, and verifies. Its key is one of `EvalPol(d)`:
     the decision's own policy, else the scope's admission policy.
   - The distinct keys meet the threshold.

**What is checked from bytes.**
- Every object hashes to its name.
- Every signature verifies.
- The policy keys are fixed by the decision's id, which covers its policy atom's id, and by the scope cell the reader
  pins.
- The threshold is met.

**What is read over the store, and holds only if the store is complete.** There is no kill edge, no INVALID verdict,
no second scope and no foreign cell. `check.py` runs no gate: that the tip is the admitted chain is the reader's pin.

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
| `settle d` | `d` is `Settled` | `d` is a contract or decision that requires no computation and no INVALID verdict of the store judges; `d` stands; each endorsement among its premises is on a standing ATTESTED verdict, with an empty witness slot, that judges and attests `d`, by a key of `d`'s evaluator policy; the distinct keys meet its threshold |

`check.py --lean` writes the line `vars1witness` reads: the store at the tip, decoded by `check.py`, and the term as
a derivation. The decoder writes a `stand` line per cone cell, after the cells it relies on, an `endorse` line per
endorsement and one `settle` line. It writes only the seals that verify. The Lean checker answers `ACCEPT` or `REJECT`.

**What the theorem assumes** (`Pin`, hypotheses, not axioms):
- **The decode is faithful.** On every cell of the store, the model agrees with what `check.py` decoded in the
  fields the checker reads. A cell is present exactly when the store holds it. A decoded policy meets its quorum with
  threshold many distinct keys.
  Hashes, the cell layout and the signatures are `check.py`'s. They are tested, not proved.
- **The store at the tip is the admitted chain.** This is the reader's pin, as for `check.py`, and it has these parts:
  - the Pass 1 equations hold;
  - an edge latches only from a present cell (`edge_present` proves this of the fold);
  - `Stale` satisfies the Pass 2 equation (`stale_pin` proves this of the model's `Stale`);
  - a verified seal under the scope cell, by a roster key, on a local cell is among that cell's cumulative
    endorsers (§4.1).

The proof never uses that `Stale` is the least fixed point. Each cell that stands is proved not stale from the cells
it relies on, which earlier lines conclude. So soundness holds for any solution of the Pass 2 equation.

The Lean checker checks two things that `check.py` leaves to the gate: a counted verdict's witness slot is empty, and
an endorsing key is in the admission roster. On an admitted chain both hold, so the two checkers do not differ there.


Outside the fragment the answer is `NOT_COVERED` and never `HELD`: there, the lens decides.

| code | when |
|---|---|
| `SCOPES` | the store has a second scope cell (a rotation, or a foreign scope) |
| `RULES` | the scope names rules other than v1 |
| `FOREIGN` | the store holds a cell of another origin |
| `COMPUTATION` | the decision requires a computation, which replay decides |
| `INVALID_VERDICT` | an INVALID verdict judges the decision |
| `KILL_EDGE` | a cone cell is invalidated, retired or superseded by any cell, or supersedes one |

The fragment is small, and the reason is the finding again. Test 08 shows decisions that the lens settles and the
checker leaves `NOT_COVERED`:
- a ground whose notice was itself invalidated;
- an INVALID verdict from another verifier;
- a rotation;
- the v2 rules.

To prove that an edge *does not count*, a term would need a proof that its source is itself invalidated, or that it
is unauthorized: negation in strata, not a Horn derivation. A decision rebound by `supersedes`, which real chains do,
is outside too. So is the live minds chain: it rotated to v2.

`REFUSED` means the term is wrong. Its codes:

| code | the term is wrong because |
|---|---|
| `FORMAT` | it is not in the term format |
| `TIP` | the tip is not a full commit id that names itself as a commit |
| `STORE` | an entry is not a store object, or an object does not hash to its name |
| `SCOPE` | the store's scope is not the term's, or not the pinned one |
| `DECISION` | the decision is not a contract or decision cell |
| `CONE_MISSING` | the cone names a cell the store does not hold |
| `CONE_OPEN` | the cone is not closed under `relies`, or lacks the decision or an endorsing verdict |
| `VERDICT` | an endorsement is not an ATTESTED verdict on the decision |
| `SEAL` | a seal is not on its verdict, is under another scope, or does not verify |
| `KEY` | a seal's key is not in the evaluator policy |
| `THRESHOLD` | there are too few distinct policy keys |

## Evidence

`test_witness.py` holds the tests; chains are admitted through the real gate. Every check in tests 03–09 runs both
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
| 08 | Outside the fragment the answer is NOT_COVERED. A decision left not Active by an unauthorized supersedes edge is not HELD. |
| 09 | A store the gate never saw: a seal that does not verify, a seal under another scope, bytes that do not hash to their name, a missing object, an entry outside `cas/`, a decision requiring a computation, a foreign cell. |
| 10 | `check.py`, copied alone into an empty folder and run with `-I`, works. |
| 11 | A term that names its decision twice, the held one last, is refused, and so is one that names a seal twice. So are a truncated term, one that is not UTF-8, one that is not an object, and one holding `NaN` or an infinity, which Python's json reads and JSON does not have. A crash exits 3. |

**Mutants.** `mutants.json` has one mutant per check: 40, all killed. Four of them break the decode that `check.py
--lean` writes: kill edges dropped, INVALID verdicts not marked, seals written without verifying, a seal's scope
replaced. The agreement of the two checkers kills them. `--mutants` runs the named tests unmutated first and
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
- **A proof of `check.py`.** Its soundness is tested, not proved. What is proved is the Lean checker, and only given
  `Pin`. The decode that both checkers read the store through (hashes, layout, Ed25519) is Python, tested and not
  proved.
- **The cost of a check.** The check is linear in the store, not in the term: the term is short, but its negative part
  reads everything.

## What would take it further (not done)

`ASSURANCE.md` carries what this spike establishes as three claims: `assurance.witness-held` and
`assurance.witness-one-reading` (tested), and `assurance.witness-lean` (proved; roadmap G7).

- **The decode in Lean.** `vars1witness` reads what `check.py` decoded. Reading the git tree, hashing (Book I's
  `SigmaEval/Sha256.lean`) and parsing cells in Lean would leave Ed25519 as the only part of the decode outside it.

- **The negative part as data.** A projection's kernel input already commits, by a witnessed digest, to every cell
  and seal at its tip. Read from there instead of a git store, the absences would rest on the projection's witnesses
  instead of on the reader's store. That is where `verify/minds_verify.py`'s attestation bundles are.
- **Edges that do not count.** A term could carry, for each edge into the cone, a proof that it does not count: its
  source is invalidated, or the edge is unauthorized. That is stratified negation, and it would bring rebinding and
  withdrawn notices into the fragment.
