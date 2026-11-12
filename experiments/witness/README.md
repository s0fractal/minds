# Witness spike: a proof term for "this decision is in force"

A spike, not a feature: does Curry–Howard say anything literal about minds? It does, on a fragment.

The lens computes `Stale` as the least fixed point of a monotone operator (§4.2, proved in `proofs/Vars1/Pass2.lean`
and `Lfp.lean`). The positive part of the rules says two things:
- a cell stands while what it relies on stands;
- a decision is Settled while enough policy keys seal ATTESTED verdicts on it.

Where the store decides every edge that touches a decision's cone, being in force amounts to having a derivation:
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

Where Curry–Howard stops is the finding. The term proves what holds. That nothing kills the cone is a negative
statement, and it comes in two strata. That an edge into the cone does not count (its source is itself invalidated,
or the edge did not latch) the checkers prove, from the store, by stratified negation: Pass 1's `Effective` is the
unique kernel of the invalidates graph, which content addressing keeps acyclic. That there is no further edge, no
further INVALID verdict, no further seal, is not part of any proof: it is read over the whole store at the tip, a
closed-world assumption.

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
   - It is Effective: every cell of the store that invalidates it is a verdict that is not INVALID, or invalidates it
     by an edge that did not latch, or is itself Invalidated, by an Effective local killer whose edge latched (§4.2
     Pass 1, read newest first: the recursion climbs the edges, and content addressing bounds it).
   - It is not Retired: every cell that retires it is Invalidated, or its edge did not latch.
   - It is not Superseded: every cell that supersedes it does so by an edge that did not latch, or is Invalidated and
     not Superseded itself.
   - Every supersedes edge it has latched: a rebinding counts only when its quorum, or its target's author, sealed it.
   - An edge latched when, under a scope of the chain, the seals on its source by keys of that scope's roster meet the
     target's `Pol` (§4.1 latch 3: every seal under the governing scope counts, cumulatively). It did not latch when
     under none they do and the author clause cannot apply: the edge is an invalidates edge, the target's author may
     not evict it, or no key that seals the source seals the target. Otherwise the store does not decide it: the
     author clause reads `InitialEndorsers`, fixed at the target's birth commit, and the store at the tip does not
     say which seals were there (`NOT_COVERED`, `LATCH`).
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
     (`WITHDRAWN`). If one is Invalidated, or relies along `relies` on an Invalidated cell, it is not live and
     withdraws nothing. Otherwise (it is retired or superseded, or the store does not decide an edge on it) whether
     it withdraws is the lens's to say (`NOT_COVERED`, `INVALID_VERDICT`).
   - Each seal is in the store at the tip, under the only scope cell, and verifies. Its key is one of `EvalPol(d)`:
     the decision's own policy, else the scope's admission policy.
   - The distinct keys meet the threshold.

**What HELD does not say.** It is about Settled, not Grounded (§4.2). A decision can be HELD while a decision in its cone
is not Settled: the `stand` rule reads `Active` and not Stale, as the lens's Pass 2 does. To ask whether what it rests on
is settled too, read `grounded` in the lens, or `grounded_at_tip` of an attestation bundle. That a decision is not
Grounded has a certificate of its own, `check.py --unfounded`, and whether it is Grounded `vars1witness --ground`
decides (both below).

**What is checked from bytes.**
- Every object hashes to its name.
- Every signature verifies.
- The policy keys are fixed by the decision's id, which covers its policy atom's id, and by the scope cell the reader
  pins.
- The threshold is met.

**What is read over the store, and holds only if the store is complete.** The edges into the cone are all the edges
there are, and the seals on their sources (and on a retired or superseded target) are all the seals there are, so an
edge that did not latch by them did not latch; the INVALID verdicts that an endorsing key seals under its verdict's
verifier id are all there are; there is no second scope and no foreign cell. `check.py` runs no gate: that the tip is
the admitted chain is the reader's pin.

**One gate rule is relied on, not rechecked.** Evaluator keys lie within the admission roster (§3 step 3). So a seal
by an evaluator key is an admitted endorsement.

## The Lean checker

`proofs/Vars1/Witness.lean` holds a checker, `accepts`, and a theorem, `witness_sound`: if `accepts` holds for a
derivation, the model of §4.2 (`proofs/Vars1`) holds its decision `Settled` at the tip. The checker is compiled as
`vars1witness` (`lake build vars1witness`). It depends on the axioms `propext` and `Quot.sound` only.

A derivation is a list of lines. Each names its rule, its conclusion and its premises, and every premise is the
conclusion of an earlier line, as in open-ontologies' `OOCert.horn_certificate_sound`.

The rules come in two strata. The first reads edges and Pass 1, by stratified negation: each negative conclusion
is drawn from conclusions above it.

| rule | concludes | checks |
|---|---|---|
| `latch y x k` | the edge `y → x` of kind `k` latched (§4.1 latch 3) | `x` is an edge of `y` of kind `k`; `y` is not a scope or schema cell and `x` not an acceptance cell; under one scope cell that governed, the seals of the store on `y` by keys of its roster number `Pol(x)`'s threshold in keys of `Pol(x)` |
| `unlatched y x k` | it did not latch | `x` is not an acceptance cell and `y` not a scope cell; under no scope cell that governed do those seals meet `Pol(x)`; and `k` is invalidates, or `x`'s author may not evict it, or no key that seals `y` seals `x` |
| `dead x` | `x` is Invalidated | a local cell `y` that is not a verdict, or is an INVALID one, invalidates `x`; premises `eff y` and `latch y x invalidates` |
| `eff y` | `y` is Effective | `y` is a cell of the store; every cell that invalidates it is a verdict that is not INVALID, or a premise proves it `dead` or its edge `unlatched` |
| `unsup w` | `w` is not Superseded | every cell that supersedes it does so by an `unlatched` edge, or premises prove it `dead` and `unsup` |
| `down b` | `b` is not live (not Active, or Stale) | a premise proves it `dead`, or it is a cell of the store that relies on a cell a premise proves `down` |

The second reads Passes 2 and 3:

| rule | concludes | checks |
|---|---|---|
| `stand c` | `c` stands (`Active`, not `Stale`) | `c` is a local cell of the store; premises `eff c` and `unsup c`; every cell that retires it is `dead` or its edge `unlatched`; each supersedes edge of `c` is `latch`ed; each cell it relies on stands |
| `endorse w k` | `k` is among `w`'s endorsers | a seal of the store on the local cell `w`, under the scope cell, by `k`, a key of the admission roster |
| `settle d` | `d` is `Settled` | `d` is a contract or decision that requires no computation; `d` stands; each endorsement among its premises is on a standing ATTESTED verdict, with an empty witness slot, that judges and attests `d`, by a key of `d`'s evaluator policy that no INVALID verdict of the store withdraws (one on `d`, under the verdict's verifier id, that the key seals, or a foreign one) unless a premise proves it `down`; the distinct keys meet its threshold |

`check.py --lean` writes the line `vars1witness` reads: the store at the tip, decoded by `check.py`, and the term as
a derivation. For each cone cell, after the cells it relies on, the decoder writes the first-stratum lines its rules
(`Rules` in `check.py`, the same rules) derive for it, then its `stand` line; then an `endorse` line per endorsement,
`down` lines for the INVALID verdicts on the decision it proves not live, and one `settle` line. A conclusion its rules
do not derive is left out, so the line that needs it fails. It writes only the seals that verify: the term's, every one
on an INVALID verdict (from which the checker reads what each withdraws), every one on a cell with an invalidates,
retires or supersedes edge and on a cell such an edge retires or supersedes (from which it reads whether the edge
latched), and the policies those edges read. The Lean checker answers `ACCEPT` or `REJECT`.

The Lean checker asks whether an INVALID verdict is live only through `down`. A withdrawal the model would not make
only leaves a key uncounted, so soundness holds; where it matters, `check.py` answers `NOT_COVERED` and the Lean checker
`REJECT`.

**What the theorem assumes** (`Pin`, hypotheses, not axioms):
- **The decode is faithful.** On every cell of the store, the model agrees with what `check.py` decoded in the
  fields the checker reads, a verdict's verifier id among them. A cell is present exactly when the store holds it. A
  decoded policy meets its quorum with threshold many distinct keys.
- **The decode holds every seal of an INVALID verdict.** Each cumulative endorser of a local INVALID verdict has a
  seal of the store on it, under a scope that governed, by a key of its roster: the absence of a withdrawal is read
  from them, so it is part of the negative part.
- **Latches are read from the seals** (§4.1 latch 3):
  - an edge latches when, under a scope cell that governed, a quorum of the target's `Pol` seals its source by keys
    of that scope's roster (`latch`, latch soundness of the fold: §4.1 counts every seal under the governing scope,
    cumulatively, and the gate admits a seal on a local cell only under the scope governing it);
  - an edge latched only so, or by the author clause through a key that seals both its ends (`unlatch`): the decode
    holds every seal on an edge's source and on a retired or superseded cell, so a negative fact read from the
    data rests on the data being complete;
  - a policy meets its quorum only with threshold many distinct keys of it (`quorumConv`, the quorum converse).
  Hashes, the cell layout and the signatures are `check.py`'s. They are tested, not proved.
- **The store at the tip is the admitted chain.** This is the reader's pin, as for `check.py`, and it has these parts:
  - the Pass 1 equations hold;
  - an edge latches only from a present cell (`edge_present` proves this of the fold);
  - `Stale` satisfies the Pass 2 equation, and for an active local cell its converse, what a live cell relies on is
    live (`stale_pin` and `stale_complete` prove these of the model's `Stale`);
  - a verified seal under the scope cell, by a roster key, on a local cell is among that cell's cumulative
    endorsers (§4.1).

The proof never uses that `Stale` is the least fixed point, nor that Pass 1 has one solution. Each cell that stands is
proved not stale from the cells it relies on, and each `eff` and `dead` from the cells above it, all concluded by
earlier lines. So soundness holds for any solution of the equations.

The Lean checker checks one thing that `check.py` leaves to the gate: a counted verdict's witness slot is empty. On an
admitted chain it holds, so the two checkers do not differ there.

**Completeness** (`proofs/Vars1/WitnessComplete.lean`). `prove` builds a derivation from the store alone:
- a `latch` or `unlatched` line for every edge of the store that the store decides;
- for the decision and every verdict that counts for it (an ATTESTED verdict with an empty witness slot that judges
  and attests it, and that meets the stand conditions down its `relies`), the first-stratum lines and stand lines,
  each Pass 1 bit decided by recursion over a rank (`effB`, `deadB`, `unsupB`);
- `down` lines for the INVALID verdicts on the decision it proves not live;
- an endorse line for every key of the decision's evaluator policy with a seal on such a verdict, under a scope of the
  chain and by a key of that scope's roster, that every INVALID verdict that may withdraw it is proved `down` for;
- the settle line.

**The Pass 1 kernel is unique** (`pass1_kernel_unique` in `proofs/Vars1/Pass1.lean`). `Effective` is a kernel, in
Richardson's sense, of the digraph of authorized invalidates edges from Accepted killers. Cells are named by the hash
of their contents, so a cell can invalidate only one that does not name it: a rank exists that every edge climbs. On
such a store two solutions of the Pass 1 equations with the same `Accepted` agree on every cell, and the prover's
`effB` is one (`kernel_iff`): a cell's status is fixed by its attackers', and a notice that invalidates itself cannot
be written.

`witness_complete`: if the model holds the decision `Settled`, `accepts` takes that derivation. With
`witness_sound`, `accepts_iff_settled`: on the fragment the checker decides `Settled`. Axioms `propext` and
`Quot.sound` only.

The fragment (`Fragment`) is where every edge the derivation reads is decided by the store:
- the decision requires no computation, and every cell of the store is local (the model counts an edge only from an
  Accepted cell; a local cell is Accepted);
- every invalidates edge latched or not by quorum, which the store always decides for a source that is not a scope
  or schema cell and a target that is not an acceptance cell;
- every retires or supersedes edge into the decision's cone, or into a cell that supersedes one of it (upward), and
  every supersedes edge out of its cone, is decided too: an edge whose quorum fails while a key that seals its
  target seals its source is left out, since the author clause reads the target's `InitialEndorsers`;
- every INVALID verdict on it is live, or not live because it is Invalidated or relies along `relies` on an
  Invalidated cell (a retired or superseded INVALID verdict is left out).

Completeness needs the decode to be complete, where soundness needs it faithful (`PinComplete`):
- the store holds a seal for every cumulative endorser of a local cell, under a scope of the chain, by a key of its
  roster;
- the decision's evaluator policy is among the decoded ones.

It also needs ranks that bound the prover's depth (`Ranked`): `relies` descends one, invalidates and supersedes edges
climb another. Cells are named by the hash of their contents, so both exist.

`check.py --lean --prove` writes the store with every seal that verifies on a verdict of the decision, and the seals
and policies the edges read, and no derivation; `vars1witness --prove` runs `prove` on it, to a depth one more than the
store's cells, then `accepts`.

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
| `INVALID_VERDICT` | an INVALID verdict on the decision, under an endorsing verdict's verifier id and sealed by the endorsing key, neither meets the stand conditions nor is proved not live (Invalidated, or resting on an Invalidated cell): whether it is live, and so withdraws the key, the lens decides |
| `LATCH` | whether a cone cell stands the store does not decide: an edge into or out of what it rests on failed its quorum while a key that seals its target seals its source, so it latched exactly if that key is one of the target's initial endorsers, which the store at the tip does not show; or an edge reaches an acceptance cell, or leaves a scope or schema cell whose quorum is met |

Edges that do not count are inside (test 16): a notice that a second notice invalidates, and a third that
invalidates the second; INVALID verdicts that are Stale or Invalidated; an ATTESTED verdict's invalidates edge;
a retirement or supersession whose source is invalidated; a rebinding whose supersedes edge latched. So are those
that count: the term is `REFUSED` (`KILLED`). An INVALID verdict that withdraws one key, and leaves the others, is
inside (test 15).

What is left outside is the exact reason the negative part cannot all be read from the tip (test 08):
- the author clause: `InitialEndorsers(x)` is fixed at `x`'s birth commit, and a later seal on `x` by the same key
  looks the same at the tip, so an edge that fails its quorum while a key of `x` seals its source may or may not
  have latched (`LATCH`);
- an INVALID verdict that is retired or superseded is not live, but the checkers prove a verdict not live only
  through an Invalidated cell (`INVALID_VERDICT`);
- a rotation under v2 that drops a key without that key's seal, so it waits, and rules other than v1 and v2.

The live minds chain is inside: its v1 epochs, its rotation to v2 and its joins under both are rotations of the
fragment, it has no edge into a decision's cone, and test 13 holds every decision the lens settles there. So no
decision of the live chain uses what this adds.

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
| `KILLED` | a cone cell does not stand: an edge that counts invalidates, retires or supersedes it or what it relies on, or one of its supersedes edges did not latch |
| `WITHDRAWN` | an endorsement is withdrawn: an INVALID verdict on the decision under its verdict's verifier id, sealed by its key and meeting the stand conditions |
| `THRESHOLD` | there are too few distinct policy keys |

## Evidence

`test_witness.py` holds the tests; chains are admitted through the real gate. Every check in tests 03–09, 12, 13, 15 and 16 runs both
checkers on the same term and requires that `vars1witness` answers `ACCEPT` exactly when `check.py` answers `HELD`. It
does so wherever the Lean checker is built, and fails where `MINDS_REQUIRE_LEAN=1` and it is not, as in CI. `histories.py` generates the
histories: a project of three maintainers whose ground fails, the generator of the withdrawn G6 pilot
(`experiments/g6/RETIRED.md`).

| test | what it checks |
|---|---|
| 01 | RFC 8032 vectors and vars1's own signatures verify. A changed message, S + L, a key of small order and a non-canonical y do not. |
| 02 | `check.py` imports the standard library only, and its constants equal vars1's. |
| 03 | Before the failure, every decision of a history of each size (S and L) gets a witness that is HELD. |
| 04 | **Soundness, exhaustively on two histories after the failure.** A decision the lens settles gets a HELD witness; one it does not gets none. No term over any subset of a decision's verdicts, each with its whole cone, is HELD for a decision the lens does not settle. There are 222 such terms. Of the 93 for lost decisions, none is HELD: 86 are REFUSED (`KILLED`: the fallen ground is in the cone) and 7 REFUSED (`THRESHOLD`). Of the 129 for settled decisions, 59 are HELD, 58 REFUSED (`THRESHOLD`, one key) and 12 REFUSED (`KILLED`, a stale verdict in the subset). None is NOT_COVERED: the store decides every edge of these histories. |
| 05 | A lost decision cannot be passed off by leaving the fallen ground, or a stale verdict, out of the cone. |
| 06–07 | A wrong term is refused for its own reason, including verdicts that judge or attest another decision, a NOT_ASSESSED verdict, a custom-schema cell shaped like a verdict, and a key outside the evaluator policy. |
| 08 | Outside the fragment the answer is NOT_COVERED: a retires edge into the cone that fails its quorum while a key of its target seals its source (`LATCH`), both where it latched by the author clause and where that key sealed the target only after its birth, so it did not; a retired INVALID verdict that would withdraw a named key (`INVALID_VERDICT`); a rotation under v2 that waits; rules other than v1 and v2; two scope cells superseding one. |
| 09 | A store the gate never saw: a seal that does not verify, a seal under another scope, bytes that do not hash to their name, a missing object, an entry outside `cas/`, a decision requiring a computation, a foreign cell. |
| 10 | `check.py`, copied alone into an empty folder and run with `-I`, works. |
| 11 | A term that names its decision twice, the held one last, is refused, and so is one that names a seal twice. So are a truncated term, one that is not UTF-8, one that is not an object, and one holding `NaN` or an infinity, which Python's json reads and JSON does not have. A crash exits 3. |
| 12 | Rotations under v1 and v2: decisions approved before and after a key joins are HELD, seals read under the scope that governed each; a pin of the replaced scope is NOT_COVERED (`WAITING`); after a v1 rotation drops a key, that key's earlier seal counts and a seal by it under the new scope is refused (`KEY`). |
| 13 | **The live chain** `refs/vars/heads/minds` at its tip: the prover finds a witness for exactly the decisions the lens settles, and both checkers hold each (34 of 46 at `57035e8`). CI requires the chain. |
| 14 | **Completeness.** `vars1witness --prove`, given only the store, accepts exactly the decisions whose `prove.py` term is HELD, on both histories before the failure and after it, and exactly the decisions the lens settles on the live chain (34 of 47 at `7c6899b`). Outside the fragment it does not accept what the lens settles: a retires edge that did not latch, whose source a key of its target sealed after the target's birth; a retired INVALID verdict that the checker cannot prove not live. |
| 15 | **INVALID verdicts withdraw their own keys only.** Against d's 2-of-3 policy: cy's INVALID verdict under its own verifier id withdraws cy's endorsement (a term naming it is REFUSED, `WITHDRAWN`; ana's and bo's are HELD); cy's under ana's id withdraws nothing (all three HELD); ana's and bo's, each under its own, leave one key (REFUSED, and no witness). `vars1witness --prove` accepts exactly where the lens settles. |
| 16 | **Kill edges that do not count.** Notices: g invalidated by n is HELD once m invalidates n, and REFUSED (`KILLED`) once o invalidates m. INVALID verdicts: one that is Stale, or Invalidated, withdraws nothing (HELD), beside a live one, which does (`WITHDRAWN`). An ATTESTED verdict's invalidates edge counts for nothing. A retirement, a supersession, and a supersession through a superseder that is itself superseded, are `KILLED`; with the retirer or the superseder invalidated, HELD. A rebinding whose supersedes edge two keys latch is HELD; one that one key cannot latch is `KILLED` (the lens: not Active). A notice on a decision of tier owner latches by the admission policy, not the decision's own. In every case both checkers agree, and `vars1witness --prove` accepts exactly where the lens settles. |
| 17 | **A status is unchanged while nothing touches its frame** (`frame.py`). Through the gate, each kind of object that can change a status touches the frame by the rule that names it, and changes the status: a notice on the cone (`EDGE`) and a second notice that revives it; a notice whose edge one more seal latches (`SEAL`); a seal that completes a quorum; an INVALID verdict that names the decision by payload alone (`JUDGE`); an answer that attests a question; a notice on what only a verdict relies on; a retirement and a supersession; a rebinding that a late seal of the replaced cell's author latches; a rotation, which is in the frame of a decision that reads the scope's policy (`SCOPE`) and not of one with its own; a rotation that waits under v2 and governs sixteen commits later with no new cell (`WAITING`); and, for Grounded, a withdrawal from a decision the decision relies on, which leaves it Settled. Then over every pair of tips of these chains: a frame nothing touches keeps its status. |
| 18 | **Random extensions.** Sixty random commits on a base of two decisions (one relying on the other), a decision that reads the scope's policy and a question, under v1 and v2 and under an admission threshold of 1 and of 2: over every pair of tips and every evaluated cell, a frame nothing touches keeps Settled and Grounded (4,315 such frames; 420 touched ones changed). |
| 19 | **The live chain.** Every tip, every decision there, every later tip: a frame the commits between do not touch keeps its status (60,642 at `7c6899b`, none changed). The table below at `7c6899b`, byte for byte (`frame-minds-7c6899b.json`). `bundle_at` is `vars1.export_attestation` at the ref's tip. CI requires the chain. |
| 20 | The draft message's proof part holds every object its term names, each hashing to its name: the cone, the endorsing seals, the scope cells the seals are under with their rosters, the decision's policy. |

**Mutants.** `mutants.json` has one mutant per check: 78, all killed. Twelve are of `frame.py` (`"file": "frame.py"`), one per rule of
the frame: new edges not read, only invalidates edges read, the cells that attack the frame's attackers left out, the cells a
member supersedes left out, seals on an edge's source not watched, seals on a judge not watched, a cell that attests not
read, a verdict by payload not read, a rotation not read, a waiting rotation not read, the frame of Grounded taken as
Settled's, and what a judge relies on left out. Each is killed in test 17 on the status changing where the frame said nothing
touched it, not on a reason's name. Three rules have no mutant, because no chain here exercises them: a rotation to other
rules touches every frame (no rules change here gives a cell another status), a frame holding a foreign cell is
`NOT_COVERED`, and a verdict on a checkpoint a judge names is a judge (no decision here requires a computation). Of the other 66, ten break the decode that `check.py
--lean` writes: kill edges dropped, INVALID verdicts not marked, verifier ids not written, an INVALID verdict's seals
not written, seals written without verifying, a seal's scope replaced, only the tip's scope written as one that
governed, the seals on an edge's ends not written, a decision's tier not written, the policies an edge reads not
written. A derivation `check.py` writes cannot take the Lean checker past what `check.py` derived, so the last three, and
the dropped kill edges, are killed where the Lean checker rejects a line `check.py` derived or where it derives on its
own: test 16 compares `vars1witness --prove` with the lens. Another writes the prover no seals (`m-prove-seals`). Of the withdrawal, each part has one: INVALID verdicts
not read, the verifier id or the key not compared, and the stand conditions taken as always met or never. Of the
edges, each rule has one: a killed cone cell not refused, an undecided one not left out, the quorum one key short,
the author clause ignored, attackers ignored, a dead killer's `eff` not asked, a non-INVALID verdict counted as a
killer, a superseder's `dead` or `unsup` not asked, retirements ignored, a rebinding's latch not asked, `down`
through `relies` or through `dead` dropped, and the owner tier read as provisional. The agreement of the two checkers kills them. `--mutants` runs the named tests unmutated first and
refuses a red baseline. It then runs each mutant without a bytecode cache and requires its test to fail on an
assertion.

**Measured once, on the maintainer's machine** (`measure.py`, not a target), on the L history after its failure, with
the kill-edge rules (2026-11-07):
- 17 of the 30 decisions are settled, and every one of the 17 has a HELD witness;
- a cone holds 5, 9 or 13 cells (minimum, median, maximum) of the store's 154;
- `check.py` takes a median 0.074 s per decision;
- the lens, cold, takes 0.123 s for every status at once.

The witness is small, but checking it is no faster: it reads the whole store. What it gains is independence (no
kernel, no vars1.py, no witnesses' word) and an explanation (which cells and which keys hold the decision).

## What a reader must read (`frame.py`, `proofs/Vars1/Reader.lean`)

The witness is small and its check reads the whole store. This is why, and how small the message can be.

**The frame.** `Settled(d)` reads, at a tip:
- `d`, every cell that **judges** it (a cell that attests it, a verdict on it, a verdict on a checkpoint or cycle
  witness one of those names), the checkpoints they name, and everything those rely on: the cells whose standing it reads
  (`read`);
- every cell with an invalidates, retires or supersedes edge into that set, latched or not, and every cell a member
  supersedes, to the fixed point: the cells whose Pass 1 bits that standing reads (`guard`);
- the seals on the judges (their endorsers are counted) and on the sources of edges into `guard` (a seal can latch the
  edge);
- for a `d` that names no evaluator policy, the governing scope's admission policy: **the scope caveat**.

`Grounded(d)` reads the same of every contract, decision or question the set reaches, their judges included.
`settled_frame` and `grounded_frame` (Lean) say that between two tips that agree on these, the status is the same;
`settled_reads_tip_scope` that the caveat cannot be dropped. `frame.py` computes the frame, and `touches` says whether an
object of later commits touches it: a new cell with an edge into `guard` (`EDGE`), a new cell that judges (`JUDGE`), a
new seal on a watched cell (`SEAL`), and for a cell under the caveat a new scope cell (`SCOPE`) or a rotation that
waited at the earlier tip (`WAITING`); a rotation to other rules touches every frame (`RULES`), since other rules read
the history again. The frame theorems ask every cell of `guard` to be local.

**Renewal.** A witness for `d` at `T` is a witness at a later `T'` if no object of the commits between touches the
frame (tests 17–19). A commit names its parent, so that the reader has every commit between is checked from their ids;
nobody's word is needed for it. On the live chain, of the frames of every decision at every tip, 60,642 pairs with a
later tip are untouched and 2,600 touched, 2,334 of those by the one rotation from v1 to v2.

**The lower bound.** The frame cannot be closed from inside the store: nothing in a cell names what refers to it.
`unread_commit_decides`: add to any one commit a cell that invalidates `d` and the seals of a quorum of `Pol(d)`, and
`d` is Invalidated at the tip whatever the rest is. `reader_reads_commit`: so a reader that reads commits by position
reads every such commit before it answers correctly. A commit that only adds a seal can do it too, where it completes
the quorum of an edge whose source is already there (test 17, `SEAL`); that case is tested, not proved. Checking a
witness is therefore linear in the commits since `d`'s birth for any reader with no commitment to reverse edges, and
this is the exact sense in which the negative part of a witness has no address.

**No snapshot.** Under one set of rules the fold's state decides the fold of every continuation
(`fold_state_suffices`), and it is as large as the store: every present cell, every latch, every cell's
InitialEndorsers, and the continuation's commits carry the seals of their trees. Nothing in it can be dropped. An
Invalidated cell changes no `Effective` bit now (`dead_cell_silent`) and a status later: invalidate what invalidated
it, and it is Effective again (`revived`), so the store that kept it and the store that dropped it differ on a cell
both hold (`dropped_cell_distinguishes`; through the gate, test 16's notices and test 17's revival). So the question of
snapshots is closed for a reader who wants every later status: nothing compresses but the bytes no rule reads
(statements and other atoms the kernel's input already leaves out). A rules change reads each commit again under the
new rules, and that, not the statuses, is what the log is kept for.

**Measured** on `refs/vars/heads/minds` at `7c6899b` (2026-11-07), over the 34 decisions the lens settles of 47, in a
store of 651 cells, 684 seals and 83 commits (`python experiments/witness/frame.py . minds 7c6899b7cf8d1bc5bf68c4f53446251b3e90a69d`;
test 19 pins the output):

| | least | median | most |
|---|---|---|---|
| cells the status reads (`read`; the same as `guard`, and as the frame of Grounded: no edge enters any) | 2 | 3 | 39 |
| seals on watched cells | 1 | 2 | 3 |
| the frame's cells, seals and atoms, bytes | 1,179 | 1,833 | 15,890 |
| the same as JSON with hex, as bundles travel | 2,427 | 3,747 | 32,092 |
| proof part of the draft message, JSON | 6,787 | 7,368 | 36,233 |
| vouch (a projection's cell, atoms and witness seals), JSON | 2,036 | 2,367 | 2,367 |
| draft message, JSON | 9,509 | 10,090 | 38,624 |
| attestation bundle with its covering projection (spec §4.4), JSON | 310,324 | 311,855 | 338,629 |
| the objects of that bundle, bytes | 155,041 | 155,802 | 169,186 |
| of which the kernel's input | 150,784 | 150,784 | 163,532 |

Three of the 47 decisions name no evaluator policy and read the scope's; all three are Settled. The kernel's input at the
tip itself is 170,084 bytes. The proof part is larger than the frame because it carries the four scope cells the seals
are under, each with its roster, and the term.

**The message.** "`d` is in force at `T`" carries three things (`frame.py` `message`, format `minds.inforce.draft@0`, a
draft that no verifier reads; spec §4.4 is unchanged):

1. **The claim**: scope, `d`, the tip's commit id, the governing scope cell at the tip (the epoch) and the rules
   identity. The epoch fixes the evaluator policy of a decision under the caveat and ends the chain of scope cells the
   seals count under; the rules identity is what the frame theorems hold under.
2. **The proof**, which travels and is checked from bytes: a `minds.witness.held@1` term with the objects it names
   (the cone's cells, the endorsing seals, the scope cells with their rosters, the policy). It proves the positive part:
   the objects hash to their names, the seals verify under distinct keys of the policy the decision's id fixes, on
   ATTESTED verdicts that judge and attest it, and the cone is closed under `relies`. With the sources of the edges into
   the cone and their seals it would also prove that an edge that is there does not count (the stratified part, which
   both checkers derive from a store). Its size follows the cone and the threshold, not the store.
3. **The vouch**, which is someone's word: that the tip holds no further cell with an edge into the frame, no further
   cell that judges `d`, and no further seal on a watched cell. By the lower bound nothing short of reading every commit
   establishes it, so it is said by whoever did, under keys the reader pinned beforehand, and bound to the tip, the
   epoch, the rules identity, `d` and the frame (a digest of the ids `frame` lists), so that the word is about this
   frame's closed world and nothing else.

**Is a projection's seal that vouch?** It vouches for more and for less, and not in a form a small message can use.
- *More.* Its witnesses seal `(tip, rules, input, state)`, where `input` is the digest of the kernel's whole input: every
  cell and every verified seal at the tip. That fixes the closed world of every decision at once.
- *Not usable.* The digest is of the whole input as one string. It says that nothing else touches `d`'s frame only to a
  reader who holds the input and recomputes; no part of it can be opened. The attestation bundle therefore carries the
  whole input, 150,784 to 163,532 bytes, for every decision, and that is all the difference between 310 KB and 10 KB.
- *Less.* `state` covers the governing scope, the latches and the bits of Passes 1–2. It says nothing of Pass 3, so
  nothing of Settled or Grounded; nothing of commits after the tip; and its witness policy is its own, so the reader
  still pins keys.

A seal that vouches for exactly the closed-world part would be on the claim itself with the frame's digest: one seal per
decision and tip in place of one per tip, by a witness that has computed the lens there anyway. Renewal keeps that
cheap: the word is needed again only when an object touches the frame. This is not built. An index of reverse edges
is (`revindex.py`, below); it gives the closed world an address, not a proof.

**Not established here.** No verifier reads the draft message; the bytes are what such a message would weigh.
`frame.py` is tested against the lens, not proved; the Lean theorems take the standing of the frame's cells as a
hypothesis that `active_frame` and `stale_frame` discharge, and are not composed with the fold into one statement. The
reader bound is proved for the v1 fold (the kill itself for both); a reader with an index of reverse edges is outside
its model.

## An address for negative facts (`revindex.py`)

The lower bound has a hypothesis: the reader holds no commitment to what points at a cell. `revindex.py` builds one. At a
tip every cell, and every id a cell or seal points at, gets a leaf: the sorted ids of the cells that attest it, of the
verdicts on it, of the verdicts that name it as their checkpoint, of the cells with an invalidates, retires or
supersedes edge into it, and of the seals on it. The leaves, sorted by id, are hashed into one Merkle tree (RFC 9162:
`0x00` before a leaf, `0x01` before a node). At the tip of 2026-11-07 that is 651 leaves under root `5baad8aa…503e`.

A message for `d` then carries, in place of the vouch, the root and the leaves its frame reads (what judges each
evaluated cell, what names each checkpoint, what points an eviction edge into each cell of `guard`, the seals on each
watched cell), each with its path, the cells of `guard`, and every seal on a watched cell. `reader_frame` reads the
frame from that alone: it checks every path, takes every "what points at this" from a leaf, and answers `Incomplete`
when a leaf, cell or seal the reading needs is missing. It never reads a gap as "nothing".

**Test 21** holds it equal to `frame.py`'s `frame`, which reads the whole store, on:
- every decision of the live chain at the named tip, for Settled and Grounded: 94 frames;
- four chains with retires and invalidates edges;
- a store with a verdict that names a checkpoint (no chain here has one, so it is built without the gate).

**Test 22:** a leaf whose path does not reach the root is refused, and a missing part is `Incomplete`.

**What it weighs.** The message is the draft message of the section above with this part as its closed world, and with
the covering projection's cell and seals standing in for the signatures on a root carried the same way. It is set
against the attestation bundle a client receives today. Bytes are compact JSON with objects in hex; medians and maxima
are over the Settled decisions with a covering projection (test 21 pins the table, `revindex-minds-7c6899b.json`):

| Tip | Cells | Decisions | Closed part | Message | Bundle | Bundle ÷ message | Message max | Bundle max |
|---|---|---|---|---|---|---|---|---|
| 11 of 83 | 36 | 6 | 3,625 | 10,764 | 24,901 | 2.3× | 13,236 | 28,725 |
| 21 of 83 | 56 | 11 | 5,467 | 13,169 | 39,492 | 3.0× | 13,254 | 41,849 |
| 42 of 83 | 112 | 20 | 5,735 | 13,455 | 63,684 | 4.7× | 13,456 | 72,493 |
| 63 of 83 | 400 | 31 | 6,141 | 13,861 | 178,740 | 12.9× | 72,566 | 206,007 |
| 83 of 83 | 651 | 34 | 6,342 | 16,463 | 311,855 | 18.9× | 102,068 | 338,629 |

Over these tips:
- **The bundle grows with the store:** ×12.5 for ×18 cells. It carries the kernel's whole input, so its closed world is
  checkable.
- **The message grows with the frame and the log of the store:** ×1.5. Each path is about ⌈log₂ N⌉ hashes.
- **The largest messages** are the decisions whose `guard` holds 39 cells.

**What changes, and what does not.**
- **The root is still a claim.** That every leaf is the store's and that none is missing is the word of whoever signs
  the root, as the vouch was a word. Test 23 builds a root over a leaf that hides a verdict on `d`: its paths check,
  and the reader reads a frame without that verdict. Committing does not prove.
- **One root serves every decision and every reader at the tip.** That is one signature where the vouch needed one per
  decision, and two readers who hold one root read one answer.
- **A lie costs one object to refute.**
  - `refute` finds, against the store, the cell or seal a leaf leaves out, or an id it lists that does not point at its
    key.
  - `judge` accepts that proof by checking the leaf's path to the root and reading that one object.
  - A proof against one root does not transfer to another.
  - Test 23 refutes an omitted verdict, an omitted seal and a falsely listed attester, and refuses an accusation against
    an honest leaf.
- **The negative facts have an address.** Their weight no longer grows with the store. Whoever signs a root does not
  have to stand behind a separate word for each decision.
- **A refutation needs no store** (`portable`, `judge_portable`, test 24).
  - The proof carries the object it names, with the git objects that show it at the tip: the tip's commit, the trees
    `/`, `cas`, `cas/<kind>` and `cas/<kind>/<id[:2]>`, and the blob, each hashing to the name its parent gives it.
  - When the object is an edge, the proof also carries the edge list its field names.
  - A git tree lists every entry, so the same path proves an id absent.
  - A judge holding the signed root and the tip's commit id decides the proof alone.
  - Test 24 refutes four lies this way: an omitted verdict, an omitted seal, a falsely listed attester, and a listed id
    no cell has. A proof with one byte changed, under the parent tip, against the honest root, or without its edge list
    is refused.
  - Against the live tip, a refutation of one hidden verdict weighs 16,075 bytes of git objects (33,597 as JSON),
    and no store is read.
  - Git's object ids are SHA-1 here, checked with `hashlib`, without the collision detection git itself uses.

**Not done.**
- No format of spec §4.4 changes, and nobody signs a root on `refs/vars/heads/minds`.
- Nothing proves the module. `reader_frame` is tested against `frame.py`, and fifteen mutants burn the module. The Lean model of
  a reader with an index (`proofs/Vars1/Reader.lean`'s bound does not cover one) is not written.

## A frame read from below (`delta.py`, `proofs/Vars1/Delta.lean`)

`frame.py` answers from a decision: what its status reads, and whether later commits touch that. With many decisions
and a small commit, that is a frame per decision. `delta.py` asks the other way: from the objects a later tip adds,
which contracts, decisions and questions have a frame they touch? `Up` holds, for one tip, the inverse of each step
`frame` takes downward (who relies on a cell, which cells a judge judges, for which cells a checkpoint is named, which
cells an edge enters, which cells supersede a cell), and `dirty` walks up from each new object's touch points by
`touches`'s own rules (EDGE, JUDGE, SEAL, SCOPE, WAITING, RULES, NOT_COVERED).

`Delta.lean` proves the walk exact for a frame given by its steps: from a touch point, the inverse of each step in the
reverse order reaches `d` iff the touch point is in `d`'s frame, for Settled (`up_settled_iff`) and for Grounded, whose
frame first closes over the evaluated cells it reads (`up_grounded_iff`); so the decisions the walk does not reach are
exactly those with no touch point in their frame (`unreached_frame_untouched`). No axiom. That an untouched frame meets
`Reads`, so its status is kept, is `frame.py`'s link to `Reader.lean`, held by tests 17–19, not proved.

Test 25 holds `dirty` to `touches` on the random chains of test 18 (v1 and v2, an admission threshold of 1 and of 2),
test 26 on `refs/vars/heads/minds`: for every pair of tips, every evaluated cell and both frames, a cell is dirty
exactly when `touches` reports its frame touched. Thirteen mutants of `delta.py`, one per inverse step and per rule,
must fail test 25. On the random walks alone six survived: no walk files a verdict on a payload it does not attest,
a verdict naming a checkpoint, an edge into a cell a frame holds only because a cell it reads supersedes it, or a seal
on a custom-schema cell a decision relies on. `shapes_stores` builds those shapes as stores no gate admitted, one
object per later store, and test 25 reads them first: each of the six now fails at the store built for it. A mutant
that removed a loop's `pop` with its body hung test 25 rather than failing it; the runner now stops a test at five
times its baseline and counts the hang as a survivor.

On the live chain at fd7b2f9 (100 commits, 49 decisions at the tip), for each of the 98 commits made after the first
decision, for Settled and for Grounded alike:

| decisions a commit dirties | 0 | 1 | 3 | 38 |
|---|---|---|---|---|
| commits | 48 | 47 | 2 | 1 |

95 of 98 commits dirty at most one decision. The one that dirties every decision of its tip (38) is the rotation to
the v2 rules: other rules read the history again, so a rules change touches every frame. The two that dirty three are
rotations of the scope, read by the three decisions that name no evaluator policy (the scope caveat). Over the 99
commits, the walk takes 0.09 s against 0.96 s for a frame per decision and `touches` (5,444 frames), eleven times
less; at 49 decisions both are under a second, and the walk's cost does not grow with the number of decisions a
commit leaves alone. The stop rule (no saving for Grounded) did not fire; on this chain no decision rests on another, so a decision's
Grounded frame is its Settled frame, and the random chains of test 25 are where the two differ.

`revindex.py`'s committed index names who attests, whose payload, who names, who points an edge and who seals; not
who relies on a cell, which the walk also needs, so `Up` is built from the store in one pass.

## A certificate that a decision is not Grounded (`check.py --unfounded`, `WitnessGrounded.lean`)

To show a decision Grounded a derivation builds a support from below. To show it is not, one dead cell is not enough:
in `circular_support` (`Grounded.lean`) every cell stands and the decision is Settled, and nothing is Grounded, because
its only support runs in a circle. `WitnessGrounded.lean` proves the dual of Knaster–Tarski for Grounded, with no
`Classical.choice`: a cell is not Grounded iff some **unfounded set** holds it, a set none of whose members satisfies
Grounded's equation when only the cells outside the set are given (`not_grounded_iff_unfounded`); checked member by
member (`unfounded_of_each`).

A certificate (`minds.witness.unfounded@1`) names the decision and the set. `check.py --unfounded` answers
`UNFOUNDED` when every member has a reason: it is `down`; it does not `stand` (retired, superseded: `stand` answers
False, which no Lean rule concludes, so this reason rests on tests); it relies on a member; or it is a contract or
decision without a computation whose policy the keys counting through its verdicts outside the set cannot meet, read
from above (every policy key that seals an ATTESTED verdict outside the set that judges it and is not down, unless an
INVALID verdict under that verdict's verifier id, sealed by the key, stands). A member with none is `REFUSED`
(`FOUNDED`); one whose standing the fragment does not decide is `NOT_COVERED`. `prove.py`'s `prove_unfounded` names the
cells not Grounded that the decision's equation reaches.

Test 27, on one chain through the gate: the circle (d0 is HELD for Settled, and `[d0, w]` is UNFOUNDED: d0 by quorum,
w by relies), `settled_not_hereditary`'s case, a decision an edge kills (`down`), one whose only key an INVALID verdict
withdraws, one whose only verdict rests on a killed ground, one whose only verdict was retired (`not live`); a set
that leaves out what the equation needs is refused, and so is any set holding a Grounded decision. On the random chains
of test 18, at every tip, every decision without a computation the lens does not ground gets a certificate that is
UNFOUNDED (351) or NOT_COVERED (157: 101 whose standing the store does not decide, 56 under a rotation that may wait),
never REFUSED; no set holding one of the 8 decisions it grounds is UNFOUNDED. Test 28: on the live chain every decision
is Grounded, and no set holding one is UNFOUNDED. Nine mutants of the check.

The certificate is not in `vars1witness`'s binary format (the brief's stop rule): its Lean side is the theorem, its
check is `check.py`. The positive side is in the binary (next section).

## A derivation that a decision is Grounded (`vars1witness --ground`)

The Lean checker has a rule `ground d` (`Witness.lean`, `groundOK`): `d` stands, every cell it relies on is grounded
by an earlier line, and, if it is a contract or decision without a computation, the endorsements among its premises
meet its policy as `settle` reads them, each on a verdict that is grounded by an earlier line. A scope, a schema or a
question is outside the rule: the store does not show what authorizes the first two or which schema answers the third.
`witness_ground_sound`: if `acceptsGround` holds, the cell is Grounded in the model, given `Pin`.

The prover (`WitnessGrounded.lean`) runs Grounded's equation in rounds from below, as `grounded_iter` does on `Fin N`,
with the checker's own reading of each cell: round `R + 1` holds the candidates whose relies are in round `R` and
whose quorum, if they are evaluated, is met by the endorsements `pairs` names through verdicts in round `R`. Each
round's new cells get their `stand`, `down`, `endorse` and `ground` lines. The rounds are lists, not a recursion on
cells: a verdict may rely on the decision it judges, and a recursion would unfold that circle once per round (the
first version did, and took 15 s on a decision of the live chain). The candidates are the cells reached from the
decision down `relies` and to the cells whose payload a reached cell is, closed (or every cell, if the closure's
steps run out), that stand by `standsB`; what `pairs` names for each is tabled once.

`groundCheck_iff`: `vars1witness --ground` answers `ACCEPT` exactly when the model holds the decision Grounded, given
`Pin` and `PinComplete`, on a fragment (`GFragment`): every live cell the decision's Grounded reads (down `relies`
and to the verdicts of `W_max`, from live cells) is in the settle checker's fragment and is not a scope, a schema or a
question. Rounds only add cells, and round `N`, for `N` the candidates, holds every cell any round holds
(`groundSet_bound`); the binary stops at the first round that adds nothing. Axioms: `propext` and `Quot.sound`.

`check.py --lean --ground` writes the store with every seal that verifies on any verdict and the evaluator policy of
every contract and decision, since Grounded reads the quorums of everything the decision rests on.

Test 29: on test 27's chain `--ground` accepts exactly the decisions the lens grounds: not d0 (the circle; d0 is
Settled and `--prove` accepts it), not e1 (`settled_not_hereditary`), not a killed, withdrawn or retired one; but dg,
dh relying on dg, dp under its own policy of 2 of 3, and dq relying on dp. On two random chains (one per kernel, every
fourth tip) and test 14's histories it accepts no decision the lens does not ground (105 rejected), accepts 65 it
does, and misses one: an edge into its ground whose latch the store does not decide, which the settle checker misses
too (the test asserts that every miss is one the settle checker shares). Test 30: on the live chain at fd7b2f9 it
accepts all 49 decisions, each in 0.03–0.52 s (the line takes 0.37 s to write in Python). Two mutants of the line
(`m-ground-policies`: without the policies of the decisions it rests on; `m-ground-seals`: with only the decision's
own verdicts' seals).

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

`ASSURANCE.md` carries what this spike establishes as five claims: `assurance.witness-held` and
`assurance.witness-one-reading` (tested), `assurance.witness-lean` (proved; roadmap G7),
`assurance.witness-complete` and `assurance.witness-kernel` (proved); and what a reader must read as five more:
`assurance.reader-frame`, `assurance.reader-scope`, `assurance.reader-bound`, `assurance.reader-state` (proved) and
`assurance.reader-touches` (tested).

- **The decode in Lean.** `vars1witness` reads what `check.py` decoded. Reading the git tree, hashing (Book I's
  `SigmaEval/Sha256.lean`) and parsing cells in Lean would leave Ed25519 as the only part of the decode outside it.

- **The negative part as data.** A projection's kernel input already commits, by a witnessed digest, to every cell
  and seal at its tip. Read from there instead of a git store, the absences would rest on the projection's witnesses
  instead of on the reader's store. That is where `verify/minds_verify.py`'s attestation bundles are.
- **The author clause.** `InitialEndorsers(x)` is fixed at `x`'s birth commit, and the store at the tip does not say
  which of `x`'s seals were there. A term could name that commit: the checker would read the tree at it, find `x`
  new there, and take its seals under the scope that governed it. That would bring the edges left out as `LATCH`
  inside, at the cost of reading a second tree (test 08's two author chains, test 14's first case outside).
- **INVALID verdicts that are retired or superseded.** They are not live, but `down` proves a verdict not live only
  through an Invalidated cell. A positive `Retired` and `Superseded` conclusion (the duals of the stand checks) would
  bring them inside (test 08's retired INVALID verdict, test 14's second case outside).
