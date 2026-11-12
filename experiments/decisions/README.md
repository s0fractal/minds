# Fold-candidates: what each reading of an event would do (`fold.py`)

A model or a person reading an unstructured event (a message, a pull request, a bug report) can offer several readings
of what it is in the graph: a notice that invalidates a check, an INVALID verdict on a decision, a seal, nothing. A
Decision API answers with a probability per reading. Here the graph answers instead, for a whole batch at once
(`minds.decisions.candidates@1`), without moving the ref:

- `admissible`: whether the reading passes the gate, its seals supposed (`GitVarsRepo.what_if(assume=True)`), and if not,
  the gate's refusal;
- `flipped_settled`, `flipped_grounded`: the contracts, decisions and questions whose status it changes;
- `classes`: readings grouped by the vector of (Settled, Grounded) they leave on every such cell: two readings that act
  alike are one question, not two;
- `discriminating`: for two classes that act differently, the cells on which they part. That is what to ask a person or
  a verifier about, rather than the raw text.

    python3 experiments/decisions/fold.py REPO SCOPE CANDIDATES.json [--tip COMMIT] [--no-gate]

## Two steps

A reading is read first in memory, from below: `delta.dirty` (`experiments/witness/delta.py`, series II task 9) gives the
cells whose Grounded frame its objects touch. That is held to `touches` on every pair of tips (`test_witness.py` 25), and
a frame nothing touches keeps its status (tests 17–19). So a reading that dirties no cell changes nothing, and with
`--no-gate` the filter alone answers it; a reading that dirties a cell is then `unread`. With the gate (the default)
every reading goes through `what_if` for admissibility and the exact changes, and the tests hold every change the gate
finds to the filter's dirty set.

## Measured

Test 01, on one chain through the gate:

| reading | what it changes | class |
|---|---|---|
| A: bo attests d; B: bo seals ana's verdict on d | d Settled and Grounded | one |
| C: ana invalidates d's ground; D: a comment; E: bo seals an axiom nothing reads | no Settled or Grounded | one (E dirties no frame) |
| C2: ana invalidates cy's verdict on e; G: cy withdraws its own | e loses Settled and Grounded | one |
| F: a key off the roster seals | refused by the gate | its own |
| H: bo attests d and ana invalidates cy's verdict | d and e | its own; parts from A's class on e alone |

Test 02, on `refs/vars/heads/minds` at fd7b2f9e, 100 readings by roster keys (25 attestations of a decision, 25 seals on
a verdict, 25 notices invalidating a verdict or a decision, 25 comments): every non-empty reading dirties exactly one
decision, the filter reads all 100 in 7.5 ms (54 ms to build the tip's inverse steps once), and the gate takes 28 s
(0.37 s a reading). 82 readings change no status and fold into one class; 18 change one decision each; 15 classes in
all. Every change the gate found was in the dirty set.

So the filter is fast and exact about what can move, and on this chain it cannot spare the gate: a reading of an event
names a decision or a verdict, and then it touches that decision's frame. The stop rule of the brief (in memory over the
loaded tree, the gate only for a chosen class) is where the next saving lies: `minds_chain.py next` already reads a
verdict or a seal in memory (`NextTip.predict`); an edge needs the gate.

## What it does not establish

- That a reading the filter does not dirty changes nothing rests on `frame.py`'s link to the lens, held by tests 17–19 of
  `test_witness.py`, not proved; `delta.py`'s exactness for a frame given by its steps is `proofs/Vars1/Delta.lean`.
- The classes group readings by the statuses they leave, not by what they say: two readings in one class are one
  question for the graph and may still be two for a person.
- Nothing here chooses a reading, or calls a model: it reads vars1.py, the witness spike's `delta.py` and `frame.py`, the
  standard library, and no network.

Mutants: eight of `fold.py` in the root `mutants.json` (`m-fold-*`), killed by test 01 through `tools/run_mutants.py`.

# The decision profile lens: which tensions are worth a question (`profile.py`)

A graph that can say what to ask next and what a reading would change holds thousands of open points. A decision
profile (`minds.decisions.profile@1`) names what matters to its reader: goals (contracts, decisions or questions whose
Settled and Grounded matter), obligations (evaluated cells that must stay live), a budget of keys (`max_deficit`: a goal
more keys than this from Settled is not a question), a
minimum cut (`preferences.min_cut_threshold`) and the precedents already resolved.

    python3 experiments/decisions/profile.py REPO SCOPE PROFILE.json [--tip COMMIT] [--since COMMIT] [--candidates C.json]

`filter_tensions` reads each goal's frame only (the cells its Grounded reads, `frame.py`) and names four kinds:

| kind | when | evidence and trajectories |
|---|---|---|
| INCOMPLETENESS | a live goal short of its quorum; or Settled and not Grounded | the missing keys and every set of them that would close it (one set: a missing fact, will this key attest?; several: a missing criterion, which way?); or the cells it rests on that are not founded (`prove_unfounded`) |
| CONTRADICTION | a goal or obligation not live; a goal with a live ATTESTED and a live INVALID verdict | the cells of its frame that are not live; the two verdicts |
| FRAGILITY | a Grounded goal that fewer than `min_cut_threshold` withdrawals unsettle | its counted keys (its own quorum's margin; `GitVarsRepo.power` reads the cut over the whole frame) |
| UNREALIZED_POSSIBILITY | with `--since`, a goal whose deficit fell from more than one to one | the keys that would close it |

Each tension carries its blast radius (how many goals' frames hold it), a question, and a signature over its kind, goal,
evidence and the conditions it was judged under (`conditions`: the goal's policy, threshold and keys, and for FRAGILITY
the profile's minimum cut). `record_resolution` adds a precedent, and a tension whose signature a precedent records is
`suppressed`: a resolution holds only while its evidence and its conditions are unchanged. A goal more keys from
Settled than the budget is `over_budget`, not a question. The trajectories are counted (`math.comb`) and only the
eight listed are drawn, so the lens's cost does not grow with the number of ways.

**Silence.** `proofs/Vars1/Silence.lean`: a change confined to cells outside every goal's frame leaves each goal's
Settled and Grounded as they were (`silence_outside_reads`), and a cell whose keys a goal's quorum does not need cannot
move it while the goal stays live (`silence_by_quorum_slack`). So tensions outside the frames are not computed, and a
candidate reading (`fold.py`'s format) whose objects touch no goal's frame (`delta.dirty`) is listed `silent`; the rest
are `loud`, with the goals they touch.

Test 01 builds a goal for each kind and one for none, and holds the evidence, trajectories (one for a fact, three for a
criterion), blast radius (2 for a goal another goal relies on), budget and precedent. Test 02 (`test_absolute_silence`):
two Grounded goals with a key to spare beside a hundred cells that touch neither (unsettled decisions, verdicts that
disagree, quorums of one, killed cells): no tension, though a profile of the background names more than thirty; 22
background readings silent, the two on a goal loud; and the gate finds no silent reading moving a goal. Test 03, on the
live chain, holds the profile to the lens: under a minimum cut of one it names exactly the decisions not Settled and
Grounded, each an INCOMPLETENESS, and under two adds a FRAGILITY for exactly the Grounded ones at margin 0 (at fd7b2f9,
silence, then all 49; at 761e04c0, a release recorded and not yet witnessed, one INCOMPLETENESS, which the earlier
assertion of silence turned into a red CI run), in 0.1 s; of 20 readings attesting decisions outside a five-goal profile, those the filter calls silent move no goal
by the gate. Test 04: a resolution holds only under its conditions (a FRAGILITY resolved under a minimum cut of 2 is
asked again under 3, with the same evidence; an INCOMPLETENESS resolved under the scope's 1 of 3 is asked again after
the scope rotates to 2 of 3, the same three keys missing; neither re-asks the other). Test 05: a policy of 3 of 6 keys
has twenty ways to close, and the lens draws eight. These two answer an outside review (both points were red first,
on the assertion). Sixteen mutants of `profile.py` in the root `mutants.json` (`m-prof-*`), killed by tests 01, 02, 04
and 05.

What it does not establish: that a reading outside the frames changes nothing rests on `silence_outside_reads` and on
`delta.dirty`'s link to `touches` (tests, not proof); FRAGILITY reads a goal's own quorum, not the cut over its frame;
the four kinds are what the lens computes, not what a person will find worth asking; and the obligation reading is
liveness only.
