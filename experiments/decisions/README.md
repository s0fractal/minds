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
