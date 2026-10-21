# Classes of rules change

Design note for VARS-1-SPEC.md §4.3 ("Changing the rules", "Results", "Evidence"). The normative text is the spec;
this note gives the reasons, the alternatives not taken and what is still open. Status: implemented on the host
(`vars1.py`, `meter.py`, `tools/minds_chain.py`), tested (`test_vars1.py` 62–70, mutants `m-amend-*`). Nothing is
active on `refs/vars/heads/minds`: that chain stays on v1 until its members decide otherwise.

## The problem

Until now a rules change was admitted only as a **semantic correction**: (a) the new rules give every status the old
ones give over the chain so far, (b) on a counterexample chain a named status bit is right under the new rules and
wrong under the old, (c) no latch is lost. A Codex state review confirmed in code what this cannot carry:

- (b) needs a status bit that differs. A change whose point is that the old rules give **no** answer (they run
  unbounded, or trap) has no bit to name.
- Either rules refusing either log refuses the decision, so the new rules can never *refuse* the counterexample.
- A change that keeps every output and changes the bytes (a faster build, another compiler) has no counterexample.
- The counterexample is named by commit id, but nothing makes that commit reachable: a fresh clone can know the id
  and not have the history.

The first real defect waiting on this is in ASSURANCE.md: the kernel bounds every count of its input by the input's
length except the commit count `C`, and the fold visits every commit, so an 8 KB input claiming 84 M commits runs for
minutes. Bounding `C` changes `lens.wasm`, so it is a rules change, and its evidence is a refusal where the old rules
run unbounded.

## Results are not all statuses

Running rules on an input gives one of four results, and they mean different things:

| Result | Meaning | Where it can appear |
|---|---|---|
| output | statuses, latches, governing scope | everywhere |
| refusal `E<code>` | the rules refuse the log: malformed, a fold refusal, or a **resource refusal** the rules declare (v1b: E-7) | everywhere |
| exhausted | the budget of steps ran out first | only in a metered run (a rules change's evidence) |
| fault | the module trapped: a defect, never a verdict | only in a metered run; elsewhere a host fault |

Exhaustion is a fact about the budget, not about the input, so it is never a status and never `INVALID`. It is
local to the run that measured it.

**Steps, not time.** A budget counts steps: entries into a function body or a loop body (every iteration enters it
again). `meter.py` rewrites a rules module so that it counts its own steps (two appended exported globals; stack-neutral
code at each function and loop start; every other byte copied) and `kernel/run_metered.mjs` runs it. The count is a
property of the module's code and the input, so two hosts on different engines or machines count the same, and the
gate's verdict on "the old rules exhaust B steps" replays anywhere. A wall-clock timeout would make admission depend on
the machine. The rewriter decodes the instruction set the rules modules use and refuses any other opcode rather than
guess an immediate's length; test 62 checks that metering changes no result on real v1, v1b and v2 inputs.

## Four classes

Each class has its own decision schema, so a decision says what it claims and the gate knows which evidence to replay.
The meta-rule, *what each class needs*, is host code and spec text, outside the graph: no cell can change it, and a
change to it is a change of this repository reviewed like any other (Kimi's germline/soma point, kept).

| Class | Schema | Over the chain so far | Counterexample | Old rules on it | New rules on it |
|---|---|---|---|---|---|
| semantic correction | `<scope>/rules-change/schema` (unchanged) | same governing scope and status bytes; latches kept | a chain the gate admits (scope + canonical commit id) | the named bit is wrong | the named bit is right; latches kept |
| resource hardening | `<scope>/rules-change/hardening/schema` | same output, byte for byte | an input (KIN1 atom), a budget | exhaust the budget or trap | refuse with a **resource** code of theirs, within the budget |
| validation tightening | `<scope>/rules-change/tightening/schema` | same output, byte for byte | an input (KIN1 atom), a budget | an output | refuse with a **non-resource** code, within the budget |
| implementation-equivalent | `<scope>/rules-change/equivalent/schema` | same output, byte for byte | none | — | — |

Common to all: exactly one decision with the rotation, naming the governing rules and the new ones, `basis` = the
rotation's parent, sealed by the governing admission quorum.

Why a hardening and a tightening take a raw input and not a chain: the defect is in the rules as a component, and the
gate's own chains cannot reach it cheaply (the commit-count input needs ~3.6 K empty commits per 3.6 KB of input to
appear in a real chain, and 84 M to reproduce the fuzzer's case). Both rules must read the same input encoding (the
host's registry says which), or one input cannot mean the same thing to both.

Why byte-for-byte over the chain so far, not statuses only: these classes claim to change nothing a reader of this
chain sees. Equality of the whole output (statuses, Authorized bytes, edge latches, governing scope) is the strongest
check the gate can make, and costs nothing more.

**Resource codes are declared, not inferred.** The host's registry (`vars1.RULES`) records, for each rules it
implements, its input encoding and its resource refusals. A hardening's code must be one of them, a tightening's must
not. This keeps "the new rules refuse for size" apart from "the new rules refuse for meaning", which a reader of the
decision needs to know.

## (d) Earlier changes stay decided

A class check compares two rule sets on two logs. Alone it would admit undoing an earlier change: after v1 → v1b, an
"equivalent" change back to v1 passes (the outputs over the chain are equal), and the commit-count defect returns. So
every rules change must keep every earlier one: on each earlier decision of the chain, the new rules give the result
that decision established for the rules it introduced.

- a correction: its named status bit of its cell (found by id, since encodings differ in order) is still `right` on its
  counterexample;
- a hardening or a tightening: its input is still refused with its code within its budget.

The chain's past rules changes become its regression corpus: the protocol changes under evidence, and evidence once
admitted constrains every later change. Consequences, stated rather than hidden:

- After v1 → v1b, a later v1b → v2 is refused twice over: v2 cannot read the hardening's v1-encoded input, and v2
  reads v1b-born cells by type (below). Activating v1b first closes the road to v2 until a v2 that knows v1b, with the
  commit bound and a way to carry the input into v2's encoding, exists. The order matters, and it is the members'
  choice.
- (d) re-runs every earlier counterexample at every rules change; the cost grows with the number of changes, not with
  the chain.

A rotation from v2 to rules that read references as v1 does is refused by the host: v2's kernel refuses only v1 itself
(E-25), and v1b reads every value as a reference, which cannot read a v2 epoch. The other way is refused too: the v2
kernel reads a cell as v1 does only if it was born under `H_LENS_KERNEL` itself, so a v1b-born cell would lose its
v1 references after a rotation to v2 (Codex review r1 F1: an accepted cell's digest stopped carrying acceptance, with
host and kernel agreeing, so the differential check could not see it). A v2 that knows v1b would need a new v2 build.

## Evidence that travels

- **Counterexample chains.** The gate writes `refs/vars/evidence/<scope>/<decision id>/<commit>` for the
  counterexample commit and, transitively, for every counterexample the corrections on its chain name (replaying the
  counterexample replays those corrections; Codex review r1 found the one-level version let a nested one be gc'd), in
  the same `update-ref --stdin` transaction that moves the scope's ref. Every node that admits the rotation
  holds the evidence reachably; `git fetch origin '+refs/vars/*:refs/vars/*'` (CI's fetch) carries it.
- **Inputs** are KIN1 atoms of the rotation commit, and every rules module is an atom of the chain: a clone of the
  scope's ref alone replays a hardening.
- **Missing is not refuted.** A replay that lacks a commit a decision names, or part of its history (an absent object,
  a shallow boundary), raises `EvidenceMissing`, a distinct result, never a refusal of the decision.
- `tools/minds_chain.py evidence` prints the manifest: per decision its rotation commit, class, rules (and whether the
  chain carries them), basis, and its counterexample ref or input atom, with a `package` digest over all items.
  `replay-changes` replays each change with a fresh gate and reports `REPLAYED`, `EVIDENCE MISSING` or `REFUSED`.
- Test 69: a fresh clone that fetched only `refs/vars/heads/core` and `refs/vars/evidence/*` replays the change after
  the author's helper ref was deleted and gc'd; with the evidence ref deleted and gc'd, or fetched shallow, or with one
  object of the counterexample's history removed, it reports missing evidence.

Not covered: Radicle replicates `refs/vars/heads/<scope>` (README, §3), not `refs/vars/evidence/*`. A Radicle peer
holds the chain without a correction's counterexample until that mapping is extended.

## Shadow replay before a rotation (release-time)

The gate compares the rules at one tip. Statuses at earlier tips can differ even when the latest agrees, and that is
what a reader of an old projection relies on. `tools/minds_chain.py shadow RULES` runs, at every historical tip of the
chain, the rules of that tip's epoch and the new rules, and lists every difference as `{commit, cell, bit, old, new}`:
a status bit, `authorized` (a cell's latch or an edge's, `cell` = `<w>><v>:<kind>`), `governing`, or `result` (output
versus a refusal). `change-rules` records a rotation only with a manifest equal to that replay now, on the tip it
replayed (a writer in between makes the rotation refused, Codex review r2), with a decision named by that tip; a hardening or an
equivalent change must have none, a correction or a tightening is recorded with differences only when the operator
passes the manifest's digest (`--accept`). The decision's text names the manifest's digest.

This is a release condition, not a gate rule: the gate's cost would grow with the square of the history, and the gate
already replays what each class needs. A node can always recompute the manifest from the chain.

## The first amendment: v1b

`kernel/` built with `--features commit-bound` adds one check before anything else is read:
`commits > input.len()` → E-7. The default build is unchanged, byte for byte (`H_LENS_KERNEL` still `874e714d…`);
`H_LENS_KERNEL_V1B = 2a2e440a…`. CI and every release rebuild both.

- On the fuzzer's input (its artifact was not kept; test 62 rebuilds it: a real v1 input, C set to 84,000,000), v1
  exhausts 10^7 steps and v1b refuses at once with E-7.
- On every chain whose commit count does not exceed its input's length, v1b's output is v1's, byte for byte.
- The gate admits a commit that adds nothing, so a chain *can* reach C > input length: about 3.6 K empty commits on a
  bare genesis (test 63, built with `git fast-import`). v1 folds such a chain; v1b refuses it (E-7, with the host's
  twin agreeing), and under v1b the gate refuses the empty commit that would cross the bound. A commit that adds a
  cell adds more than 160 bytes of input, so a scope under v1b can always continue with content. This is a liveness
  property of degenerate chains, and the price of the bound.
- With v1b, the kernel's time is O(L·(N+S)) for an input of L bytes, N cells and S seals: quadratic in L, no longer
  unbounded.
- The offline verifier (`verify/minds_verify.py`) interprets only v1; a v1b projection is reported unsupported, as a
  v2 one is.

To activate it on `refs/vars/heads/minds` (the members' decision, not done here):

```
.venv/bin/python tools/minds_chain.py shadow 2a2e440a548b73adbb3072c23e21ee8d9d7bd7867fa7bc3e38150c477f1b11cd --out shadow.json
.venv/bin/python tools/minds_chain.py change-rules hardening 2a2e440a548b73adbb3072c23e21ee8d9d7bd7867fa7bc3e38150c477f1b11cd \
    --manifest shadow.json --input fuzz.kin --budget 10000000 --refusal 7
```

where `fuzz.kin` is the counterexample input (test 62's construction). Remember (d): after it, v2 needs a v2 with the
same bound.

## Inputs weighed

Codex state review (`.drafts/MINDS-STATE-CRITIQUE-STRATEGY-2026-10-21.md`), taken: the four classes (§4.1), distinct
results for refusal, exhaustion and status change, no automatic activation of arbitrary wasm (the host still executes
only the rules in its registry); shadow replay of every tip with a manifest (§4.2), Authorized and edge latches checked
separately; evidence manifest, fresh-clone test with refs deleted and gc, missing evidence distinct from refutation
(§4.5). Not taken: quarantine (§4.2) — it needs its own policy with start, objection and end rules, and an empty commit
gives no time for review; a compatibility manifest (§4.3) — `H_LENS_KERNEL` still does not identify the gate (this
branch changes the host's admission again without changing `H_LENS_KERNEL`); a release names the host by its `main`
commit.

Kimi's proposal (`minds-proposals/AMENDMENT-PROTOCOL-KIMI-2026-10-21.md`), taken: meta-rule outside the graph;
shadow equivalence on every commit (as a release condition, with an explicit manifest instead of "the counterexample's
class"); the commit-count bound as the first exercise; a per-rules encoder registry. Not taken: suites and mutants as
a gate rule (the gate cannot replay them; they stay release checks); a witnessed projection under the new rules before
activation (a projection names the rules of its tip's epoch, §3 step 6); a complexity budget as a gate rule — the step
budget here is evidence about one input, not a bound on the rules.

## Open

- Equivalence on inputs other than the chain so far and the earlier counterexamples: not established (two logs and a
  corpus, not all inputs). An "implementation-equivalent" change is a claim of its quorum beyond that.
- The step rewriter is one implementation; a second, independent one would make the count a checked agreement rather
  than a definition.
- The kernel fuzzer builds without `commit-bound` and still skips C > 4096; a v1b fuzz target is not set up.
- A hardening's input cannot yet move between encodings (v1 → v2), which blocks v1b → v2 under (d).
- Radicle does not replicate `refs/vars/evidence/*`.
- `evidence_closure` re-walks nested counterexample chains at every level that checks them: the work across a nesting
  of depth d grows about as d² (Codex review r2 measured 1, 6 and 28 entries at depths 2, 4 and 8). Real chains nest
  rarely; a memo per (scope, commit) would make it linear.
- The live chain is untouched.
