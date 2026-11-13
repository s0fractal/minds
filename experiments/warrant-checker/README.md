# A warrant checker as a minds rules module (experiment 6a): measured, not activated

Plan: `.drafts/NEW-INTERNET-ANALYSIS-AND-PLAN-2026-11-12.md`, stage 6, step 6a.

Today a warrant checker is named by "the digest of a Python import closure plus the environment's versions". That is
honest, but a stranger cannot run it safely. minds has the general form for that:
- a wasm module named by its hash;
- an input named by its hash;
- a budget of steps (`meter.py`);
- a result of one of four kinds (output, refusal, exhausted, fault), the same on every host.

6a asks whether that form carries a real warrant checker before anyone thinks about 6b (`assess` as a module).

Nothing here is active. This experiment does not change:
- the chain;
- `VARS-1-SPEC.md` or `AMENDMENTS.md`;
- `vars1.RULES`;
- the warrant repository.

## Pre-registered

Record `5c724596` (goal@1 `E6A`, open, no guard) is in `.warrant/records.jsonl`. It was filed in this branch's first
commit, fc3cc5cc, and pushed before anything was built or run. It fixes:
- what is measured;
- the three checks;
- the plan's stop rule for 6b.

Each measure ran once, as defined there.

## What it is

`src/lib.rs` is warrant/engine.py's `_schema_problem` and `_body_problem` at warrant f7e3637b, with what they call:
- `records.type_ok`, `guard_problem`, `is_list`, `body_refs`;
- `shapes.hex64`, `actor_problem`;
- `engine.quote`, `_weaker`.

It is written again as no_std Rust 1.100.0. The only dependency is `unicode-normalization` 0.1.25, for NFC; its tables
are Unicode 17.0.0, as Python 3.15's are.

The ABI is the rules modules': `memory`, `reset`, `alloc`, `run`, no imports.

**Input.** The canonical JSON (warrant's jcs) of one of:
- `{"schema": B}`;
- `{"record": R, "schema": S}`.

**Output.** `{"code", "reason", "verdict"}`:
- `code` names the engine's return statement that was taken: `counted` / `not-counted`, or `members`, `types`, `refs`,
  `valid-not-entity`, `state`, `guard`, `valid`;
- `reason` is the engine's text byte for byte.

**Refusals.**
- -1: not canonical.
- -2: neither object.
- -3: a pair the engine never asks about.

`checker.wasm` (SHA-256 `0e5a9f36…`, 154 713 bytes) and `checker-fault-variant.wasm` are committed. Test 137 rebuilds
both from `src/` to the same bytes.

## Held to warrant's own Python, by vectors

`vectors.py export --warrant DIR` imports warrant from a checkout at the pin and asks warrant's own functions:
- `jcs.loads`;
- the precondition, written in records/shapes predicates;
- `engine._schema_problem` / `_body_problem`.

The code is the return statement the call took, found with `sys.settrace`, so the harness restates no branch of the
engine.

The 3615 vectors, in `vectors.json.gz`:

| source | what | vectors |
|---|---|---|
| `live` | every schema and every body the engine checks in warrant's store at f7e3637b (3070 records) | 1826 |
| `live-minds` | the same for this repository's store | 93 |
| `mutation` | those records changed one way at a time: an extra member, each wrong type, each missing required member, an unknown state, each guard weaker or stronger than the schema's, a reference outside refs, another kind, pairs the engine never asks about; each schema without each member, with bad names, types, states, closed, successors and pins | 1207 |
| `edge` | Python's `==` in a guard's match (True == 1 at any depth, both directions); code point order against UTF-16 order; every Cc character and every Zs/Zl/Zp character at either end of an actor id; NFC and its Unicode-16 compositions; `?` and `??` types; attests and challenges and their target | 417 |
| `jcs` | bytes `jcs.loads` refuses or reads: white space, BOM, member order, repeated members, floats, `-0`, ±2^53, every non-canonical escape, invalid UTF-8, nesting at 256/257 | 72 |

**Result: 0 differences.** The module answers every vector as warrant's Python 3.15.2 does.

**Mutants.** 49 are declared in `mutants.json` (`m-wc-*`, run by `tools/run_mutants.py`, which now builds this crate as
it builds the kernels):
- 42 are in `src/lib.rs`, one per branch: the reader, Python equality, the shapes, the schema check, the body check,
  `_weaker`, the reasons' text, the precondition;
- 7 are in the harness.

All 49 are killed. The first full run surfaced two gaps in the vectors and tests, and both were fixed:
- A dict compared in one direction only, so dropping the size check survived.
- −1 packs to the same bytes in either byte order, and nothing forged a statement with the right hashes.

Found on the way, and matched rather than "fixed": `jcs.loads` refuses some canonical bytes. canon writes a container
256 deep, but `jcs.loads` refuses a container 257 deep (counting from the top) when the bytes hold more than 1024 `[`
and `{`, inside strings too. The module mirrors that, and the vectors hold both sides of the count.

## The three checks (test 136)

`run.py MODULE INPUT` prints a statement, `minds.metered-run@1`:
- the module's SHA-256 and the input's SHA-256;
- the budget;
- the steps spent;
- the result's kind;
- the SHA-256 of the result's encoding, as `vars1.RulesResult.encode` writes it.

`run.py --rerun STATEMENT MODULE INPUT` reproduces those bytes, or says why it does not count. Its exit codes:
- 0: reproduced;
- 1: other bytes;
- 2: not the module or the input the statement names.

- **One byte.** A module with one byte changed (in its output text) hashes to another value. The statement does not
  count for it (exit 2), and that module's own statement names another module and another result.
- **Exhausted.** On a live body (6340 steps), a budget of 6339 gives `exhausted` with digest SHA-256(`X`), never a
  verdict. A budget of 6340 gives the output.
- **Fault against refusal.** On an input starting with `!`:
  - the checker refuses it (E-1);
  - `checker-fault-variant.wasm`, built with `fault-variant`, traps (`fault`, SHA-256(`T`));
  - on every other input the variant gives the checker's result.

**Another host.** `host_wasmtime.py` reruns every vector on wasmtime 50.0.1 (Cranelift) and compares with Node (V8).
3615 of 3615 match, both result and steps. This check is optional and not in CI.

## Measured once (2026-11-13), as registered

On an Apple M4 Pro, Node v26.13.0, Python 3.15.2 (`measured.json`):

| | |
|---|---|
| steps per vector (`meter.py`) | median 5 567, maximum 43 043; live bodies median 6 028 |
| module | 154 713 bytes; metered 160 038 bytes. NFC's tables are most of it |
| T_metered, all 3615 vectors, median of 5 passes | 170.1 ms (47.0 µs per vector, a fresh instance each) |
| T_unmetered, the same way (descriptive) | 162.9 ms (45.1 µs) |
| T_python: warrant's check in one process (jcs.loads, the precondition, the function) | 411.1 ms (113.7 µs) |
| **T_metered / T_python** | **0.41** |
| metering's own cost | +4.4% |

## Verdict on the stop rule

The rule says: if T_metered / T_python ≥ 10 and nobody but us has rerun a result, do not start 6b.

The speed condition does not hold: the metered module is 2.4 times faster than the Python check on the same vectors.
So the rule does not fire, whatever the rerun condition says, and 6b may start.

The rerun condition holds today: only claude, the analysis session and this repository's CI have run it. It is to be
judged again on 2026-11-20, as registered, but it can no longer fire the rule.

## Found: warrant's own answer depends on the interpreter

Not pre-registered; descriptive.

The same export under Python 3.13.15 (Unicode 15.1.0) differs from Python 3.15.2 (Unicode 17.0.0) on 2 of 3615
vectors. Both are a schema whose role is U+16D67 U+16D67, which Unicode 16 composes into U+16D68:
- under 3.13, `actor_problem` finds the role in NFC and the schema is counted;
- under 3.15 it is not NFC and the schema is not counted.

warrant's CI runs Python 3.11 (Unicode 15.0). So one store can count a schema on one receiver and not on another,
though both run the same code identity.

The module carries its own tables, so it answers one way on every host. This is the case for 6a's form, measured on a
verdict, not only on a reason's text.

## Not established

- **Agreement beyond the recorded vectors.** Every branch is held by a mutant, but nothing is proved.
- **CI does not ask warrant again.** The vectors are recorded at f7e3637b. A later warrant engine is a new pin and a
  new export.
- **A trap on memory.** A memory request the host denies traps (`fault`) rather than refusing. No vector reaches it.
- **Who reruns.** Nobody outside us has rerun a statement.
- **What this says about `assess`.** It is one checker. Lineages, attests, trust and profiles (6b) are not measured
  here.

## Reproduce

```
.venv/bin/python -m unittest test_vars1.TestVars1Conformance.test_135_a_warrant_checker_runs_as_a_metered_rules_module
.venv/bin/python experiments/warrant-checker/vectors.py check                 # 0 differences
.venv/bin/python experiments/warrant-checker/run.py experiments/warrant-checker/checker.wasm INPUT
git clone https://github.com/s0fractal/warrant W && git -C W checkout f7e3637b4a965de5cc502ce6c8e6b1cd7f423673
PY=python3.15 (with cryptography); $PY -I experiments/warrant-checker/vectors.py export --warrant W   # the same file
$PY -I experiments/warrant-checker/measure.py --warrant W --smoke
```
