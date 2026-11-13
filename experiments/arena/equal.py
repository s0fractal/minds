#!/usr/bin/env python3
"""Byte equality of rules modules: the live v2 module (kernel2/lens2.wasm) and candidates, on the same inputs.

    .venv/bin/python experiments/arena/equal.py chain MODULE...   every tip of refs/vars/heads/minds, encoded for v2
    .venv/bin/python experiments/arena/equal.py props MODULE...   every v2 input the property suite feeds the kernel

Every input the rules v2 receive goes to the live module and to each MODULE; the outputs (the bytes after the length
word, or the refusal code) must be equal, byte for byte. `chain` encodes every tip of the chain for v2
(`kernel_facts`, as `shadow` does), whatever the rules of its own epoch. `props` runs test_vars1_props.py's own
unittest suite with `KernelRunner.run` wrapped: the suite's verdicts are its own; this only adds the comparison. Prints one
JSON line: inputs compared, differences (each with the input's SHA-256), and the suite's exit code for `props`.
"""
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT)]
import vars1 as V  # noqa: E402

mode, modules = sys.argv[1], [Path(m).resolve() for m in sys.argv[2:]]
others = [V.KernelRunner(V.H_LENS_KERNEL_V2, module=m) for m in modules]
seen = {"inputs": 0, "refusals": 0, "differences": []}
_run = V.KernelRunner.run


def run(self, kernel_input: bytes) -> bytes:
    try:
        mine = ("output", _run(self, kernel_input))
    except V.KernelRefusal as e:
        mine = ("refusal", e.code)
    if self.rules == V.H_LENS_KERNEL_V2 and self not in others:
        seen["inputs"] += 1
        seen["refusals"] += mine[0] == "refusal"
        for m, o in zip(modules, others):
            try:
                theirs = ("output", _run(o, kernel_input))
            except V.KernelRefusal as e:
                theirs = ("refusal", e.code)
            if theirs != mine:
                seen["differences"].append({"module": m.name, "input": hashlib.sha256(kernel_input).hexdigest(),
                                            "live": str(mine)[:80], "candidate": str(theirs)[:80]})
    if mine[0] == "refusal":
        raise V.KernelRefusal(mine[1])
    return mine[1]


V.KernelRunner.run = run
code = None
if mode == "chain":
    repo = V.GitVarsRepo(ROOT)
    chain = repo.commit_chain(repo.ref_commit("minds"))
    deltas = repo.chain_deltas(chain)
    live = V.kernel_runner(V.H_LENS_KERNEL_V2)
    for i in range(len(chain)):
        try:
            live.run(V.kernel_facts("minds", deltas[: i + 1], V.H_LENS_KERNEL_V2)[0])
        except V.KernelRefusal:
            pass
    seen["tips"] = len(chain)
elif mode == "props":
    sys.path.insert(0, str(ROOT))
    import unittest
    import test_vars1_props as P  # noqa: E402
    result = unittest.main(module=P, argv=[str(ROOT / "test_vars1_props.py")], exit=False, verbosity=0).result
    code = {"run": result.testsRun, "failures": len(result.failures), "errors": len(result.errors),
            "skipped": len(result.skipped)}
else:
    raise SystemExit(__doc__)
print(json.dumps({"mode": mode, "modules": [m.name for m in modules], **seen, "suite_exit": code}))
