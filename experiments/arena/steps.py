#!/usr/bin/env python3
"""Steps (meter.py's fuel) each module spends on every tip of refs/vars/heads/minds encoded for v2, and its memory.

    .venv/bin/python experiments/arena/steps.py MODULE...

One JSON line per module: total, median and largest steps over the tips, the steps at the tip, and whether every
output equals the first module's (the metered run is a second, independent comparison of the outputs)."""
import json
import statistics
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT)]
import meter  # noqa: E402
import vars1 as V  # noqa: E402

repo = V.GitVarsRepo(ROOT)
chain = repo.commit_chain(repo.ref_commit("minds"))
deltas = repo.chain_deltas(chain)
inputs = [V.kernel_facts("minds", deltas[: i + 1], V.H_LENS_KERNEL_V2)[0] for i in range(len(chain))]
first = None
for m in sys.argv[1:]:
    p = subprocess.Popen(["node", str(Path(__file__).with_name("steps.mjs"))], stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, text=True)
    p.stdin.write(meter.metered(Path(m).read_bytes()).hex() + "\n")
    rows = []
    for x in inputs:
        p.stdin.write(x.hex() + "\n")
        p.stdin.flush()
        steps, out = p.stdout.readline().split()
        rows.append((int(steps), out))
    p.stdin.close()
    p.wait()
    first = first or [o for _, o in rows]
    s = [n for n, _ in rows]
    print(json.dumps({"module": Path(m).name, "tips": len(s), "total": sum(s), "median": statistics.median(s),
                      "max": max(s), "at_tip": s[-1], "outputs_equal_first": [o for _, o in rows] == first}))
