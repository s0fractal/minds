#!/usr/bin/env python3
"""The measures pre-registered for experiment 6a (record 5c724596 in .warrant, goal@1 E6A), run once.

    python measure.py --warrant DIR [--smoke]

DIR is the warrant checkout at vectors.PIN; run under the interpreter that recorded the vectors (Python 3.15.2). It
writes measured.json: steps per vector under meter.py (median, maximum), the module's bytes and its metered
rewrite's, and wall times over every vector on this machine, each the median of 5 passes: the metered module under
Node (compiled once, a fresh instance per vector), the same module unmetered (descriptive), and warrant's Python
check in one process (jcs.loads, the precondition, the function). --smoke runs one pass over 20 vectors and records
nothing (a check that the script runs, not a measure)."""
from __future__ import annotations

import argparse
import json
import platform
import statistics
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import vectors as VEC  # noqa: E402

PASSES = 5


def main(argv) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--warrant", required=True)
    ap.add_argument("--smoke", action="store_true")
    a = ap.parse_args(argv)
    ref = VEC.Reference(Path(a.warrant).resolve())
    sys.path.insert(0, str(VEC.ROOT))
    import meter
    doc = VEC.load()
    raws = [VEC.raw_of(v) for v in doc["vectors"]]
    passes = PASSES
    if a.smoke:
        raws, passes = raws[:20], 1
    module = VEC.MODULE.read_bytes()
    metered = meter.metered(module)

    diffs, steps = VEC.check(VEC.MODULE, dict(doc, vectors=doc["vectors"][:len(raws)]))
    if diffs:
        raise SystemExit(f"{len(diffs)} differences: no measure of a module that disagrees")

    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        (tmp / "inputs.bin").write_bytes(struct.pack("<I", len(raws)) + b"".join(struct.pack("<I", len(r)) + r for r in raws))
        (tmp / "metered.wasm").write_bytes(metered)
        node = {}
        for mode, file in (("metered", tmp / "metered.wasm"), ("plain", VEC.MODULE)):
            out = subprocess.run(["node", str(HERE / "time.mjs"), str(file), str(tmp / "inputs.bin"), str(passes), mode],
                                 capture_output=True, text=True, check=True)
            node[mode] = json.loads(out.stdout)

    E, C = ref.E, ref.C

    def plain(raw):
        try:
            v = C.loads(raw)
        except ValueError:
            return
        if not isinstance(v, dict) or set(v) not in ({"schema"}, {"record", "schema"}):
            return
        if set(v) == {"schema"}:
            return E._schema_problem(v["schema"])
        if ref.asked(v["record"], v["schema"]):
            return E._body_problem(v["record"], v["schema"])

    py = []
    for _ in range(passes):
        t0 = time.perf_counter_ns()
        for raw in raws:
            plain(raw)
        py.append(time.perf_counter_ns() - t0)

    if a.smoke:
        print("smoke: the script runs; nothing recorded")
        return 0
    t_m, t_p, t_py = (statistics.median(x) for x in (node["metered"]["passes_ns"], node["plain"]["passes_ns"], py))
    live = [s for s, v in zip(steps, doc["vectors"]) if v["source"] == "live"]
    ratio = t_m / t_py
    result = {
        "registered": "5c72459664b0ab3d02914f73f8fe3c87045c4b9443e842d4aca5260e6f8b07da",
        "module": {"sha256": VEC.MODULE_SHA256, "bytes": len(module), "metered_bytes": len(metered)},
        "vectors": len(raws),
        "steps": {"median": statistics.median(steps), "max": max(steps), "live_median": statistics.median(live),
                  "live_max": max(live), "total": sum(steps)},
        "wall_ns": {"metered": t_m, "unmetered": t_p, "python": t_py,
                    "passes": {"metered": node["metered"]["passes_ns"], "unmetered": node["plain"]["passes_ns"], "python": py}},
        "per_vector_us": {"metered": t_m / len(raws) / 1000, "unmetered": t_p / len(raws) / 1000,
                          "python": t_py / len(raws) / 1000},
        "ratio": {"metered_over_python": ratio, "unmetered_over_python": t_p / t_py, "metered_over_unmetered": t_m / t_p},
        "stop_rule": {"speed_condition": ratio >= 10},
        "host": {"machine": platform.machine(), "system": f"{platform.system()} {platform.release()}",
                 "cpu": subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True, text=True).stdout.strip(),
                 "node": subprocess.run(["node", "--version"], capture_output=True, text=True).stdout.strip(),
                 "python": sys.version.split()[0]},
    }
    (HERE / "measured.json").write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps(result, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
