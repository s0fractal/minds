#!/usr/bin/env python3
"""A second host for the metered checker: wasmtime (Cranelift) instead of Node (V8). Optional, not run by CI.

    pip install wasmtime && python host_wasmtime.py [--module FILE]

Runs meter.py's rewrite of the module on every vector with a fresh instance per run, as host.mjs does, and compares
each run's steps and result with host.mjs's. Prints {"vectors", "same_result", "same_steps"}; exit 0 only when every
run agrees: steps are the module's and the input's, not the engine's."""
from __future__ import annotations

import argparse
import json
import sys
from importlib import metadata
from pathlib import Path

import wasmtime as W

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import vectors as VEC  # noqa: E402


def run(engine, module, raw: bytes, budget: int):
    store = W.Store(engine)
    ex = W.Instance(store, module, []).exports(store)
    ex["minds_exhausted"].set_value(store, W.Val.i32(0))
    ex["minds_fuel"].set_value(store, W.Val.i64(budget))
    try:
        ex["reset"](store)
        ptr = ex["alloc"](store, len(raw))
        ex["memory"].write(store, raw, ptr)
        out = ex["run"](store, ptr, len(raw))
    except W.Trap:
        steps = budget - ex["minds_fuel"].value(store)
        return steps, "X" if ex["minds_exhausted"].value(store) == 1 else "T"
    steps = budget - ex["minds_fuel"].value(store)
    if out < 0:
        return steps, f"E{out}"
    n = int.from_bytes(ex["memory"].read(store, out, out + 4), "little")
    return steps, ex["memory"].read(store, out + 4, out + 4 + n).hex()


def main(argv) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--module", default=str(VEC.MODULE))
    a = ap.parse_args(argv)
    sys.path.insert(0, str(VEC.ROOT))
    import meter
    data = Path(a.module).read_bytes()
    engine = W.Engine()
    module = W.Module(engine, meter.metered(data))
    node = VEC.Host(data)
    same_result = same_steps = 0
    doc = VEC.load()
    try:
        for v in doc["vectors"]:
            raw = VEC.raw_of(v)
            mine, theirs = run(engine, module, raw, VEC.BUDGET), node.run(raw)
            same_result += mine[1] == theirs[1]
            same_steps += mine[0] == theirs[0]
    finally:
        node.close()
    n = len(doc["vectors"])
    print(json.dumps({"vectors": n, "same_result": same_result, "same_steps": same_steps, "wasmtime": metadata.version("wasmtime")}))
    return 0 if same_result == same_steps == n else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
