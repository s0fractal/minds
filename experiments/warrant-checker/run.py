#!/usr/bin/env python3
"""A metered run of a rules module as a statement anyone can rerun (experiment 6a, README.md).

    python run.py MODULE INPUT [--budget N]           # run once; print the statement (canonical JSON)
    python run.py --rerun STATEMENT MODULE INPUT      # 0: the same bytes; 1: other bytes; 2: not the module or input named

The statement names the module and the input by their SHA-256, the budget of steps, the steps spent, the kind of the
result (output, refusal, exhausted, fault) and the SHA-256 of its encoding as vars1.RulesResult.encode writes it (`O` +
output, `E` + the code as i32 little-endian, `X`, `T`). Steps are a property of the module and the input (meter.py),
so a rerun on any host gives the same statement. A module or an input that does not hash to what the statement names
is another one, and the statement says nothing about it."""
from __future__ import annotations

import argparse
import hashlib
import json
import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import vectors as VEC  # noqa: E402

FORMAT = "minds.metered-run@1"
KINDS = {"X": "exhausted", "T": "fault"}


def encode(result: str) -> tuple[str, bytes]:
    """The kind of a host result (vectors.Host) and its encoding."""
    if result in KINDS:
        return KINDS[result], result.encode()
    if result.startswith("E"):
        return "refusal", b"E" + struct.pack("<i", int(result[1:]))
    return "output", b"O" + bytes.fromhex(result)


def statement(module: bytes, raw: bytes, budget: int = VEC.BUDGET, host: VEC.Host | None = None) -> bytes:
    own = host is None
    host = host or VEC.Host(module)
    try:
        steps, result = host.run(raw, budget)
    finally:
        if own:
            host.close()
    kind, enc = encode(result)
    doc = {"budget": budget, "format": FORMAT, "input": hashlib.sha256(raw).hexdigest(),
           "module": hashlib.sha256(module).hexdigest(), "result": {"kind": kind, "sha256": hashlib.sha256(enc).hexdigest()},
           "steps": steps}
    return json.dumps(doc, sort_keys=True, separators=(",", ":")).encode() + b"\n"


def rerun(stated: bytes, module: bytes, raw: bytes) -> tuple[int, str]:
    doc = json.loads(stated)
    if doc.get("format") != FORMAT:
        return 2, f"not a {FORMAT} statement"
    for what, data in (("module", module), ("input", raw)):
        if hashlib.sha256(data).hexdigest() != doc[what]:
            return 2, f"not counted: the {what} hashes to {hashlib.sha256(data).hexdigest()}, the statement names {doc[what]}"
    again = statement(module, raw, doc["budget"])
    if again != stated:
        return 1, "rerun gives other bytes: " + again.decode().strip()
    return 0, "reproduced: " + again.decode().strip()


def main(argv) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--rerun", metavar="STATEMENT")
    ap.add_argument("--budget", type=int, default=VEC.BUDGET)
    ap.add_argument("module")
    ap.add_argument("input")
    a = ap.parse_args(argv)
    module, raw = Path(a.module).read_bytes(), Path(a.input).read_bytes()
    if a.rerun:
        code, why = rerun(Path(a.rerun).read_bytes(), module, raw)
        print(why)
        return code
    sys.stdout.write(statement(module, raw, a.budget).decode())
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
