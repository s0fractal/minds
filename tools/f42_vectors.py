#!/usr/bin/env python3
"""F42 vectors (RULES-V2.md §8): cases of v2's typed references, with the answers of the Lean oracle
`proofs/Vars1/Mask.lean` (compiled as `vars1mask`), never of the host's parser. test_vars1.py 89 holds the host to
them; CI regenerates the file with the oracle and refuses any difference.

Mask cases are a schema's field descriptors (UTF8 atoms `name:type`, the domain schema admission accepts) and the
oracle's mask. Reference cases are an instance of such a schema, or of the standard verdict or acceptance schema, and
the oracle's reference positions: what each slot holds (empty, a cell, anything else) and whether a verdict's or an
acceptance's payload is a cell. The cases are fixed corners plus a seeded random sample, so the file is reproducible.

    python3 tools/f42_vectors.py --write   # regenerate vectors/f42.json with the oracle
    python3 tools/f42_vectors.py --check   # CI: the file is exactly what the oracle answers now
"""
from __future__ import annotations

import json
import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ORACLE = ROOT / "proofs" / ".lake" / "build" / "bin" / "vars1mask"
OUT = ROOT / "vectors" / "f42.json"
TYPES = ["utf8", "u64", "pol1", "root", "digest", "wasm", "kin1", "cell", "hash"]
NAMES = ["a", "cell", "cells", "x1", "the cell", "ünïcode", "c", "utf8", "z" * 40]
# the standard verdict and acceptance schemas' descriptors (VARS-1-SPEC.md §2), as data; test 89 checks the host's
# standard schemas name exactly these
VERDICT = ["ckpt_or_witness:cell", "verdict_code:utf8", "verifier_id:utf8"]
ACCEPTANCE = ["source_scope:utf8", "foreign_scope_cell:cell"]


def atom(descriptor: str) -> str:
    return (b"UTF8" + descriptor.encode()).hex()


def cases() -> tuple[list[list[str]], list[dict]]:
    rnd = random.Random(42)
    corners = [[], ["a:cell"], ["a:utf8"], ["cell:utf8"], ["cells:cell"], ["a:cell", "b:cell"],
               [f"f{i}:cell" for i in range(64)], [f"f{i}:utf8" for i in range(63)] + ["last:cell"],
               ["first:cell"] + [f"f{i}:hash" for i in range(63)], [f"{n}:{t}" for n, t in zip(NAMES, TYPES)]]
    masks = corners + [[f"{rnd.choice(NAMES)}:{rnd.choice(TYPES)}" for _ in range(rnd.randrange(0, 65))]
                       for _ in range(200)]
    refs = []
    for ds in masks[:60]:
        refs.append({"schema": "custom", "descriptors": ds, "typed": False, "payload_cell": False,
                     "slots": [rnd.randrange(3) for _ in ds]})
    for kind, ds in (("verdict", VERDICT), ("acceptance", ACCEPTANCE)):
        for payload_cell in (False, True):
            for _ in range(10):
                refs.append({"schema": kind, "descriptors": ds, "typed": True, "payload_cell": payload_cell,
                             "slots": [rnd.randrange(3) for _ in ds]})
    return masks, refs


def ask(lines: list[str]) -> list[str]:
    if not ORACLE.exists():
        raise SystemExit("build the oracle first: cd proofs && lake build vars1mask")
    out = subprocess.run([str(ORACLE)], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True)
    answers = out.stdout.splitlines()
    if len(answers) != len(lines) or "E" in answers:
        raise SystemExit("the oracle refused a case: every case must lie in its domain")
    return answers


def render() -> str:
    masks, refs = cases()
    mask_answers = ask(["M " + " ".join(atom(d) for d in ds) for ds in masks])
    masks_of = {tuple(ds): int(a) for ds, a in zip(masks, mask_answers)}
    for r in refs:  # the standard schemas' masks come from the oracle too
        if tuple(r["descriptors"]) not in masks_of:
            masks_of[tuple(r["descriptors"])] = int(ask(["M " + " ".join(atom(d) for d in r["descriptors"])])[0])
    ref_answers = ask([f"R {int(r['typed'])} {int(r['payload_cell'])} {masks_of[tuple(r['descriptors'])]} "
                       + " ".join(map(str, r["slots"])) for r in refs])
    doc = {"format": "minds.f42-vectors@1", "oracle": "proofs/Vars1/Mask.lean (vars1mask)",
           "masks": [{"descriptors": ds, "mask": int(a)} for ds, a in zip(masks, mask_answers)],
           "refs": [dict(r, positions=[] if a == "-" else [int(x) for x in a.split()])
                    for r, a in zip(refs, ref_answers)]}
    return json.dumps(doc, indent=1, ensure_ascii=False) + "\n"


def main(argv: list[str]) -> int:
    text = render()
    if "--write" in argv:
        OUT.parent.mkdir(exist_ok=True)
        OUT.write_text(text)
        return 0
    if "--check" in argv:
        if not OUT.exists() or OUT.read_text() != text:
            print("vectors/f42.json is not what the oracle answers now (tools/f42_vectors.py --write)")
            return 1
        print("f42 vectors: the oracle's")
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
