#!/usr/bin/env python3
"""Seed corpus for the kernel fuzzer: the kernel input at every admitted tip of the property suite's first random
programs (real, deep inputs for libFuzzer to mutate). Writes into kernel/fuzz/corpus/evaluate/ (not tracked).

    .venv/bin/python tools/fuzz_seeds.py [SEEDS]
"""
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
import vars1 as V  # noqa: E402
import test_vars1_props as P  # noqa: E402

out = ROOT / "kernel" / "fuzz" / "corpus" / "evaluate"
out.mkdir(parents=True, exist_ok=True)
for seed in range(int(sys.argv[1]) if len(sys.argv) > 1 else 15):
    _, _, it, tmp = P.generate(seed, 8)
    for c in it.repo.commit_chain(it.tip):
        ki, _ = V.kernel_facts(P.SCOPE, [it.repo.read_cas_tree(x) for x in it.repo.commit_chain(c)])
        (out / hashlib.sha256(ki).hexdigest()[:16]).write_bytes(ki)
    tmp.cleanup()
print(len(list(out.iterdir())), "seed inputs in", out)
