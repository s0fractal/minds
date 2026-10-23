#!/usr/bin/env python3
"""Run the mutants of mutants.json: each replaces one exact string in one file, then the tests it names must fail
on an assertion, or on a TwinDivergence (the rules kernel and its Python twin disagree: the differential witness
caught the mutant). An import error or any other crash proves nothing. The file is restored after every mutant.
A mutant of kernel/src/ or kernel2/src/ is built to wasm in its own target directory (under MINDS_KERNEL_TARGET,
default .git/kernel-mutants-target) and its tests receive the build as MINDS_KERNEL_WASM or MINDS_KERNEL2_WASM.

    .venv/bin/python tools/run_mutants.py            # all
    .venv/bin/python tools/run_mutants.py ID...      # some
"""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KERNELS = {"kernel": ("vars_lens.wasm", "MINDS_KERNEL_WASM", "kernel/lens.wasm"),
           "kernel2": ("vars_lens2.wasm", "MINDS_KERNEL2_WASM", "kernel2/lens2.wasm")}


def run(mid: str, m: dict) -> tuple[bool, str]:
    path = ROOT / m["file"]
    original = path.read_text()
    if original.count(m["find"]) != 1:
        return False, f"find string occurs {original.count(m['find'])} times in {m['file']}"
    env_extra: dict = {}
    cleanup: list = []
    try:
        path.write_text(original.replace(m["find"], m["replace"]))
        crate = next((k for k in KERNELS if m["file"].startswith(f"{k}/src/")), None)
        if crate:
            # a mutant of a rules kernel: build it beside the real one (its own target directory, never the crate's)
            # and hand the build to the tests; the kernel the gate runs is untouched
            wasm, var, pinned = KERNELS[crate]
            # a fresh target per mutant: cargo decides what to rebuild by modification time, so a mutant written in the
            # same second as the previous one could be served the previous mutant's build
            base = Path(os.environ.get("MINDS_KERNEL_TARGET", ROOT / ".git" / "kernel-mutants-target"))
            base.mkdir(parents=True, exist_ok=True)
            target = Path(tempfile.mkdtemp(prefix=f"{mid}-", dir=base))
            cleanup.append(target)
            b = subprocess.run(["cargo", "build", "--release", "--target", "wasm32-unknown-unknown"],
                               cwd=ROOT / crate, capture_output=True, text=True,
                               env=dict(os.environ, CARGO_TARGET_DIR=str(target)))
            if b.returncode != 0:
                return False, "the mutant does not build: " + b.stderr.strip().splitlines()[-1][:120]
            built = target / "wasm32-unknown-unknown" / "release" / wasm
            if hashlib.sha256(built.read_bytes()).digest() == hashlib.sha256((ROOT / pinned).read_bytes()).digest():
                return False, "the mutant builds to the unmutated kernel (an equivalent mutant)"
            env_extra[var] = str(built)
        for t in m["kills"]:
            # a fresh bytecode cache per run: a cache written for an earlier mutant of the same size in the same
            # second would otherwise be loaded in place of this one's source
            with tempfile.TemporaryDirectory() as cache:
                env = dict(os.environ, MINDS_MUTANT=mid, **env_extra)  # check_claims skips the applied mutant
                out = subprocess.run([sys.executable, "-X", f"pycache_prefix={cache}", "-m", "unittest",
                                      f"test_vars1.TestVars1Conformance.{t}"], cwd=ROOT, capture_output=True, text=True,
                                     env=env)
            text = out.stdout + out.stderr
            if out.returncode != 0 and "AssertionError" in text:
                return True, f"killed by {t}"
            if out.returncode != 0 and "TwinDivergence" in text:
                return True, f"killed by {t} (kernel and twin diverge)"
        return False, f"survived {', '.join(m['kills'])}"
    finally:
        path.write_text(original)
        for d in cleanup:
            shutil.rmtree(d, ignore_errors=True)


def main(argv: list[str]) -> int:
    mutants = json.loads((ROOT / "mutants.json").read_text())
    chosen = argv or sorted(mutants)
    survived = 0
    for mid in chosen:
        ok, why = run(mid, mutants[mid])
        survived += not ok
        print(f"{'killed  ' if ok else 'SURVIVED'} {mid}: {why}", flush=True)
    print(f"{len(chosen) - survived}/{len(chosen)} killed")
    return 1 if survived else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
