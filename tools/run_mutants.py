#!/usr/bin/env python3
"""Run the mutants of mutants.json: each replaces one exact string in one file, then the tests it names must fail
on an assertion, or on a TwinDivergence (the rules kernel and its Python twin disagree: the differential witness
caught the mutant). An import error or any other crash proves nothing. The file is restored after every mutant.

    .venv/bin/python tools/run_mutants.py            # all
    .venv/bin/python tools/run_mutants.py ID...      # some
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def run(mid: str, m: dict) -> tuple[bool, str]:
    path = ROOT / m["file"]
    original = path.read_text()
    if original.count(m["find"]) != 1:
        return False, f"find string occurs {original.count(m['find'])} times in {m['file']}"
    try:
        path.write_text(original.replace(m["find"], m["replace"]))
        for t in m["kills"]:
            # a fresh bytecode cache per run: a cache written for an earlier mutant of the same size in the same
            # second would otherwise be loaded in place of this one's source
            with tempfile.TemporaryDirectory() as cache:
                out = subprocess.run([sys.executable, "-X", f"pycache_prefix={cache}", "-m", "unittest",
                                      f"test_vars1.TestVars1Conformance.{t}"], cwd=ROOT, capture_output=True, text=True)
            text = out.stdout + out.stderr
            if out.returncode != 0 and "AssertionError" in text:
                return True, f"killed by {t}"
            if out.returncode != 0 and "TwinDivergence" in text:
                return True, f"killed by {t} (kernel and twin diverge)"
        return False, f"survived {', '.join(m['kills'])}"
    finally:
        path.write_text(original)


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
