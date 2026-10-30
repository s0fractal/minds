"""One measurement for README.md, not a target: on a G6 history of size L after its failure, the store's size, the
cones of the witnesses, and the time of `check.py` against the lens it does not run.

    .venv/bin/python experiments/witness/measure.py
"""
import json
import statistics
import time

import test_witness as TW


def main() -> None:
    h, ch, path, _, after = TW.g6_chain(1)
    repo = ch["repo"]
    t0 = time.perf_counter()
    lens = TW.V.GitVarsRepo(path).lens(TW.g6.SCOPE)  # a fresh instance: no cache, as check.py has none
    lens_s = time.perf_counter() - t0
    cones, checks, held = [], [], 0
    for d in h["decisions"]:
        cid = ch["ids"][d["id"]]
        if not lens["settled"].get(cid):
            continue
        term = TW.PR.prove(repo, TW.g6.SCOPE, cid, after)
        t0 = time.perf_counter()
        r = TW.CK.check(str(path), term)
        checks.append(time.perf_counter() - t0)
        held += r["result"] == "HELD"
        cones.append(len(term["cone"]))
    print(json.dumps({"decisions": len(h["decisions"]), "settled": len(cones), "held": held,
                      "store_cells": r["store_cells"], "cone": [min(cones), statistics.median(cones), max(cones)],
                      "lens_seconds": round(lens_s, 3), "check_seconds_median": round(statistics.median(checks), 3)},
                     indent=1))


if __name__ == "__main__":
    main()
