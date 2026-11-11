"""The results table of REPORT.md, from results.json: measured against the theory of run.py.

    python3 -I experiments/criticality/table.py experiments/criticality/results.json
"""
import json
import math
import sys


def f(x, d=3):
    return "∞" if x == math.inf or x is None else f"{x:.{d}f}"


rows = json.load(open(sys.argv[1]))
out = ["| λ | μ | p measured | p theory | q measured | q theory | r₁ | r₂ | kill flips measured | theory | Live flips "
       "measured | theory | largest Live flip |",
       "|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
for r in rows:
    t = r["theory"]
    lam = "e" if abs(r["lambda"] - math.e) < 1e-9 else f(r["lambda"], 2)
    out.append(f"| {lam} | {f(r['mu'], 2)} | {f(r['p'])} | {f(t['p'])} | {f(r['q'])} | {f(t['q'])} | {f(t['r1'])} | "
               f"{f(t['r2'])} | {f(r['kill_flips'], 2)} | {f(t['kill_flips'], 2)} | {f(r['live_flips'], 2)} | "
               f"{f(t['live_flips'], 2)} | {r['live_flips_max']} |")
print("\n".join(out))
