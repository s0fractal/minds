"""Task 8: how far a status change spreads in VARS-1, measured through the real gate and the v2 rules kernel.

Theory (REPORT.md). Every cell is attacked by Poisson(lambda) newer cells (invalidates edges, latched: one seal of a
1-of-3 admission roster) and relied on by Poisson(mu) newer cells (relies edges). Pass 1 is NOR on the kill edges,
Pass 2 is OR down `relies`, and the first does not read the second. With W the principal branch of Lambert's W:

- Effective fraction p = W(lambda)/lambda; a flip of Effective spreads with branching factor r1 = W(lambda), critical
  at lambda = e; mean cells flipped by one kill, 1/(1 - r1).
- Live fraction (Active and not Stale) q, the solution <= p of q = p e^{-mu(1-q)}; a flip of Live spreads to
  dependents with factor r2 = mu q = -W(-p mu e^{-mu}) < 1 whenever p < 1. Only at p = 1 (no kills) is it critical,
  at mu = 1. Mean Live cells flipped by one kill of an Effective cell: (1/(1 - r1)) (q/p) / (1 - r2).

Here: a chain of N cells per (lambda, mu) is admitted through the gate in batches, the lens reads every status, and
then R kills of random Effective cells are each built as a candidate commit (never advanced) and read by the lens at
it. Edges are drawn within a band of the next 150 cells, so degrees are stationary away from the ends. Measured: p
and q over the cells with a full band on both sides, and the mean flips over kills in the newer half of that middle.

    .venv/bin/python experiments/criticality/run.py OUT.json [N [R]]
"""
import hashlib
import json
import math
import random
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
import vars1 as V  # noqa: E402

SCOPE = "crit"
WORK = Path.home() / "Projects" / ".worktrees" / "witness-work"


def lambert_w(x: float) -> float:
    """Principal branch W0 on [-1/e, inf), by Halley's iteration."""
    if x == 0:
        return 0.0
    w = math.log1p(x) if x > -0.25 else -0.9
    w = max(w, -0.999999)
    for _ in range(200):
        ew = math.exp(w)
        f = w * ew - x
        step = f / (ew * (w + 1) - (w + 2) * f / (2 * w + 2))
        w -= step
        if abs(step) < 1e-15:
            break
    return w


def theory(lam: float, mu: float) -> dict:
    p = lambert_w(lam) / lam if lam > 0 else 1.0
    r1 = lambert_w(lam)
    if p < 1:
        r2 = -lambert_w(-p * mu * math.exp(-mu))
    else:
        r2 = mu  # nothing is dead: the Stale layer is a plain branching process
    q = r2 / mu if mu > 0 else p
    if p == 1:
        q = 1.0
    kill = 1 / (1 - r1) if r1 < 1 else math.inf
    live = kill * (q / p) / (1 - r2) if r1 < 1 and r2 < 1 else math.inf
    return {"p": p, "q": q, "r1": r1, "r2": r2, "kill_flips": kill, "live_flips": live}


def poisson(rng: random.Random, lam: float) -> int:
    lim, k, prod = math.exp(-lam), 0, 1.0
    while True:
        prod *= rng.random()
        if prod <= lim:
            return k
        k += 1


def graph(n: int, lam: float, mu: float, seed: int, band: int):
    """For each cell i, Poisson(lam) attackers and Poisson(mu) dependents drawn uniformly among the `band` cells after
    it. Away from both ends every cell then has about lam attackers and lam targets, mu relied cells and mu dependents
    (uniform among all newer cells would give old cells few relied cells and new cells many)."""
    rng = random.Random(seed)
    kills = [set() for _ in range(n)]
    relies = [set() for _ in range(n)]
    for i in range(n - 1):
        hi = min(n, i + 1 + band)
        for _ in range(poisson(rng, lam)):
            kills[rng.randrange(i + 1, hi)].add(i)
        for _ in range(poisson(rng, mu)):
            relies[rng.randrange(i + 1, hi)].add(i)
    return kills, relies, rng


class Chain:
    """A scope of one key-holder ('ana' of a 1-of-3 admission roster) under the v2 rules, admitted through the gate."""

    def __init__(self, path: Path) -> None:
        subprocess.run(["git", "init", "-q", str(path)], check=True)
        for k, v in (("user.name", "crit"), ("user.email", "crit@local"), ("gc.auto", "0")):
            subprocess.run(["git", "-C", str(path), "config", k, v], check=True)
        self.repo = V.GitVarsRepo(path)
        self.sk = {m: hashlib.sha256(b"crit/" + m.encode()).digest() for m in ("ana", "bo", "cy")}
        a = dict(V.STD_SCHEMA_ATOMS)
        a[V.H_LENS_KERNEL_V2] = V.KERNEL2_ATOM
        keys = V.atom_hvec(sorted(V.ed25519_pubkey(s) for s in self.sk.values()))
        a[V.sha256(keys)] = keys
        pol = V.atom_pol1(1, V.sha256(keys))
        a[V.sha256(pol)] = pol
        name, payload = V.atom_utf8(f"{SCOPE}/SCOPE"), V.atom_utf8(SCOPE)
        a[V.sha256(name)], a[V.sha256(payload)] = name, payload
        self.scope = V.Cell(V.H_SCHEMA["scope"], V.sha256(name), V.sha256(payload),
                            slots=(V.sha256(pol), V.sha256(pol), V.H_LENS_KERNEL_V2))
        self.tip = self.repo.build_candidate_commit(SCOPE, a, [*V.STD_SCHEMAS.values(), self.scope],
                                                    [V.Seal.sign(self.sk["ana"], self.scope.id, self.scope.id)],
                                                    parent_commit=None)
        self.repo.admit_and_advance(SCOPE, self.tip, expected_old=None)
        self.atoms = {}

    def put(self, raw: bytes) -> bytes:
        self.atoms[V.sha256(raw)] = raw
        return V.sha256(raw)

    def axiom(self, name: str, relies, kills) -> V.Cell:
        kw = {}
        if relies:
            kw["h_relies"] = self.put(V.atom_hvec(sorted(relies)))
        if kills:
            kw["h_invalidates"] = self.put(V.atom_hvec(sorted(kills)))
        return V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=self.put(V.atom_utf8(f"{SCOPE}/{name}")),
                      h_payload=self.put(V.atom_utf8(name)), **kw)

    def candidate(self, cells) -> str:
        c = self.repo.build_candidate_commit(SCOPE, self.atoms, cells,
                                             [V.Seal.sign(self.sk["ana"], x.id, self.scope.id) for x in cells],
                                             parent_commit=self.tip)
        self.atoms = {}
        return c

    def commit(self, cells) -> None:
        c = self.candidate(cells)
        self.repo.admit_and_advance(SCOPE, c, expected_old=self.tip)
        self.tip = c


def one(n: int, lam: float, mu: float, r: int, seed: int, band: int = 150) -> dict:
    kills, relies, rng = graph(n, lam, mu, seed, band)
    c = Chain(Path(tempfile.mkdtemp(dir=WORK, prefix="crit-")))
    t0 = time.time()
    ids, batch = [], []
    for j in range(n):
        x = c.axiom(f"n/{j}", [ids[i] for i in relies[j]], [ids[i] for i in kills[j]])
        ids.append(x.id)
        batch.append(x)
        if len(batch) == 250:
            c.commit(batch)
            batch = []
    if batch:
        c.commit(batch)
    lens = c.repo.lens(SCOPE)
    eff = lambda L, x: bool(L["effective"].get(x))  # noqa: E731
    live = lambda L, x: bool(L["active"].get(x)) and not L["stale"].get(x)  # noqa: E731
    bulk = ids[band: n - band]  # the stationary middle: full bands on both sides
    p = sum(eff(lens, x) for x in bulk) / len(bulk)
    q = sum(live(lens, x) for x in bulk) / len(bulk)
    targets = [x for x in ids[n // 2: n - band] if eff(lens, x)]  # room behind for a kill, ahead for Stale
    kf, lf = [], []
    for k in range(r):
        t = targets[rng.randrange(len(targets))]
        cand = c.candidate([c.axiom(f"kill/{k}", [], [t])])
        after = c.repo.lens(SCOPE, at=cand)
        kf.append(sum(eff(lens, x) != eff(after, x) for x in ids))
        lf.append(sum(live(lens, x) != live(after, x) for x in ids))
    return {"n": n, "band": band, "lambda": lam, "mu": mu, "kills": r, "seed": seed, "p": p, "q": q,
            "kill_flips": sum(kf) / r, "live_flips": sum(lf) / r, "kill_flips_max": max(kf),
            "live_flips_max": max(lf), "theory": theory(lam, mu), "seconds": round(time.time() - t0, 1)}


GRID = ([(lam, 0.0) for lam in (0.5, 1.0, 1.5, 2.0, math.e, 3.0, 4.0)]
        + [(lam, mu) for lam in (0.5, 1.0) for mu in (0.5, 1.0, 2.0)]
        + [(0.0, mu) for mu in (0.5, 0.8, 1.2)])


if __name__ == "__main__":
    out = Path(sys.argv[1])
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
    r = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    WORK.mkdir(parents=True, exist_ok=True)
    rows = []
    for i, (lam, mu) in enumerate(GRID):
        rows.append(one(n, lam, mu, r, seed=1000 + i))
        print(json.dumps({k: (round(v, 4) if isinstance(v, float) else v) for k, v in rows[-1].items() if k != "theory"}),
              flush=True)
        out.write_text(json.dumps(rows, indent=1) + "\n")
