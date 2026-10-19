#!/usr/bin/env python3
"""How admission and lens cost grow with chain history (VARS-1 host, `vars1.py`).

Builds a chain of N commits of K local axioms each (one seal each) directly in Git, without the gate, then at each
checkpoint length times one gate admission of a further commit and one `lens()`, each on a fresh `GitVarsRepo`
(cold: what a `minds_chain.py` process pays), then a second admission and lens on the instance that admitted the
first (warm: its caches hold the history).

    .venv/bin/python tools/bench_chain.py                       # 10 40 80 320, edgeless and edges
    .venv/bin/python tools/bench_chain.py --lengths 10 40 --shape edges
    .venv/bin/python tools/bench_chain.py --root ../minds-old   # time another checkout's vars1.py

Shapes: `edgeless` (all-local axioms, no edges); `edges` (every axiom relies on the previous commit's axioms, and
each commit rebinds one name by a supersedes edge from the previous binding, which its author may authorize).
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
ap.add_argument("--root", default=str(Path(__file__).resolve().parent.parent), help="checkout whose vars1.py to time")
ap.add_argument("--lengths", type=int, nargs="+", default=[10, 40, 80, 320])
ap.add_argument("--per-commit", type=int, default=10)
ap.add_argument("--shape", choices=["edgeless", "edges", "both"], default="both")
ap.add_argument("--json", help="also write the results here")
args = ap.parse_args()

sys.path.insert(0, str(Path(args.root).resolve()))
import vars1 as V  # noqa: E402

SK = b"\x01" * 32
PK = V.ed25519_pubkey(SK)
SCOPE = "core"


class Builder:
    """Writes chain commits straight into Git (blobs, one growing private index, write-tree, commit-tree)."""

    def __init__(self, repo: Path) -> None:
        self.repo = repo
        self.env = {**os.environ, "GIT_INDEX_FILE": str(repo / ".git" / "bench-index")}
        self.tip: str | None = None
        self.seen: set[bytes] = set()

    def git(self, *a: str, inp: bytes | None = None) -> str:
        return subprocess.run(["git", "-C", str(self.repo), *a], input=inp, env=self.env, capture_output=True,
                              check=True).stdout.decode().strip()

    def commit(self, atoms: dict[bytes, bytes], cells: list, seals: list) -> str:
        entries = [("atoms", h, raw) for h, raw in atoms.items()]
        entries += [("cells", c.id, c.encode()) for c in cells] + [("seals", s.id, s.encode()) for s in seals]
        entries = [e for e in entries if e[1] not in self.seen]
        self.seen.update(e[1] for e in entries)
        if entries:
            with tempfile.TemporaryDirectory() as d:
                paths = []
                for i, (_, _, raw) in enumerate(entries):
                    p = Path(d) / str(i)
                    p.write_bytes(raw)
                    paths.append(str(p))
                oids = self.git("hash-object", "-w", "--stdin-paths", inp="\n".join(paths).encode()).split()
            lines = [f"100644 {oid}\tcas/{kind}/{h.hex()[:2]}/{h.hex()[2:]}" for (kind, h, _), oid in zip(entries, oids)]
            self.git("update-index", "--add", "--index-info", inp=("\n".join(lines) + "\n").encode())
        tree = self.git("write-tree")
        cmd = ["commit-tree", tree, "-m", f"vars({SCOPE}): bench"] + (["-p", self.tip] if self.tip else [])
        return self.git(*cmd)

    def advance(self, commit: str) -> None:
        self.git("update-ref", f"refs/vars/heads/{SCOPE}", commit)
        self.tip = commit


def put(atoms: dict[bytes, bytes], raw: bytes) -> bytes:
    h = V.sha256(raw)
    atoms[h] = raw
    return h


def genesis() -> tuple[dict[bytes, bytes], list, list, V.Cell]:
    atoms = dict(V.STD_SCHEMA_ATOMS)
    pol = put(atoms, V.atom_pol1(1, put(atoms, V.atom_hvec([PK]))))
    s0 = V.Cell(h_schema=V.H_SCHEMA["scope"], h_slot_name=put(atoms, V.atom_utf8(f"{SCOPE}/SCOPE")),
                h_payload=put(atoms, V.atom_utf8(SCOPE)), slots=(pol, pol, V.H_LENS_KERNEL))
    return atoms, [*V.STD_SCHEMAS.values(), s0], [V.Seal.sign(SK, s0.id, s0.id)], s0


class Shape:
    def __init__(self, edges: bool, k: int, s0: V.Cell) -> None:
        self.edges, self.k, self.s0 = edges, k, s0
        self.prev: list[bytes] = []
        self.head: bytes | None = None

    def commit_body(self, i: int) -> tuple[dict[bytes, bytes], list, list]:
        atoms: dict[bytes, bytes] = {}
        cells = []
        for j in range(self.k):
            kw = {}
            name = f"{SCOPE}/c{i}.a{j}"
            if self.edges and self.prev:
                kw["h_relies"] = put(atoms, V.atom_hvec(sorted(self.prev)))
            if self.edges and j == 0:
                name = f"{SCOPE}/head"
                if self.head is not None:
                    kw["h_supersedes"] = put(atoms, V.atom_hvec([self.head]))
                    kw["h_loss"] = put(atoms, V.atom_utf8(f"rebind head at {i}"))
            cells.append(V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=put(atoms, V.atom_utf8(name)),
                                h_payload=put(atoms, V.atom_utf8(f"claim {i}.{j}")), **kw))
        if self.edges:
            self.head = cells[0].id
        self.prev = [c.id for c in cells]
        return atoms, cells, [V.Seal.sign(SK, c.id, self.s0.id) for c in cells]


def forget_process_caches() -> None:
    """Drop the module-level Ed25519 memo (lru_cache), so a cold timing pays every signature check a new process
    would; seals the bench itself signed are not counted as verified."""
    mv = sys.modules.get("minds_verify")
    for f in (getattr(mv, n, None) for n in ("_ed_dec", "ed25519_verify")):
        if f is not None and hasattr(f, "cache_clear"):
            f.cache_clear()


def timed(f) -> float:
    t = time.perf_counter()
    f()
    return time.perf_counter() - t


def run(shape_name: str) -> list[dict]:
    rows = []
    tmp = Path(tempfile.mkdtemp(prefix="vars-bench-"))
    try:
        subprocess.run(["git", "-C", str(tmp), "init", "-q"], check=True)
        b = Builder(tmp)
        atoms, cells, seals, s0 = genesis()
        b.advance(b.commit(atoms, cells, seals))
        shape = Shape(shape_name == "edges", args.per_commit, s0)
        length = 1  # commits on the chain, genesis included
        for target in sorted(args.lengths):
            while length < target:
                b.advance(b.commit(*shape.commit_body(length)))
                length += 1
            # cold: a fresh process-like instance admits one commit and computes the lens
            forget_process_caches()
            repo = V.GitVarsRepo(tmp)
            cand = b.commit(*shape.commit_body(length))
            admit_cold = timed(lambda: repo.admit_and_advance(SCOPE, cand, b.tip))
            b.tip = cand
            length += 1
            forget_process_caches()
            lens_cold = timed(lambda: V.GitVarsRepo(tmp).lens(SCOPE))  # a fresh instance: nothing cached
            # warm: the same instance admits the next commit and computes the lens again
            cand = b.commit(*shape.commit_body(length))
            admit_warm = timed(lambda: repo.admit_and_advance(SCOPE, cand, b.tip))
            b.tip = cand
            length += 1
            lens_warm = timed(lambda: repo.lens(SCOPE))
            row = {"shape": shape_name, "commits": target, "admit_cold_s": round(admit_cold, 3),
                   "lens_cold_s": round(lens_cold, 3), "admit_warm_s": round(admit_warm, 3),
                   "lens_warm_s": round(lens_warm, 3)}
            rows.append(row)
            print(f"{shape_name:9} {target:5} commits  admit {admit_cold:7.3f} s cold {admit_warm:7.3f} s warm"
                  f"   lens {lens_cold:7.3f} s cold {lens_warm:7.3f} s warm", flush=True)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return rows


results = []
for name in (["edgeless", "edges"] if args.shape == "both" else [args.shape]):
    results += run(name)
if args.json:
    Path(args.json).write_text(json.dumps({"root": str(Path(args.root).resolve()), "rows": results}, indent=1) + "\n")
