#!/usr/bin/env python3
"""Tests of `fold.py` (fold-candidates).

    .venv/bin/python experiments/decisions/test_decisions.py [-v]

Test 01 builds one chain through the gate and a batch of candidate readings of events on it, and checks what the
fold says of each against what the readings do: which statuses each changes, which act alike, where two classes
part, which the gate refuses. Every reading the gate answers is held to the frame filter: a cell it changes is one
the filter dirtied (`delta.dirty`). Test 02 does the same on the live chain, 100 readings, and checks the time.
"""
import hashlib
import json
import os
import random
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))
import vars1 as V  # noqa: E402
import fold as F  # noqa: E402

SCOPE = "proj"
MEMBERS = ("ana", "bo", "cy")


class Chain:
    """A small chain through the gate: a 1-of-3 roster, every cell sealed by whoever files it."""

    def __init__(self) -> None:
        self.path = Path(tempfile.mkdtemp(prefix="decisions-"))
        subprocess.run(["git", "init", "-q", str(self.path)], check=True)
        for k, v in (("user.name", "decisions"), ("user.email", "decisions@local"), ("gc.auto", "0")):
            subprocess.run(["git", "-C", str(self.path), "config", k, v], check=True)
        self.repo = V.GitVarsRepo(self.path)
        self.sk = {m: hashlib.sha256(b"decisions/" + m.encode()).digest() for m in (*MEMBERS, "dee")}
        self.pk = {m: V.ed25519_pubkey(s) for m, s in self.sk.items()}
        a = dict(V.STD_SCHEMA_ATOMS)
        adm = self.pol(a, 1, MEMBERS)
        self.scope = V.Cell(V.H_SCHEMA["scope"], self.put(a, V.atom_utf8(f"{SCOPE}/SCOPE")),
                            self.put(a, V.atom_utf8(SCOPE)), slots=(adm, adm, V.H_LENS_KERNEL))
        self.tip = self.repo.build_candidate_commit(SCOPE, a, [*V.STD_SCHEMAS.values(), self.scope],
                                                    [V.Seal.sign(self.sk["ana"], self.scope.id, self.scope.id)],
                                                    parent_commit=None)
        self.repo.admit_and_advance(SCOPE, self.tip, expected_old=None)
        self.atoms = {}

    @staticmethod
    def put(a, raw: bytes) -> bytes:
        a[V.sha256(raw)] = raw
        return V.sha256(raw)

    def pol(self, a, thr: int, members) -> bytes:
        return self.put(a, V.atom_pol1(thr, self.put(a, V.atom_hvec(sorted(self.pk[m] for m in members)))))

    def axiom(self, name: str, relies=()) -> V.Cell:
        extra = {"h_relies": self.put(self.atoms, V.atom_hvec(sorted(c.id for c in relies)))} if relies else {}
        return V.Cell(V.H_SCHEMA["axiom"], self.put(self.atoms, V.atom_utf8(f"{SCOPE}/{name}")),
                      self.put(self.atoms, V.atom_utf8(name)), **extra)

    def decision(self, name: str, thr: int, relies=()) -> V.Cell:
        extra = {"h_relies": self.put(self.atoms, V.atom_hvec(sorted(c.id for c in relies)))} if relies else {}
        return V.Cell(V.H_SCHEMA["decision"], self.put(self.atoms, V.atom_utf8(f"{SCOPE}/{name}")),
                      self.put(self.atoms, V.atom_utf8(name)),
                      slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, self.pol(self.atoms, thr, MEMBERS)), **extra)

    def verdict(self, on: V.Cell, name: str, verifier: str) -> V.Cell:
        self.atoms[V.H_ATTESTED] = V.atom_utf8("ATTESTED")
        return V.Cell(V.H_SCHEMA["verdict"], self.put(self.atoms, V.atom_utf8(f"{SCOPE}/{name}")), on.id,
                      h_attests=self.put(self.atoms, V.atom_hvec([on.id])),
                      slots=(V.H_EMPTY, V.H_ATTESTED, self.put(self.atoms, V.atom_utf8(verifier))))

    def commit(self, *pairs) -> None:
        seals = [V.Seal.sign(self.sk[m], c.id, self.scope.id) for c, m in pairs]
        tip = self.repo.build_candidate_commit(SCOPE, self.atoms, [c for c, _ in pairs], seals, parent_commit=self.tip)
        self.repo.admit_and_advance(SCOPE, tip, expected_old=self.tip)
        self.tip, self.atoms = tip, {}


def flips_within_dirty(test, out) -> None:
    """Every cell a reading changes, by the gate, is one the frame filter dirtied."""
    for row in out["candidates"]:
        if row["flips"]:
            test.assertLessEqual(set(row["flips"]), set(row["dirty_cells"]), row["id"])


class T(unittest.TestCase):
    def test_01_candidates_fold_into_classes_by_what_they_change(self):
        """A decision d (2 of 3) that ana's verdict attests and a decision e (1 of 3) that cy's verdict settles; a
        ground g that d relies on; an axiom x nothing reads. Readings: bo attests d (A), bo seals ana's verdict (B):
        both settle and ground d, one class. ana invalidates g (C), a comment (D), bo seals x (E): nothing that
        Settled or Grounded reads moves, one class, and E dirties no frame, so the filter alone knows it changes
        nothing. ana invalidates cy's verdict (C2), cy withdraws its own (G): both unsettle e, one class. A key off
        the roster seals x (F): refused. bo attests d and ana invalidates cy's verdict at once (H): it parts from A's
        class on e alone, though both change d."""
        c = Chain()
        g, x = c.axiom("ground/g"), c.axiom("other/x")
        d, e = c.decision("decision/d", 2, [g]), c.decision("decision/e", 1)
        c.commit((g, "ana"), (x, "ana"), (d, "ana"), (e, "cy"))
        va, ve = c.verdict(d, "decision/d/by-ana", "ana"), c.verdict(e, "decision/e/by-cy", "cy")
        c.commit((va, "ana"), (ve, "cy"))
        lens = c.repo.lens(SCOPE)
        self.assertEqual([lens["settled"][d.id], lens["settled"][e.id]], [False, True])
        pk = lambda m: c.pk[m].hex()  # noqa: E731
        hx = lambda cell: cell.id.hex()  # noqa: E731
        cands = [
            {"id": "A", "keys": [pk("bo")], "acts": [{"act": "verdict", "on": hx(d), "code": "ATTESTED", "verifier": "bo"}]},
            {"id": "B", "keys": [pk("bo")], "acts": [{"act": "seal", "target": hx(va)}]},
            {"id": "C", "keys": [pk("ana")], "acts": [{"act": "notice", "edge": "invalidates", "target": hx(g)}]},
            {"id": "C2", "keys": [pk("ana")], "acts": [{"act": "notice", "edge": "invalidates", "target": hx(ve)}]},
            {"id": "D", "keys": [pk("ana")], "acts": [{"act": "none"}]},
            {"id": "E", "keys": [pk("bo")], "acts": [{"act": "seal", "target": hx(x)}]},
            {"id": "F", "keys": [c.pk["dee"].hex()], "acts": [{"act": "seal", "target": hx(x)}]},
            {"id": "G", "keys": [pk("cy")], "acts": [{"act": "verdict", "on": hx(e), "code": "INVALID", "verifier": "cy"}]},
            {"id": "H", "keys": [pk("bo"), pk("ana")],
             "acts": [{"act": "verdict", "on": hx(d), "code": "ATTESTED", "verifier": "bo"},
                      {"act": "notice", "edge": "invalidates", "target": hx(ve)}]},
        ]
        out = F.fold_candidates(c.repo, SCOPE, F.read_candidates(json.dumps({"format": F.FORMAT, "candidates": cands}).encode()))
        rows = {r["id"]: r for r in out["candidates"]}
        self.assertEqual({k: (r["flipped_settled"], r["flipped_grounded"]) for k, r in rows.items()}, {
            "A": ([hx(d)], [hx(d)]), "B": ([hx(d)], [hx(d)]), "C": ([], []), "C2": ([hx(e)], [hx(e)]), "D": ([], []),
            "E": ([], []), "F": ([], []), "G": ([hx(e)], [hx(e)]), "H": (sorted([hx(d), hx(e)]), sorted([hx(d), hx(e)]))})
        self.assertEqual(sorted(sorted(k["members"]) for k in out["classes"]),
                         [["A", "B"], ["C", "D", "E"], ["C2", "G"], ["F"], ["H"]])
        self.assertEqual((rows["F"]["admissible"], rows["E"]["admissible"]), (False, True))
        self.assertEqual((rows["E"]["dirty"], rows["E"]["read"], rows["A"]["read"]), (0, "frame", "gate"))
        cls = {r["id"]: r["class"] for r in out["candidates"]}
        disc = {tuple(sorted(x["classes"])): x["cells"] for x in out["discriminating"]}
        self.assertEqual(disc[tuple(sorted((cls["A"], cls["C"])))], [hx(d)])
        self.assertEqual(disc[tuple(sorted((cls["A"], cls["C2"])))], sorted([hx(d), hx(e)]))
        self.assertEqual(disc[tuple(sorted((cls["A"], cls["H"])))], [hx(e)])
        flips_within_dirty(self, out)
        # without the gate the filter alone answers for E and the comment, and leaves the rest unread
        bare = {r["id"]: r for r in F.fold_candidates(c.repo, SCOPE, cands, gate=False)["candidates"]}
        self.assertEqual({k: (r["read"], r["flips"]) for k, r in bare.items() if k in ("D", "E", "A")},
                         {"D": ("empty", {}), "E": ("frame", {}), "A": ("unread", None)})

    def test_02_the_live_chain_folds_a_hundred_readings(self):
        """On refs/vars/heads/minds: 100 readings of roster keys (an attestation, a seal on a verdict, a notice, a
        comment), each read by the frame filter and the gate. Every change the gate finds is in the filter's dirty
        set; the filter takes under a second for all. With MINDS_FOLD_STATS=1 it prints the classes and the time.
        Skipped when the chain is not fetched, unless MINDS_REQUIRE_CHAIN=1."""
        repo = V.GitVarsRepo(ROOT)
        if repo.ref_commit("minds") is None:
            if os.environ.get("MINDS_REQUIRE_CHAIN") == "1":
                self.fail("refs/vars/heads/minds is not fetched, and MINDS_REQUIRE_CHAIN=1 requires it")
            self.skipTest("refs/vars/heads/minds is not fetched in this clone")
        lens = repo.lens("minds")
        cells, atoms = lens["cells"], lens["atoms"]
        keys = sorted(V.parse_hvec(atoms[V.parse_pol1(atoms[cells[lens["scope"]].slots[0]])[1]], require_sorted=True))
        ds = sorted(x for x, y in cells.items() if y.h_schema == V.H_SCHEMA["decision"])
        vs = sorted(x for x, y in cells.items() if y.h_schema == V.H_SCHEMA["verdict"])
        rnd = random.Random(7)
        cands = []
        for i in range(100):
            kind = i % 4
            acts = [[{"act": "verdict", "on": rnd.choice(ds).hex(), "code": "ATTESTED", "verifier": f"fold/{i}"}],
                    [{"act": "seal", "target": rnd.choice(vs).hex()}],
                    [{"act": "notice", "edge": "invalidates", "target": rnd.choice(vs + ds).hex()}],
                    [{"act": "none"}]][kind]
            cands.append({"id": f"c{i}", "keys": [rnd.choice(keys).hex()], "acts": acts})
        out = F.fold_candidates(repo, "minds", cands)
        flips_within_dirty(self, out)
        self.assertLess(out["timing"]["filter_s"], 1.0, out["timing"])
        if os.environ.get("MINDS_FOLD_STATS"):
            print(json.dumps({"timing": out["timing"], "classes": [len(k["members"]) for k in out["classes"]],
                              "dirty": sorted(r["dirty"] for r in out["candidates"])}))


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], *sys.argv[1:]], verbosity=1)
