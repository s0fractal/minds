"""Tests of the witness spike (README.md). Run from the repository root:

    .venv/bin/python experiments/witness/test_witness.py              # the tests
    .venv/bin/python experiments/witness/test_witness.py --mutants    # each mutant in mutants.json must fail its test
    .venv/bin/python experiments/witness/test_witness.py --mutants ID...   # the named ones

A mutant must fail its named test on an assertion (an error is not a kill), and the named tests must pass unmutated
first. Chains are built through the real gate (vars1.py); the checker under test is check.py, or the file named by
WITNESS_SOURCE (a mutant); the frame under test (tests 17-19) is frame.py, or the file named by FRAME_SOURCE; the
committed reverse index (tests 21-24) is revindex.py, or the file named by REVINDEX_SOURCE.
"""
import collections
import contextlib
import hashlib
import importlib.util
import io
import itertools
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))
import vars1 as V  # noqa: E402
import histories as HI  # noqa: E402
import prove as PR  # noqa: E402


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


SOURCE = Path(os.environ.get("WITNESS_SOURCE", HERE / "check.py"))
CK = _load("witness_check", SOURCE)
FR = _load("witness_frame", Path(os.environ.get("FRAME_SOURCE", HERE / "frame.py")))
RX = _load("witness_revindex", Path(os.environ.get("REVINDEX_SOURCE", HERE / "revindex.py")))
LIVE_TIP = "7c6899b7cf8d1bc5bf68c4f53446251b3e90a69d"  # refs/vars/heads/minds on 2026-11-07: test 19's named tip
LEAN = ROOT / "proofs" / ".lake" / "build" / "bin" / "vars1witness"
WORK = Path.home() / "Projects" / ".worktrees" / "witness-work"
WORK.mkdir(parents=True, exist_ok=True)
MEMBERS = ("ana", "bo", "cy")
SCOPE = "proj"
MUTATED = {"check.py": "WITNESS_SOURCE", "frame.py": "FRAME_SOURCE", "revindex.py": "REVINDEX_SOURCE"}  # the files mutants.json mutates, and how a test takes a copy
_CACHE = {}


def held(path, term, pin=None):
    """check.py's answer on a term. Where the Lean checker is built, and wherever MINDS_REQUIRE_LEAN=1, the same term
    also goes through `check.py --lean` to `vars1witness`, and the two must agree: ACCEPT exactly when HELD."""
    r = CK.check(str(path), term, pin)
    if LEAN.exists() or os.environ.get("MINDS_REQUIRE_LEAN") == "1":
        assert LEAN.exists(), "MINDS_REQUIRE_LEAN=1, but proofs/.lake/build/bin/vars1witness is not built"
        try:
            line = CK.lean_line(str(path), term, pin)
        except CK.Refused:
            lean = "REFUSED"
        else:
            lean = subprocess.run([str(LEAN)], input=line + "\n", capture_output=True, text=True,
                                  check=True).stdout.strip()
        assert lean in ("ACCEPT", "REJECT", "REFUSED"), lean
        assert (lean == "ACCEPT") == (r["result"] == "HELD"), f"Lean {lean}, check.py {r}"
    return r


def scratch() -> Path:
    return Path(tempfile.mkdtemp(dir=WORK))


class Chain:
    """A hand-built chain admitted through the gate: genesis sealed by ana, every cell sealed by whoever files it."""

    def __init__(self, path: Path, rules: bytes = V.H_LENS_KERNEL, admission=(1, MEMBERS)) -> None:
        subprocess.run(["git", "init", "-q", str(path)], check=True)
        for k, v in (("user.name", "witness"), ("user.email", "witness@local"), ("gc.auto", "0")):
            subprocess.run(["git", "-C", str(path), "config", k, v], check=True)
        self.path, self.repo = path, V.GitVarsRepo(path)
        self.sk = {m: hashlib.sha256(b"witness/" + m.encode()).digest() for m in (*MEMBERS, "dee")}
        self.pk = {m: V.ed25519_pubkey(s) for m, s in self.sk.items()}
        a = dict(V.STD_SCHEMA_ATOMS)
        if rules == V.H_LENS_KERNEL_V2:
            a[rules] = V.KERNEL2_ATOM
        adm = self.pol(a, *admission)
        self.scope = V.Cell(V.H_SCHEMA["scope"], self.put(a, V.atom_utf8(f"{SCOPE}/SCOPE")),
                            self.put(a, V.atom_utf8(SCOPE)), slots=(adm, adm, rules))
        self.tip = self.repo.build_candidate_commit(SCOPE, a, [*V.STD_SCHEMAS.values(), self.scope],
                                                    [V.Seal.sign(self.sk[m], self.scope.id, self.scope.id)
                                                     for m in admission[1][:admission[0]]],
                                                    parent_commit=None)
        self.repo.admit_and_advance(SCOPE, self.tip, expected_old=None)
        self.ctx, self.atoms = self.scope.id, {}

    def put(self, a, raw: bytes) -> bytes:
        a[V.sha256(raw)] = raw
        return V.sha256(raw)

    def hv(self, ids) -> bytes:
        return self.put(self.atoms, V.atom_hvec(sorted(ids)))

    def pol(self, a, thr: int, members) -> bytes:
        return self.put(a, V.atom_pol1(thr, self.put(a, V.atom_hvec(sorted(self.pk[m] for m in members)))))

    def utf8(self, text: str) -> bytes:
        return self.put(self.atoms, V.atom_utf8(text))

    def _edges(self, relies, edges):
        out = {"h_relies": self.hv([c.id for c in relies])} if relies else {}
        for k, v in edges.items():
            out[f"h_{k}"] = self.hv([c.id for c in v])
        if "supersedes" in edges or "retires" in edges:
            out["h_loss"] = self.utf8("replaced")
        return out

    def axiom(self, name: str, relies=(), **edges) -> V.Cell:
        return V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=self.utf8(f"{SCOPE}/{name}"),
                      h_payload=self.utf8(name), **self._edges(relies, edges))

    def decision(self, name: str, relies, thr: int = 2, members=MEMBERS, **edges) -> V.Cell:
        return V.Cell(h_schema=V.H_SCHEMA["decision"], h_slot_name=self.utf8(f"{SCOPE}/{name}"),
                      h_payload=self.utf8(name), **self._edges(relies, edges),
                      slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, self.pol(self.atoms, thr, members)))

    def verdict(self, decision: V.Cell, name: str, relies=(), code: bytes = V.H_ATTESTED, attests=None,
                verifier: str = "v") -> V.Cell:
        return V.Cell(h_schema=V.H_SCHEMA["verdict"], h_slot_name=self.utf8(f"{SCOPE}/{name}"),
                      h_payload=decision.id, h_attests=self.hv([(attests or decision).id]),
                      **self._edges(relies, {}), slots=(V.H_EMPTY, code, self.utf8(verifier)))

    def commit(self, *pairs) -> str:
        """Admit cells, each sealed by the named member(s) under the governing scope."""
        cells = [c for c, _ in pairs]
        seals = [V.Seal.sign(self.sk[m], c.id, self.ctx) for c, ms in pairs for m in ((ms,) if isinstance(ms, str) else ms)]
        tip = self.repo.build_candidate_commit(SCOPE, self.atoms, cells, seals, parent_commit=self.tip)
        self.repo.admit_and_advance(SCOPE, tip, expected_old=self.tip)
        self.tip, self.atoms = tip, {}
        return tip

    def seal(self, cell: V.Cell, member: str) -> str:
        """Admit a seal by `member` on a cell the chain already holds, under the governing scope, and nothing else."""
        tip = self.repo.build_candidate_commit(SCOPE, {}, [], [V.Seal.sign(self.sk[member], cell.id, self.ctx)],
                                               parent_commit=self.tip)
        self.repo.admit_and_advance(SCOPE, tip, expected_old=self.tip)
        self.tip = tip
        return tip

    def owned(self, name: str, relies, thr: int, members=MEMBERS) -> V.Cell:
        """A decision of tier owner: its own policy evaluates it, and the admission policy governs its edges."""
        return V.Cell(h_schema=V.H_SCHEMA["decision"], h_slot_name=self.utf8(f"{SCOPE}/{name}"),
                      h_payload=self.utf8(name), **self._edges(relies, {}),
                      slots=(V.H_OWNER, V.H_EMPTY, V.H_EMPTY, self.pol(self.atoms, thr, members)))

    def basic(self):
        """ground g -> check k -> decision d (2 of 3), approved by ana, bo and cy, each relying on k."""
        g = self.axiom("ground/g")
        self.commit((g, "ana"))
        k = self.axiom("check/k", [g])
        self.commit((k, "bo"))
        d = self.decision("decision/d", [k])
        vs = {m: self.verdict(d, f"decision/d/by-{m}", [k], verifier=m) for m in MEMBERS}
        self.commit((d, "ana"), *((v, m) for m, v in vs.items()))
        return g, k, d, vs

    def check(self, term, pin=None):
        return held(self.path, term, pin)

    def rotate(self, members, label: str, rules=None, sealer: str = "ana") -> V.Cell:
        """Admit a new scope cell superseding the governing one, with `members` 1-of-n in both rosters, sealed by
        `sealer` under the governing scope; it governs from the next commit unless its rotation waits."""
        a = self.atoms
        pol = self.pol(a, 1, members)
        old = self.repo.read_cas_tree(self.tip)[1][self.ctx]
        s1 = V.Cell(V.H_SCHEMA["scope"], self.put(a, V.atom_utf8(f"{SCOPE}/SCOPE")), self.put(a, V.atom_utf8(label)),
                    h_supersedes=self.put(a, V.atom_hvec([self.ctx])), h_loss=self.put(a, V.atom_utf8(label)),
                    slots=(pol, pol, rules or old.slots[2]))
        self.commit((s1, sealer))
        return s1

    def governing(self) -> bytes:
        return self.repo._evaluate_commit_chain(SCOPE, self.repo.commit_chain(self.tip))["active_scope_id"]


def seals_on(repo: V.GitVarsRepo, tip: str, cid: bytes):
    return sorted(sid for sid, s in repo.read_cas_tree(tip)[2].items() if s.h_target == cid)


def closure(repo: V.GitVarsRepo, tip: str, roots) -> list:
    atoms, cells, _ = repo.read_cas_tree(tip)
    out, todo = set(roots), list(roots)
    while todo:
        h = cells[todo.pop()].h_relies
        for r in ([] if h == V.H_EMPTY else V.parse_hvec(atoms[h], require_sorted=True)):
            if r not in out:
                out.add(r)
                todo.append(r)
    return sorted(out)


def term(repo, tip, decision: bytes, verdicts, cone=None, scope=SCOPE) -> dict:
    """A term over the given verdicts, every seal of each counted, with their whole cone unless one is given."""
    return {"format": CK.FORMAT, "scope": scope, "tip": tip, "decision": decision.hex(),
            "cone": [x.hex() for x in (closure(repo, tip, [decision, *verdicts]) if cone is None else cone)],
            "endorsements": [{"verdict": w.hex(), "seal": s.hex()} for w in verdicts for s in seals_on(repo, tip, w)]}


def history_chain(i: int):
    """History i of the seed `witness` (S, L, S, ...), built by histories.py through the gate, before and after
    its failed ground's notice is admitted."""
    if i not in _CACHE:
        s, size = HI.seeds("witness", i + 1)[i]
        h = HI.history(s, size)
        path = scratch()
        ch = HI.build_chain(h, s, path)
        repo, before = ch["repo"], ch["repo"].ref_commit(HI.SCOPE)
        a = {}
        put = lambda raw: (a.__setitem__(V.sha256(raw), raw), V.sha256(raw))[1]  # noqa: E731
        notice = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=put(V.atom_utf8(f"{HI.SCOPE}/notice/{h['failed']}")),
                        h_payload=put(V.atom_utf8(f"{h['failed']} was found invalid")),
                        h_invalidates=put(V.atom_hvec([ch["ids"][h["failed"]]])))
        ctx = repo._evaluate_commit_chain(HI.SCOPE, repo.commit_chain(before))["active_scope_id"]
        after = repo.build_candidate_commit(HI.SCOPE, a, [notice], [V.Seal.sign(HI._key(s, ch["reporter"]), notice.id, ctx)],
                                            parent_commit=before)
        repo.admit_and_advance(HI.SCOPE, after, expected_old=before)
        _CACHE[i] = (h, ch, path, before, after)
    return _CACHE[i]


def verdicts_on(repo, tip, d: bytes):
    cells = repo.read_cas_tree(tip)[1]
    return sorted(w.id for w in cells.values() if w.h_schema == V.H_SCHEMA["verdict"] and w.h_payload == d)


def raw_commit(path: Path, parent: str, entries) -> str:
    """A commit adding (path, bytes) entries to `parent`'s tree, unchecked by any gate."""
    env = {**os.environ, "GIT_INDEX_FILE": str(path / ".git" / "witness-raw-index")}
    git = lambda *a, inp=None: subprocess.run(["git", "-C", str(path), *a], input=inp, env=env,  # noqa: E731
                                              capture_output=True, check=True).stdout.decode().strip()
    git("read-tree", parent)
    lines = []
    for p, raw in entries:
        oid = raw if isinstance(raw, str) else git("hash-object", "-w", "--stdin", inp=raw)
        lines.append(f"100644 {oid}\t{p}\n")
    git("update-index", "--add", "--index-info", inp="".join(lines).encode())
    return git("commit-tree", git("write-tree", "--missing-ok"), "-p", parent, "-m", "raw")


def cas(kind: str, raw: bytes):
    h = hashlib.sha256(raw).hexdigest()
    return f"cas/{kind}/{h[:2]}/{h[2:]}", raw


def lean_proves(path, tip, scope, d) -> bool:
    """`vars1witness --prove` on the store at `tip` for `d`, as `check.py --lean --prove` writes it: ACCEPT or not."""
    t = {"format": CK.FORMAT, "scope": scope, "tip": tip, "decision": d.hex(), "cone": [], "endorsements": []}
    try:
        line = CK.lean_line(str(path), t, None, prove=True)
    except CK.Refused:
        return False
    out = subprocess.run([str(LEAN), "--prove"], input=line + "\n", capture_output=True, text=True,
                         check=True).stdout.strip()
    assert out in ("ACCEPT", "REJECT"), out
    return out == "ACCEPT"


def lens_settles(c, d) -> bool:
    lens = c.repo.lens(SCOPE)
    return bool(lens["settled"].get(d.id) and lens["active"].get(d.id) and not lens["stale"].get(d.id))


def author_chain(late: bool):
    """g -> e -> d: e a decision whose own policy is 2 of 3, sealed by ana at its birth; d (2 of 3) approved by ana and
    bo; a cell w that retires e, sealed by one key. Its quorum fails; the author clause latches it when that key is one
    of e's initial endorsers. With `late`, bo seals e after its birth and w is bo's: bo is no initial endorser, so the
    edge does not latch and the lens settles d; otherwise w is ana's and e is Retired. Either way some key seals both e
    and w, which is all the store at the tip shows: the checkers cannot tell the two apart."""
    c = Chain(scratch())
    g = c.axiom("ground/g")
    c.commit((g, "ana"))
    e = c.decision("decision/e", [g], thr=2)
    c.commit((e, "ana"))
    if late:
        c.seal(e, "bo")
    d = c.decision("decision/d", [e], thr=2)
    vs = {m: c.verdict(d, f"decision/d/by-{m}", [e], verifier=m) for m in ("ana", "bo")}
    c.commit((d, "ana"), *((v, m) for m, v in vs.items()))
    c.commit((c.axiom("retire/e", retires=[e]), "bo" if late else "ana"))
    return c, d, vs


def retired_invalid_chain():
    """g -> k -> d, d 3 of 3, approved by all three; cy's INVALID verdict under its own id relies on k, and a cell cy
    seals retires it. A retired verdict is not Active, so it withdraws nothing and the lens settles d; the checkers
    prove a verdict not live only through an Invalidated cell, so they cannot count cy's key."""
    c = Chain(scratch())
    g = c.axiom("ground/g")
    c.commit((g, "ana"))
    k = c.axiom("check/k", [g])
    c.commit((k, "bo"))
    d = c.decision("decision/d", [k], thr=3)
    vs = {m: c.verdict(d, f"decision/d/by-{m}", [k], verifier=m) for m in MEMBERS}
    c.commit((d, "ana"), *((v, m) for m, v in vs.items()))
    b = c.verdict(d, "decision/d/invalid-by-cy", [k], code=V.H_VERDICT_INVALID, verifier="cy")
    c.commit((b, "cy"))
    c.commit((c.axiom("retire/invalid", retires=[b]), "cy"))
    return c, d, vs


def stale_invalid_chain():
    """basic(), then two INVALID verdicts on d: bo's, under its own verifier id, relies on a ground a notice
    invalidates, so it is Stale and withdraws nothing; cy's, under its own, withdraws cy's endorsement. The lens
    settles d by ana and bo; that bo's INVALID verdict is not live is what no checker here derives."""
    c = Chain(scratch())
    g, k, d, vs = c.basic()
    h = c.axiom("ground/h")
    c.commit((h, "bo"))
    c.commit((c.verdict(d, "decision/d/invalid-by-bo", [h], code=V.H_VERDICT_INVALID, verifier="bo"), "bo"))
    c.commit((c.axiom("notice/h", invalidates=[h]), "ana"))
    c.commit((c.verdict(d, "decision/d/invalid-by-cy", [k], code=V.H_VERDICT_INVALID, verifier="cy"), "cy"))
    return c, d, vs


class FakeTip:
    """What frame.py and revindex.py read of a tip, over cells no gate admitted: for a shape no chain here has."""

    def __init__(self, cells, atoms) -> None:
        self.V, self.cells, self.atoms, self.seals = V, {c.id: c for c in cells}, atoms, {}
        self.tip, self.waiting, self.governing = "0" * 40, None, cells[0].id

    def hv(self, h: bytes):
        return [] if h == V.H_EMPTY else V.parse_hvec(self.atoms[h], require_sorted=True)

    def is_local(self, cid: bytes) -> bool:
        return True


def named_store():
    """A decision d; a checkpoint n; ana's verdict on d names n; bo's verdict names n and is on another cell, so it
    judges d only through n (frame.py: a verdict on a checkpoint one of d's verdicts names). No chain here holds a
    verdict naming a checkpoint, so these cells are built without the gate, for the frame's reading alone."""
    atoms = {}
    put = lambda raw: atoms.setdefault(hashlib.sha256(raw).digest(), raw) and hashlib.sha256(raw).digest()  # noqa: E731
    name = lambda s: put(V.atom_utf8(f"{SCOPE}/{s}"))  # noqa: E731
    pol = put(V.atom_pol1(1, put(V.atom_hvec([b"\x01" * 32]))))
    d = V.Cell(h_schema=V.H_SCHEMA["decision"], h_slot_name=name("decision/d"), h_payload=put(V.atom_utf8("d")),
               slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, pol))
    other = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=name("other"), h_payload=put(V.atom_utf8("o")))
    n = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=name("checkpoint/n"), h_payload=put(V.atom_utf8("n")))
    by = lambda who, on: V.Cell(h_schema=V.H_SCHEMA["verdict"], h_slot_name=name(f"verdict/{who}"),  # noqa: E731
                                h_payload=on.id, h_attests=put(V.atom_hvec([on.id])),
                                slots=(n.id, V.H_ATTESTED, put(V.atom_utf8(who))))
    ana, bo = by("ana", d), by("bo", other)
    return FakeTip([d, other, n, ana, bo], atoms), [d.id]


class T(unittest.TestCase):
    def test_01_ed25519_is_rfc8032_strict_and_cofactorless(self):
        """RFC 8032 §7.1 tests 1 and 2 verify, and vars1's own signatures verify; a changed message, S + L, a key of
        small order and a non-canonical point encoding do not."""
        for pub, msg, sig in (
            ("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a", "",
             "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"),
            ("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c", "72",
             "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00")):
            pub, msg, sig = bytes.fromhex(pub), bytes.fromhex(msg), bytes.fromhex(sig)
            self.assertTrue(CK.ed25519_verify(pub, msg, sig))
            self.assertFalse(CK.ed25519_verify(pub, msg + b"x", sig), "another message")
            s = int.from_bytes(sig[32:], "little") + CK.L
            self.assertFalse(CK.ed25519_verify(pub, msg, sig[:32] + s.to_bytes(32, "little")), "S + L is not canonical")
        for i in range(4):
            sk = hashlib.sha256(bytes([i])).digest()
            m = hashlib.sha256(bytes([i, i])).digest() * (i + 1)
            self.assertTrue(CK.ed25519_verify(V.ed25519_pubkey(sk), m, V.ed25519_sign(sk, m)), "vars1's signature")
        s = 12345
        forged = CK._encode(CK._mul(s, CK.B)) + s.to_bytes(32, "little")
        self.assertFalse(CK.ed25519_verify(CK._encode(CK.ZERO), b"any message", forged),
                         "under a key of small order, [S]B = R signs every message")
        self.assertIsNone(CK._decode((CK.P + 1).to_bytes(32, "little")), "y >= p is not a canonical encoding")

    def test_02_the_checker_uses_nothing_of_vars1(self):
        """check.py imports the standard library only, and its constants are the spec's, equal to vars1's."""
        import ast
        mods = {n.name.split(".")[0] for x in ast.walk(ast.parse((HERE / "check.py").read_text()))
                if isinstance(x, ast.Import) for n in x.names}
        mods |= {x.module.split(".")[0] for x in ast.walk(ast.parse((HERE / "check.py").read_text()))
                 if isinstance(x, ast.ImportFrom)}
        self.assertLessEqual(mods, {"hashlib", "json", "re", "subprocess", "sys", "typing"})
        self.assertEqual(CK.SCHEMA, {k: V.H_SCHEMA[k] for k in CK.SCHEMA})
        self.assertEqual(CK.STANDARD, {c.id for c in V.STD_SCHEMAS.values()})
        self.assertEqual((CK.H_EMPTY, CK.H_ATTESTED, CK.H_VERDICT_INVALID, CK.H_LENS_KERNEL, CK.H_META_SCHEMA,
                          CK.H_OWNER),
                         (V.H_EMPTY, V.H_ATTESTED, V.H_VERDICT_INVALID, V.H_LENS_KERNEL, V.H_META_SCHEMA, V.H_OWNER))

    def test_03_before_the_failure_every_decision_is_held(self):
        """On a history of each size, every decision in force before the notice gets a witness the checker holds."""
        for i in (0, 1):
            h, ch, path, before, _ = history_chain(i)
            for d in h["decisions"]:
                r = held(path, PR.prove(ch["repo"], HI.SCOPE, ch["ids"][d["id"]], before))
                self.assertEqual(r["result"], "HELD", (i, d["id"], r))

    def test_04_after_the_failure_held_only_what_the_lens_settles(self):
        """After the notice: a decision the lens settles gets a witness the checker holds, one it does not gets none;
        and no term over any subset of a decision's verdicts, each with its whole cone, is HELD for a decision the
        lens does not settle."""
        seen = set()
        for i in (0, 1):
            h, ch, path, _, after = history_chain(i)
            repo, lens = ch["repo"], ch["repo"].lens(HI.SCOPE)
            for dd in h["decisions"]:
                d = ch["ids"][dd["id"]]
                settled = bool(lens["settled"].get(d) and lens["active"].get(d) and not lens["stale"].get(d))
                if settled:
                    self.assertEqual(held(path, PR.prove(repo, HI.SCOPE, d, after))["result"], "HELD", dd)
                else:
                    with self.assertRaises(PR.NotHeld):
                        PR.prove(repo, HI.SCOPE, d, after)
                vs = verdicts_on(repo, after, d)
                for r in range(1, len(vs) + 1):
                    for sub in itertools.combinations(vs, r):
                        out = held(path, term(repo, after, d, sub))
                        seen.add((out["result"], out.get("code")))
                        if out["result"] == "HELD":
                            self.assertTrue(settled, (i, dd["id"], out))
        self.assertTrue({("REFUSED", "KILLED"), ("REFUSED", "THRESHOLD"), ("HELD", None)} <= seen, seen)
        self.assertFalse({x for x in seen if x[0] == "NOT_COVERED"}, "every edge of these histories is decided")

    def test_05_a_term_that_hides_part_of_its_cone_is_refused(self):
        """A lost decision cannot be passed off by leaving the fallen ground or a stale verdict out of the cone."""
        h, ch, path, _, after = history_chain(0)
        repo, kinds = ch["repo"], HI.kinds(h)
        fallen = ch["ids"][h["failed"]]
        own = next(ch["ids"][x] for x, k in kinds.items() if k == "own")
        cone = [x for x in closure(repo, after, [own, *verdicts_on(repo, after, own)]) if x != fallen]
        r = held(path, term(repo, after, own, verdicts_on(repo, after, own), cone=cone))
        self.assertEqual((r["result"], r.get("code")), ("REFUSED", "CONE_OPEN"))
        lost = next(ch["ids"][x] for x, k in kinds.items() if k == "approvals")
        vs = verdicts_on(repo, after, lost)
        r = held(path, term(repo, after, lost, vs, cone=closure(repo, after, [lost])))
        self.assertEqual((r["result"], r.get("code")), ("REFUSED", "CONE_OPEN"), "a stale verdict outside the cone")
        r = held(path, term(repo, after, own, verdicts_on(repo, after, own)))
        self.assertEqual((r["result"], r.get("code")), ("REFUSED", "KILLED"), "the whole cone holds the fallen ground")

    def test_06_a_wrong_term_is_refused_for_its_reason(self):
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        good = term(c.repo, c.tip, d.id, [vs["ana"].id, vs["bo"].id])
        self.assertEqual(c.check(good)["result"], "HELD")
        self.assertEqual(c.check(good, c.scope.id)["result"], "HELD")
        tag = subprocess.run(["git", "-C", str(c.path), "tag", "-a", "t", "-m", "t", c.tip], check=True)
        tag = subprocess.run(["git", "-C", str(c.path), "rev-parse", "t"], capture_output=True, text=True).stdout.strip()
        other = term(c.repo, c.tip, d.id, [vs["ana"].id, vs["bo"].id])
        other["endorsements"][1]["seal"] = seals_on(c.repo, c.tip, vs["cy"].id)[0].hex()
        cases = {
            "FORMAT": [dict(good, format="x"), dict(good, cone="x"), dict(good, endorsements=[{"verdict": 1}])],
            "TIP": [dict(good, tip=c.tip[:12]), dict(good, tip=tag)],
            "SCOPE": [dict(good, scope="other")],
            "DECISION": [dict(good, decision=k.id.hex())],
            "CONE_MISSING": [dict(good, cone=good["cone"] + ["ab" * 32])],
            "CONE_OPEN": [dict(good, cone=[x for x in good["cone"] if x != g.id.hex()]),
                          dict(good, cone=[x for x in good["cone"] if x != d.id.hex()]),
                          dict(good, cone=[x for x in good["cone"] if x != vs["bo"].id.hex()])],
            "VERDICT": [dict(good, endorsements=[{"verdict": k.id.hex(), "seal": e["seal"]} for e in good["endorsements"]])],
            "SEAL": [other],
            "THRESHOLD": [dict(good, endorsements=good["endorsements"][:1]),
                          dict(good, endorsements=good["endorsements"][:1] * 2)],
        }
        for code, terms in cases.items():
            for t in terms:
                r = c.check(t)
                self.assertEqual((r["result"], r.get("code")), ("REFUSED", code), (code, r))
        r = c.check(good, hashlib.sha256(b"another scope").digest())
        self.assertEqual((r["result"], r.get("code")), ("REFUSED", "SCOPE"), "the reader's pin")

    def test_07_only_ATTESTED_verdicts_on_the_decision_by_its_policy_keys_count(self):
        """A verdict judging another decision, one that attests another, one that judges another but attests this
        one, one NOT_ASSESSED, a cell of a custom schema shaped like a verdict, and a key of the roster outside the
        decision's evaluator policy count nothing; the prover's witness uses ana and bo."""
        c = Chain(scratch())
        g = c.axiom("ground/g")
        c.commit((g, "ana"))
        d = c.decision("decision/d", [g], thr=2, members=("ana", "bo"))
        e = c.decision("decision/e", [g], thr=1, members=("ana",))
        ana, bo, cy = (c.verdict(d, f"decision/d/by-{m}", [g]) for m in MEMBERS)
        on_e = c.verdict(e, "decision/e/by-bo", [g])
        side = c.verdict(d, "decision/d/sideways", [g], attests=e)
        crossed = c.verdict(e, "decision/e/crossed", [g], attests=d)
        na = c.verdict(d, "decision/d/not-assessed", [g], code=V.H_NOT_ASSESSED)
        shaped_schema = V.Cell(h_schema=V.H_META_SCHEMA, h_slot_name=c.utf8(f"{SCOPE}/schema/shaped"),
                               h_payload=V.H_EMPTY, slots=tuple(c.utf8(f"{n}:utf8") for n in "abc"))
        shaped = V.Cell(h_schema=shaped_schema.id, h_slot_name=c.utf8(f"{SCOPE}/decision/d/shaped"), h_payload=d.id,
                        h_attests=c.hv([d.id]), slots=(c.utf8("x"), V.H_ATTESTED, c.utf8("y")))
        c.commit((d, "ana"), (e, "ana"), (ana, "ana"), (bo, "bo"), (cy, "cy"), (on_e, "bo"), (side, "bo"),
                 (crossed, "bo"), (na, "bo"), (shaped_schema, "ana"), (shaped, "bo"))
        self.assertEqual(c.check(PR.prove(c.repo, SCOPE, d.id))["endorsers"], sorted(c.pk[m].hex() for m in ("ana", "bo")))
        for w, code in ((on_e, "VERDICT"), (side, "VERDICT"), (crossed, "VERDICT"), (na, "VERDICT"),
                        (shaped, "VERDICT"), (cy, "KEY")):
            r = c.check(term(c.repo, c.tip, d.id, [ana.id, w.id]))
            self.assertEqual((r["result"], r.get("code")), ("REFUSED", code), (code, r))

    def test_08_outside_the_fragment_the_answer_is_not_covered(self):
        """Outside the fragment the answer is NOT_COVERED: an edge into the cone whose quorum fails while a key of its
        target seals its source (the author clause reads the target's initial endorsers, which the store at the tip does
        not show), whether it latched or not; an INVALID verdict that would withdraw a named key and is retired; a
        rotation that may wait (under v2 it drops a key without that key's seal); rules other than v1 and v2; two scope
        cells that supersede one."""
        for late in (False, True):
            c, d, vs = author_chain(late)
            self.assertEqual(lens_settles(c, d), late, "the lens: Retired by the author clause, unless bo sealed e late")
            r = c.check(term(c.repo, c.tip, d.id, [v.id for v in vs.values()]))
            self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "LATCH"), (late, r))

        c, d, vs = retired_invalid_chain()
        self.assertTrue(lens_settles(c, d), "cy's INVALID verdict is retired: all three keys count")
        r = c.check(PR.prove(c.repo, SCOPE, d.id))
        self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "INVALID_VERDICT"), r)

        c = Chain(scratch(), rules=V.H_LENS_KERNEL_V2)
        g, k, d, vs = c.basic()
        s1 = c.rotate(("ana", "bo"), "cy leaves")  # under v2, without cy's seal: it waits (§4.1 latch 4a)
        self.assertEqual(c.governing(), c.scope.id, "the rotation waits")
        self.assertTrue(c.repo.lens(SCOPE)["settled"].get(d.id))
        for pin in (None, c.scope.id):
            r = c.check(PR.prove(c.repo, SCOPE, d.id), pin)
            self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "WAITING"), (pin, r))

        c = Chain(scratch())
        g, k, d, vs = c.basic()
        a = {}
        pol = c.pol(a, 1, MEMBERS)
        name = c.put(a, V.atom_utf8(f"{SCOPE}/SCOPE"))
        others = [V.Cell(V.H_SCHEMA["scope"], name, c.put(a, V.atom_utf8(label)),
                         h_supersedes=c.put(a, V.atom_hvec([c.scope.id])), h_loss=c.put(a, V.atom_utf8(label)),
                         slots=(pol, pol, rules)) for label, rules in (("other rules", V.sha256(b"other rules")),
                                                                       ("v1 again", V.H_LENS_KERNEL))]
        t = term(c.repo, c.tip, d.id, [vs["ana"].id, vs["bo"].id])
        for cells, code in (([others[0]], "RULES"), (others, "SCOPES")):  # unadmitted stores: no gate ran on them
            tip = raw_commit(c.path, c.tip, [*(cas("cells", x.encode()) for x in cells),
                                             *(cas("atoms", x) for x in a.values())])
            r = c.check(dict(t, tip=tip))
            self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", code), r)

    def test_09_the_store_is_read_from_bytes(self):
        """Objects the gate never saw: a seal that does not verify, a seal under another scope, bytes that do not hash
        to their name, a missing object, an entry outside cas/, a computation-requiring decision and a foreign cell."""
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        good = term(c.repo, c.tip, d.id, [vs["ana"].id, vs["bo"].id])
        real = c.repo.read_cas_tree(c.tip)[2][bytes.fromhex(good["endorsements"][1]["seal"])]
        flipped = real.encode()[:-1] + bytes([real.encode()[-1] ^ 1])
        moved = V.Seal.sign(c.sk["bo"], vs["bo"].id, hashlib.sha256(b"another scope").digest()).encode()

        def with_seal(raw):
            tip = raw_commit(c.path, c.tip, [cas("seals", raw)])
            t = dict(good, tip=tip, endorsements=[good["endorsements"][0], {"verdict": vs["bo"].id.hex(),
                                                                            "seal": hashlib.sha256(raw).hexdigest()}])
            return c.check(t)
        for raw, why in ((flipped, "does not verify"), (moved, "another scope")):
            r = with_seal(raw)
            self.assertEqual((r["result"], r.get("code")), ("REFUSED", "SEAL"), why)
            self.assertIn(why, r["detail"])
        p, _ = cas("atoms", b"UTF8true")
        for entries in ([(p, b"UTF8false")], [(p, "e" * 40)], [("README", b"hello")]):
            r = c.check(dict(good, tip=raw_commit(c.path, c.tip, entries)))
            self.assertEqual((r["result"], r.get("code")), ("REFUSED", "STORE"), (entries[0][0], r))
        a = {}
        forged = V.Cell(h_schema=V.H_SCHEMA["decision"], h_slot_name=c.put(a, V.atom_utf8(f"{SCOPE}/decision/x")),
                        h_payload=c.put(a, V.atom_utf8("x")), slots=(V.H_PROVISIONAL, d.id, V.H_EMPTY, V.H_EMPTY))
        tip = raw_commit(c.path, c.tip, [cas("cells", forged.encode()), *(cas("atoms", x) for x in a.values())])
        r = c.check(dict(good, tip=tip, decision=forged.id.hex(), cone=[forged.id.hex()], endorsements=[]))
        self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "COMPUTATION"), r)
        a = {}
        stranger = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=c.put(a, V.atom_utf8("other/x")),
                          h_payload=c.put(a, V.atom_utf8("x")))
        tip = raw_commit(c.path, c.tip, [cas("cells", stranger.encode()), *(cas("atoms", x) for x in a.values())])
        r = c.check(dict(good, tip=tip))
        self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "FOREIGN"), r)

    def test_10_the_checker_runs_alone(self):
        """check.py copied alone into an empty folder, run with -I, holds a witness and refuses another scope pin."""
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        folder = scratch()
        shutil.copy(SOURCE, folder / "check.py")
        (folder / "term.json").write_text(json.dumps(PR.prove(c.repo, SCOPE, d.id)))
        run = lambda *a: subprocess.run([sys.executable, "-I", "check.py", str(c.path), "term.json", *a],  # noqa: E731
                                        cwd=folder, capture_output=True, text=True)
        r = run("--scope-cell", c.scope.id.hex())
        self.assertEqual((r.returncode, json.loads(r.stdout)["result"]), (0, "HELD"), r.stderr)
        r = run("--scope-cell", "00" * 32)
        self.assertEqual((r.returncode, json.loads(r.stdout)["code"]), (1, "SCOPE"), r.stderr)

    def test_11_a_term_reads_one_way_and_a_crash_is_no_verdict(self):
        """Decision 0008 of open-ontologies: an object that names a key twice has two readings (Python keeps the last
        value, other readers the first), so the term is refused rather than read by one convention; so is a term that
        is not UTF-8 JSON. A crash of the checker exits 3, which no verdict uses."""
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        t = PR.prove(c.repo, SCOPE, d.id)
        text = json.dumps(t)
        f = scratch() / "term.json"

        def cli(raw):
            f.write_bytes(raw)
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                rc = CK.main([str(c.path), str(f)])
            return rc, (json.loads(out.getvalue()) if out.getvalue() else {}).get("code")

        self.assertEqual(cli(text.encode()), (0, None))
        # the held decision named last, another first: the last value alone would be HELD
        twice = text.replace('"decision": ', f'"decision": "{"00" * 32}", "decision": ', 1)
        self.assertEqual(cli(twice.encode()), (1, "FORMAT"))
        seal = t["endorsements"][0]["seal"]
        twice = text.replace(f'"seal": "{seal}"', f'"seal": "{"00" * 32}", "seal": "{seal}"', 1)
        self.assertEqual(cli(twice.encode()), (1, "FORMAT"))
        for raw in (text.encode()[:-1], b"\xff" + text.encode(), b"[]"):
            self.assertEqual(cli(raw), (1, "FORMAT"), raw[:8])
        # NaN and the infinities are not JSON, though Python's json reads them (Codex finding fb410499 on #48)
        for token in ("NaN", "Infinity", "-Infinity"):
            for extra in (token, f'{{"nested": {token}}}'):
                raw = (text[:-1] + f', "extra": {extra}}}').encode()
                self.assertEqual(cli(raw), (1, "FORMAT"), raw[-40:])
        self.assertEqual(cli((text[:-1] + ', "extra": {"nested": 1.5}}').encode()), (0, None), "a number is JSON")
        crash = CK.check_text
        CK.check_text = lambda *a: 1 // 0
        try:
            self.assertEqual(cli(text.encode()), (3, None))
        finally:
            CK.check_text = crash

    def test_12_a_seal_counts_under_the_scope_that_governed_it(self):
        """Rotations, under v1 and under v2: a decision approved before a key joins and one approved after are HELD,
        their seals read under the scope that governed each commit, and both checkers agree; a pin of the scope a
        rotation replaced is not the tip (NOT_COVERED WAITING). A rotation that drops a key in a v1 epoch takes effect
        at once; that key's seals before it still count, a seal by it under the new scope does not (KEY)."""
        for rules in (V.H_LENS_KERNEL, V.H_LENS_KERNEL_V2):
            c = Chain(scratch(), rules=rules)
            g, k, d, vs = c.basic()
            s0 = c.scope.id
            s1 = c.rotate((*MEMBERS, "dee"), "dee joins")  # adds a key: never waits
            self.assertEqual(c.governing(), s1.id, "a join takes effect at once")
            c.ctx = s1.id
            d2 = c.decision("decision/d2", [k], members=(*MEMBERS, "dee"))
            w = {m: c.verdict(d2, f"decision/d2/by-{m}", [k], verifier=m) for m in ("bo", "dee")}
            c.commit((d2, "dee"), *((v, m) for m, v in w.items()))
            for dec, ws in ((d, [vs["ana"].id, vs["bo"].id]), (d2, [w["bo"].id, w["dee"].id])):
                self.assertTrue(c.repo.lens(SCOPE)["settled"].get(dec.id))
                for t in (PR.prove(c.repo, SCOPE, dec.id), term(c.repo, c.tip, dec.id, ws)):
                    r = c.check(t, s1.id)
                    self.assertEqual(r["result"], "HELD", (rules.hex()[:8], r))
            r = c.check(PR.prove(c.repo, SCOPE, d.id), s0)
            self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "WAITING"), r)

        c = Chain(scratch())
        g, k, d, vs = c.basic()
        s1 = c.rotate(("ana", "bo"), "cy leaves")  # a v1 epoch: at once, consent or not
        self.assertEqual(c.governing(), s1.id)
        good = term(c.repo, c.tip, d.id, [vs["ana"].id, vs["cy"].id])
        self.assertEqual(c.check(good)["result"], "HELD", "cy's seal under the scope it was a member of counts")
        late = V.Seal.sign(c.sk["cy"], vs["cy"].id, s1.id).encode()
        tip = raw_commit(c.path, c.tip, [cas("seals", late)])
        t = dict(good, tip=tip, endorsements=[good["endorsements"][0], {"verdict": vs["cy"].id.hex(),
                                                                       "seal": hashlib.sha256(late).hexdigest()}])
        r = c.check(t)
        self.assertEqual((r["result"], r.get("code")), ("REFUSED", "KEY"), r)

    def test_13_every_decision_of_the_live_chain(self):
        """On refs/vars/heads/minds at its tip (its v1 epochs, the rotation to v2, joins under both): the prover finds
        a witness for exactly the decisions the lens holds Settled, check.py holds each, and vars1witness accepts each.
        Skipped when the chain is not fetched, unless MINDS_REQUIRE_CHAIN=1."""
        repo = V.GitVarsRepo(ROOT)
        tip = repo.ref_commit("minds")
        if tip is None:
            if os.environ.get("MINDS_REQUIRE_CHAIN") == "1":
                self.fail("refs/vars/heads/minds is not fetched, and MINDS_REQUIRE_CHAIN=1 requires it")
            self.skipTest("refs/vars/heads/minds is not fetched in this clone")
        lens = repo.lens("minds", at=tip)
        decisions = [cid for cid, c in lens["cells"].items() if c.h_schema == V.H_SCHEMA["decision"]]
        held_ = []
        for dec in decisions:
            settled = bool(lens["settled"].get(dec)) and bool(lens["active"].get(dec)) and not lens["stale"].get(dec)
            try:
                t = PR.prove(repo, "minds", dec, tip)
            except PR.NotHeld:
                self.assertFalse(settled, f"the lens settles {dec.hex()}, the prover found no witness")
                continue
            r = held(ROOT, t)
            self.assertEqual(r["result"], "HELD", (dec.hex(), r))
            held_.append(dec)
        self.assertEqual(len(held_), sum(bool(lens["settled"].get(x)) for x in decisions))
        self.assertGreater(len(held_), 0)

    def test_14_the_lean_prover_finds_a_derivation_wherever_the_checker_holds_one(self):
        """`vars1witness --prove` builds the derivation from the store alone (proofs/Vars1/WitnessComplete.lean `prove`;
        `witness_complete`: on its fragment the checker accepts it whenever the model holds the decision Settled). On
        both generated histories, before the failure and after it, it accepts exactly the decisions for which
        prove.py's term is HELD; on every decision of the live chain at its tip, where no edge touches a cone, exactly
        those the lens holds Settled. Test 16 covers the edges that do not count. Skipped without the Lean checker or the chain, unless MINDS_REQUIRE_LEAN=1 and
        MINDS_REQUIRE_CHAIN=1."""
        if not LEAN.exists():
            if os.environ.get("MINDS_REQUIRE_LEAN") == "1":
                self.fail("MINDS_REQUIRE_LEAN=1, but proofs/.lake/build/bin/vars1witness is not built")
            self.skipTest("proofs/.lake/build/bin/vars1witness is not built")

        seen = set()
        for i in (0, 1):
            h, ch, path, before, after = history_chain(i)
            for tip in (before, after):
                for dd in h["decisions"]:
                    d = ch["ids"][dd["id"]]
                    try:
                        r = held(path, PR.prove(ch["repo"], HI.SCOPE, d, tip))
                        r = r["result"] if r["result"] != "NOT_COVERED" else f"NOT_COVERED {r['code']}"
                    except PR.NotHeld:
                        r = "NOT_HELD"
                    self.assertEqual(lean_proves(path, tip, HI.SCOPE, d), r == "HELD", (i, tip, dd["id"], r))
                    seen.add(r)
        self.assertEqual(seen, {"HELD", "NOT_HELD"})
        # outside the fragment completeness is not claimed: the lens settles d, and no derivation the checker accepts
        # exists (a retires edge into the cone that did not latch, whose source a key of its target seals after the
        # target's birth; an INVALID verdict that is retired, which the checker cannot prove not live)
        for c, d in (author_chain(True)[:2], retired_invalid_chain()[:2]):
            self.assertTrue(lens_settles(c, d))
            self.assertFalse(lean_proves(c.path, c.tip, SCOPE, d.id))

        repo = V.GitVarsRepo(ROOT)
        tip = repo.ref_commit("minds")
        if tip is None:
            if os.environ.get("MINDS_REQUIRE_CHAIN") == "1":
                self.fail("refs/vars/heads/minds is not fetched, and MINDS_REQUIRE_CHAIN=1 requires it")
            self.skipTest("refs/vars/heads/minds is not fetched in this clone")
        lens = repo.lens("minds", at=tip)
        accepted = 0
        for dec in (cid for cid, c in lens["cells"].items() if c.h_schema == V.H_SCHEMA["decision"]):
            settled = bool(lens["settled"].get(dec)) and bool(lens["active"].get(dec)) and not lens["stale"].get(dec)
            self.assertEqual(lean_proves(ROOT, tip, "minds", dec), settled, dec.hex())
            accepted += settled
        self.assertGreater(accepted, 0)

    def test_15_an_invalid_verdict_withdraws_only_the_keys_that_seal_it(self):
        """An INVALID verdict on the decision withdraws an endorsement under its own verifier id by a key that seals it,
        and no other (§4.2 Pass 3: a verifier id is free text): a term that names such an endorsement is REFUSED
        (`WITHDRAWN`), the others are HELD where their keys meet the threshold, on both checkers. `vars1witness --prove`
        accepts exactly where the lens settles. Three INVALID verdicts by the keys of d's 2-of-3 policy: cy under its own
        id, cy under ana's, and ana and bo each under their own."""
        prove_lean = LEAN.exists() or os.environ.get("MINDS_REQUIRE_LEAN") == "1"

        def outcome(c, d, verdicts):
            r = c.check(term(c.repo, c.tip, d.id, [v.id for v in verdicts]))
            return r["result"], r.get("code"), len(r.get("endorsers", []))

        # cy, under its own verifier id: its endorsement through its own verdict is withdrawn, ana's and bo's stand
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        c.commit((c.verdict(d, "decision/d/invalid-by-cy", [k], code=V.H_VERDICT_INVALID, verifier="cy"), "cy"))
        lens = c.repo.lens(SCOPE)
        self.assertTrue(lens["settled"].get(d.id))
        self.assertEqual(lens["counted_witnesses"][d.id].get(vs["cy"].id, set()), set(), "the lens withdraws cy")
        self.assertEqual(outcome(c, d, vs.values()), ("REFUSED", "WITHDRAWN", 0))
        self.assertEqual(outcome(c, d, [vs["cy"]]), ("REFUSED", "WITHDRAWN", 0))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]]), ("HELD", None, 2))
        self.assertEqual(c.check(PR.prove(c.repo, SCOPE, d.id))["result"], "HELD")
        if prove_lean:
            self.assertTrue(lean_proves(c.path, c.tip, SCOPE, d.id))

        # cy, under ana's verifier id: it withdraws only cy's keys under that id, and cy sealed no verdict under it
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        c.commit((c.verdict(d, "decision/d/invalid-as-ana", [k], code=V.H_VERDICT_INVALID, verifier="ana"), "cy"))
        self.assertTrue(c.repo.lens(SCOPE)["settled"].get(d.id))
        self.assertEqual(outcome(c, d, vs.values()), ("HELD", None, 3))
        if prove_lean:
            self.assertTrue(lean_proves(c.path, c.tip, SCOPE, d.id))

        # ana and bo, each under its own: only cy's endorsement is left, one key of two
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        c.commit(*((c.verdict(d, f"decision/d/invalid-by-{m}", [k], code=V.H_VERDICT_INVALID, verifier=m), m)
                   for m in ("ana", "bo")))
        self.assertFalse(c.repo.lens(SCOPE)["settled"].get(d.id))
        self.assertEqual(outcome(c, d, vs.values()), ("REFUSED", "WITHDRAWN", 0))
        self.assertEqual(outcome(c, d, [vs["cy"]]), ("REFUSED", "THRESHOLD", 0))
        with self.assertRaises(PR.NotHeld):
            PR.prove(c.repo, SCOPE, d.id)
        if prove_lean:
            self.assertFalse(lean_proves(c.path, c.tip, SCOPE, d.id))

    def test_16_kill_edges_that_do_not_count(self):
        """An edge into the cone that does not count leaves the decision held, on both checkers, and one that counts
        refuses the term (KILLED); `vars1witness --prove` accepts exactly where the lens settles. The cases: a notice
        withdrawn by a second notice, and a third that withdraws the second; INVALID verdicts that are Stale or
        Invalidated, which withdraw nothing, beside a live one, which does; an ATTESTED verdict's invalidates edge,
        which counts for nothing; a retirement, and one whose retirer is invalidated; a supersession, one whose
        superseder is invalidated, and one where that superseder is itself superseded; a rebinding whose supersedes
        edge latched, and one whose edge did not (test 08's unauthorized supersedes); a notice on a decision of tier
        owner, whose edges the admission policy governs."""
        prove_lean = LEAN.exists() or os.environ.get("MINDS_REQUIRE_LEAN") == "1"

        def outcome(c, d, verdicts, lens: bool):
            self.assertEqual(lens_settles(c, d), lens, d.id.hex())
            if prove_lean:
                self.assertEqual(lean_proves(c.path, c.tip, SCOPE, d.id), lens, d.id.hex())
            r = c.check(term(c.repo, c.tip, d.id, [v.id for v in verdicts]))
            if lens:
                self.assertEqual(c.check(PR.prove(c.repo, SCOPE, d.id))["result"], "HELD")
            return r["result"], r.get("code")

        held_, killed = ("HELD", None), ("REFUSED", "KILLED")
        # notices: g is invalidated by n, n by m, m by o
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        n = c.axiom("notice/g", invalidates=[g])
        c.commit((n, "cy"))
        m = c.axiom("notice/not-g", invalidates=[n])
        c.commit((m, "bo"))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], True), held_, "n is dead: g stands")
        c.commit((c.axiom("notice/not-not-g", invalidates=[m]), "ana"))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], False), killed, "m is dead, n Effective: g falls")

        # INVALID verdicts: bo's is Stale, so it withdraws nothing; cy's is live
        c, d, vs = stale_invalid_chain()
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], True), held_)
        self.assertEqual(outcome(c, d, list(vs.values()), True), ("REFUSED", "WITHDRAWN"))
        # bo's INVALID verdict is itself invalidated
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        b = c.verdict(d, "decision/d/invalid-by-bo", [k], code=V.H_VERDICT_INVALID, verifier="bo")
        c.commit((b, "bo"))
        c.commit((c.axiom("notice/invalid-by-bo", invalidates=[b]), "ana"))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], True), held_)

        # an ATTESTED verdict (on another decision) that invalidates g: a verdict kills only if it is INVALID
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        e = c.decision("decision/e", [g], thr=1)
        w = V.Cell(h_schema=V.H_SCHEMA["verdict"], h_slot_name=c.utf8(f"{SCOPE}/decision/e/by-cy"), h_payload=e.id,
                   h_attests=c.hv([e.id]), h_invalidates=c.hv([g.id]), slots=(V.H_EMPTY, V.H_ATTESTED, c.utf8("cy")))
        c.commit((e, "cy"), (w, "cy"))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], True), held_)

        # a retirement of g, then an invalidation of its retirer
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        r = c.axiom("retire/g", retires=[g])
        c.commit((r, "cy"))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], False), killed)
        c.commit((c.axiom("notice/retire", invalidates=[r]), "bo"))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], True), held_)

        # g superseded by u; u invalidated; u superseded by v, so g is Superseded through it
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        u = c.axiom("ground/g", supersedes=[g])
        c.commit((u, "ana"))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], False), killed, "u is Effective: g is Superseded")
        c.commit((c.axiom("notice/u", invalidates=[u]), "bo"))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], True), held_, "u is Invalidated and not Superseded")
        c.commit((c.axiom("ground/g", supersedes=[u]), "cy"))
        self.assertEqual(outcome(c, d, [vs["ana"], vs["bo"]], False), killed, "u is Superseded: so is g, through u")

        # rebinding: d2 supersedes d1 (2 of 3) by an edge ana and bo latch; then one cy alone does not
        for sealers, lens in ((("ana", "bo"), True), (("cy",), False)):
            c = Chain(scratch())
            g = c.axiom("ground/g")
            c.commit((g, "ana"))
            d1 = c.decision("decision/d", [g], thr=2 if lens else 3)
            c.commit((d1, ("ana", "bo")))
            d2 = c.decision("decision/d", [g], thr=1, supersedes=[d1])
            v2 = c.verdict(d2, "decision/d2/by-ana", [g])
            c.commit((d2, sealers), (v2, "ana"))
            self.assertEqual(outcome(c, d2, [v2], lens), held_ if lens else killed, sealers)

        # a decision of tier owner relied upon, invalidated by one key: the admission policy (1 of 3) governs it,
        # not its own policy (3 of 3)
        c = Chain(scratch())
        g = c.axiom("ground/g")
        c.commit((g, "ana"))
        e = c.owned("decision/e", [g], thr=3)
        c.commit((e, "ana"))
        d = c.decision("decision/d", [e], thr=1)
        v = c.verdict(d, "decision/d/by-ana", [e])
        c.commit((d, "ana"), (v, "ana"))
        self.assertEqual(outcome(c, d, [v], True), held_)
        c.commit((c.axiom("notice/e", invalidates=[e]), "cy"))
        self.assertEqual(outcome(c, d, [v], False), killed)


    # --- what a reader must read (frame.py, proofs/Vars1/Reader.lean) ---------------------------------------------

    def _step(self, c, d, act, grounded=False):
        """What `touches` says of the objects `act` adds to the chain, against d's frame before it, and whether d's
        status changed: (reason or None, changed). Where nothing touches the frame the status must be the same."""
        T = FR.Tip(V, c.repo, SCOPE, c.tip)
        fr = FR.frame(T, d.id, grounded)
        before = status(T.lens, d.id, grounded)
        act()
        c.ctx = c.governing()
        t = FR.touches(T, fr, *FR.delta(T, c.tip))
        after = status(c.repo.lens(SCOPE, at=c.tip), d.id, grounded)
        if t is None:
            self.assertEqual(before, after, f"nothing touched the frame of {d.id.hex()[:8]}, yet its status changed")
        return (t[0] if t else None, before != after)

    def test_17_a_status_is_unchanged_while_nothing_touches_its_frame(self):
        """`settled_frame` and `grounded_frame` on chains through the gate: each kind of object that can change a
        decision's status touches its frame, by the rule that names it, and changes the status; what touches nothing
        changes nothing. The cases: a notice on the cone, and a second notice that revives it; a notice whose edge
        one more seal latches; a seal that completes a quorum; an INVALID verdict that names the decision by payload
        alone; an answer that attests a question; a notice on what only a verdict relies on; a retirement and a
        supersession; a rotation, for a decision that reads the scope's policy and for one with its own; a rotation
        that waits under v2 and governs sixteen commits later with no new cell; and, for Grounded, a withdrawal from a
        decision the decision relies on, which leaves it Settled; a rebinding whose supersedes edge a late seal of the
        replaced cell's author latches. Then every pair of tips of every chain, both frames."""
        chains, step = [], self._step

        def chain(**kw):
            chains.append(Chain(scratch(), **kw))
            return chains[-1]

        touched = lambda reason: (reason, True)  # noqa: E731
        c = chain()
        g, k, d, vs = c.basic()
        x = c.axiom("ground/x")
        self.assertEqual(step(c, d, lambda: c.commit((x, "cy"))), (None, False), "an unrelated cell")
        self.assertEqual(step(c, d, lambda: c.commit((c.axiom("notice/x", invalidates=[x]), "bo"))), (None, False))
        self.assertEqual(step(c, d, lambda: c.seal(x, "ana")), (None, False), "a seal on an unrelated cell")
        n = c.axiom("notice/g", invalidates=[g])
        self.assertEqual(step(c, d, lambda: c.commit((n, "cy"))), touched("EDGE"), "a notice on the ground")
        m = c.axiom("notice/not-g", invalidates=[n])
        self.assertEqual(step(c, d, lambda: c.commit((m, "bo"))), touched("EDGE"), "the notice is invalidated: revived")

        c = chain()
        g, k, d, vs = c.basic()
        n = c.axiom("notice/d", invalidates=[d])
        self.assertEqual(step(c, d, lambda: c.commit((n, "ana"))), ("EDGE", False), "one key of d's 2 of 3: no latch")
        self.assertEqual(step(c, d, lambda: c.seal(n, "bo")), touched("SEAL"), "the second seal latches the edge")

        c = chain()
        g = c.axiom("ground/g")
        c.commit((g, "ana"))
        d = c.decision("decision/d", [g], thr=2)
        v = c.verdict(d, "decision/d/by-ana", [g], verifier="ana")
        c.commit((d, "ana"), (v, "ana"))
        self.assertEqual(step(c, d, lambda: c.seal(v, "bo")), touched("SEAL"), "a second key seals the verdict")

        c = chain()
        g = c.axiom("ground/g")
        c.commit((g, "ana"))
        d = c.decision("decision/d", [g], thr=3)
        vs = {m: c.verdict(d, f"decision/d/by-{m}", [g], verifier=m) for m in MEMBERS}
        c.commit((d, "ana"), *((v, m) for m, v in vs.items()))
        bad = V.Cell(h_schema=V.H_SCHEMA["verdict"], h_slot_name=c.utf8(f"{SCOPE}/decision/d/no-by-cy"), h_payload=d.id,
                     slots=(V.H_EMPTY, V.H_VERDICT_INVALID, c.utf8("cy")))
        self.assertEqual(step(c, d, lambda: c.commit((bad, "cy"))), touched("JUDGE"), "INVALID, by payload alone")

        c = chain()
        q = V.Cell(V.H_SCHEMA["question"], c.utf8(f"{SCOPE}/question/q"), c.utf8("is it so?"),
                   slots=(V.H_SCHEMA["axiom"], V.H_EMPTY))
        c.commit((q, "ana"))
        ans = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=c.utf8(f"{SCOPE}/answer/q"), h_payload=c.utf8("it is"),
                     h_attests=c.hv([q.id]))
        self.assertEqual(step(c, q, lambda: c.commit((ans, "bo"))), touched("JUDGE"), "an answer attests the question")

        c = chain()
        g, k2 = c.axiom("ground/g"), c.axiom("ground/k2")
        c.commit((g, "ana"), (k2, "bo"))
        d = c.decision("decision/d", [g], thr=2)
        vs = {m: c.verdict(d, f"decision/d/by-{m}", [k2], verifier=m) for m in ("ana", "bo")}
        c.commit((d, "ana"), *((v, m) for m, v in vs.items()))
        self.assertEqual(step(c, d, lambda: c.commit((c.axiom("notice/k2", invalidates=[k2]), "cy"))),
                         touched("EDGE"), "a notice on what only the verdicts rely on")

        for edge in ("retires", "supersedes"):
            c = chain()
            g, k, d, vs = c.basic()
            r = c.axiom("ground/g" if edge == "supersedes" else "retire/g", **{edge: [g]})
            self.assertEqual(step(c, d, lambda: c.commit((r, "ana"))), touched("EDGE"), edge)

        c = chain()
        g, k, d, vs = c.basic()
        e = V.Cell(h_schema=V.H_SCHEMA["decision"], h_slot_name=c.utf8(f"{SCOPE}/decision/e"), h_payload=c.utf8("e"),
                   h_relies=c.hv([k.id]), slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY))
        ve = c.verdict(e, "decision/e/by-cy", [k], verifier="cy")
        c.commit((e, "cy"), (ve, "cy"))
        self.assertTrue(c.repo.lens(SCOPE)["settled"].get(e.id), "cy is one of the scope's admission keys")
        rot = lambda: c.rotate(("ana", "bo"), "cy leaves")  # noqa: E731
        T = FR.Tip(V, c.repo, SCOPE, c.tip)
        frames = FR.frame(T, e.id), FR.frame(T, d.id)
        self.assertEqual(step(c, e, rot), touched("SCOPE"), "e reads the scope's policy: the rotation is in its frame")
        self.assertEqual(FR.touches(T, frames[1], *FR.delta(T, c.tip)), None, "d names its own policy: it is not")
        self.assertTrue(c.repo.lens(SCOPE)["settled"].get(d.id))

        c = chain(rules=V.H_LENS_KERNEL_V2)
        g, k, d, vs = c.basic()
        e = V.Cell(h_schema=V.H_SCHEMA["decision"], h_slot_name=c.utf8(f"{SCOPE}/decision/e"), h_payload=c.utf8("e"),
                   h_relies=c.hv([k.id]), slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY))
        ve = c.verdict(e, "decision/e/by-cy", [k], verifier="cy")
        c.commit((e, "cy"), (ve, "cy"))
        self.assertEqual(step(c, e, lambda: c.rotate(("ana", "bo"), "cy leaves")), ("SCOPE", False), "it waits")
        self.assertEqual(c.governing(), c.scope.id)

        def sixteen():
            for i in range(17):
                c.ctx = c.governing()
                c.commit((c.axiom(f"filler/{i}"), "ana"))

        self.assertEqual(step(c, e, sixteen), touched("WAITING"), "the wait ends in commits that add no scope cell")
        self.assertNotEqual(c.governing(), c.scope.id)

        c = chain()
        g = c.axiom("ground/g")
        c.commit((g, "ana"))
        d1 = c.decision("decision/d1", [g], thr=3)
        vs = {m: c.verdict(d1, f"decision/d1/by-{m}", [g], verifier=m) for m in MEMBERS}
        d2 = c.decision("decision/d2", [d1], thr=1)
        v2 = c.verdict(d2, "decision/d2/by-ana", [g], verifier="ana")
        c.commit((d1, "ana"), *((v, m) for m, v in vs.items()), (d2, "ana"), (v2, "ana"))
        self.assertTrue(c.repo.lens(SCOPE)["grounded"].get(d2.id))
        bad = c.verdict(d1, "decision/d1/no-by-cy", [g], code=V.H_VERDICT_INVALID, verifier="cy")
        T = FR.Tip(V, c.repo, SCOPE, c.tip)
        settled_frame = FR.frame(T, d2.id)
        self.assertEqual(step(c, d2, lambda: c.commit((bad, "cy")), grounded=True), touched("JUDGE"),
                         "d1 loses its quorum: d2 is Settled and no longer Grounded")
        self.assertEqual(FR.touches(T, settled_frame, *FR.delta(T, c.tip)), None, "Settled of d2 does not read d1's verdicts")
        lens = c.repo.lens(SCOPE)
        self.assertEqual((lens["settled"].get(d2.id), lens["grounded"].get(d2.id), lens["settled"].get(d1.id)),
                         (True, False, False))

        c = chain()
        g = c.axiom("ground/g")
        c.commit((g, "ana"))
        d1 = c.decision("decision/d", [g], thr=3)
        c.commit((d1, "ana"))
        d2 = c.decision("decision/d", [g], thr=1, supersedes=[d1])
        v2 = c.verdict(d2, "decision/d2/by-cy", [g], verifier="cy")
        c.commit((d2, "cy"), (v2, "cy"))
        self.assertFalse(c.repo.lens(SCOPE)["active"].get(d2.id), "cy alone latches no edge onto d1")
        self.assertEqual(step(c, d2, lambda: c.seal(d2, "ana")), touched("SEAL"),
                         "ana sealed d1 at its birth: its seal on d2 latches the rebinding, and d2 stands")

        seen = collections.Counter()
        for c in chains:
            seen += frame_holds(self, c.repo, SCOPE, c.repo.commit_chain(c.tip))
        if os.environ.get("FRAME_STATS"):
            print("test 17", dict(seen))
        self.assertGreater(seen["untouched"], 100, seen)
        self.assertGreater(seen["changed"], 20, seen)

    def test_18_random_extensions_keep_what_nothing_touches(self):
        """Random perturbations through the gate: from a base with a ground, two decisions of their own policy (one
        relying on the other), one that reads the scope's policy and a question, 60 random commits (cells, notices on
        any cell, verdicts ATTESTED and INVALID under any verifier id, late seals, retirements, supersessions, a
        rotation), under each of v1 and v2 and under an admission threshold of 1 and of 2. Over every pair of tips and
        every evaluated cell, a frame that nothing touches keeps its status, Settled and Grounded."""
        seen = collections.Counter()
        for seed, rules, thr in ((1, V.H_LENS_KERNEL, 1), (2, V.H_LENS_KERNEL_V2, 1), (3, V.H_LENS_KERNEL, 2)):
            c, tips = random_walk(seed, rules, thr, 60)
            self.assertGreater(len(tips), 40, "most random commits are admitted")
            seen += frame_holds(self, c.repo, SCOPE, tips)
        if os.environ.get("FRAME_STATS"):
            print("test 18", dict(seen))
        self.assertGreater(seen["untouched"], 1000, seen)
        self.assertGreater(seen["changed"], 100, seen)
        for reason in ("EDGE", "JUDGE", "SEAL", "SCOPE"):
            self.assertGreater(seen[reason], 0, seen)

    def test_19_the_live_chain_at_a_named_tip(self):
        """On refs/vars/heads/minds. (1) Renewal: for every tip, every decision there and every later tip, a frame
        that the commits between do not touch keeps its status at the later tip, so a witness is renewed by reading
        those commits alone. (2) The table of README.md at the tip of 2026-11-07, byte for byte: what a Settled
        decision's status reads (2, 3 and 39 cells of 651), the bytes of that against the attestation bundle a client
        receives, and the decisions that read the scope's policy (3 of 47). (3) `bundle_at` is `vars1.export_attestation`
        at the ref's tip. Skipped when the chain is not fetched, unless MINDS_REQUIRE_CHAIN=1."""
        repo = V.GitVarsRepo(ROOT)
        tip = repo.ref_commit("minds")
        if tip is None:
            if os.environ.get("MINDS_REQUIRE_CHAIN") == "1":
                self.fail("refs/vars/heads/minds is not fetched, and MINDS_REQUIRE_CHAIN=1 requires it")
            self.skipTest("refs/vars/heads/minds is not fetched in this clone")
        chain = repo.commit_chain(tip)
        self.assertIn(LIVE_TIP, chain)
        seen = frame_holds(self, repo, "minds", chain, schemas=("decision",))
        if os.environ.get("FRAME_STATS"):
            print("test 19", dict(seen))
        self.assertGreater(seen["untouched"], 10000, seen)
        self.assertGreater(seen["changed"], 0, seen)
        pinned = json.loads((HERE / "frame-minds-7c6899b.json").read_text())
        self.assertEqual(FR.measure(V, repo, "minds", LIVE_TIP, PR.prove), pinned)
        mmm = pinned["min_median_max"]
        self.assertEqual((pinned["store"]["cells"], pinned["decisions"], pinned["settled"], mmm["read"]),
                         (651, 47, 34, [2, 3.0, 39]))
        self.assertEqual(pinned["scope_caveat"], {"decisions": 3, "settled": 3})
        self.assertLess(mmm["message_json"][2] * 8, mmm["bundle_json"][0], "the message is under an eighth of the bundle")
        T = FR.Tip(V, repo, "minds", tip)
        for d in [x for x, c in T.cells.items() if c.h_schema == V.H_SCHEMA["decision"]][:3]:
            pid = FR.covering_at(T, d)
            self.assertEqual(FR.bundle_at(T, d, pid), V.export_attestation(repo, "minds", d, pid))

    def test_20_the_message_carries_what_its_proof_names(self):
        """The draft message for "d is in force at T" (frame.py `message`): its proof part holds every cell of the
        term's cone, every endorsing seal, each scope cell a seal is under with its roster, and the decision's policy,
        each object hashing to the name the term or another object of the message gives it; and it is the attestation
        bundle's facts about d, without the tip. Nothing in it says that no other cell, verdict or seal touches the
        frame: that is the vouch, which this test leaves empty."""
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        s1 = c.rotate((*MEMBERS, "dee"), "dee joins")
        c.ctx = s1.id
        c.seal(vs["cy"], "dee")
        T = FR.Tip(V, c.repo, SCOPE, c.tip)
        t = PR.prove(c.repo, SCOPE, d.id)
        self.assertEqual(c.check(t)["result"], "HELD")
        msg = FR.message(T, t, {})
        self.assertEqual(msg["claim"], {"scope": SCOPE, "decision": d.id.hex(), "tip": c.tip, "epoch": s1.id.hex(),
                                        "rules": V.H_LENS_KERNEL.hex()})
        have = {hashlib.sha256(bytes.fromhex(x)).digest() for part in ("cells", "seals", "scopes", "atoms")
                for x in msg["proof"][part]}
        self.assertTrue({bytes.fromhex(x) for x in t["cone"]} <= have)
        self.assertTrue({bytes.fromhex(e["seal"]) for e in t["endorsements"]} <= have)
        self.assertTrue({s1.id, c.scope.id} <= have, "the seals are under the first scope, the tip under the second")
        self.assertTrue({d.slots[3], T.cells[c.scope.id].slots[0], T.cells[s1.id].slots[0]} <= have)
        self.assertEqual(len(msg["proof"]["scopes"]), 2)
        bundle = FR.bundle_at(T, d.id)
        self.assertEqual(bundle, V.export_attestation(c.repo, SCOPE, d.id))
        self.assertIn(bundle["cell"], msg["proof"]["cells"])
        self.assertTrue(set(msg["proof"]["seals"]) <= set(bundle["seals"]))

    def _rev_frames(self, T, decisions):
        """Every frame of `decisions` (Settled's and Grounded's) read from its closed-world part alone, against
        frame.py's frame and the seals on its watched cells read from the store."""
        ix = RX.Index(T)
        fields = ("read", "guard", "judges", "named", "sources", "evaluated", "watch", "fallback")
        n = 0
        for d in decisions:
            for grounded in (False, True):
                fr = FR.frame(T, d, grounded)
                rf = RX.reader_frame(V, RX.closed_part(T, ix, fr), d, grounded)
                self.assertEqual({k: rf[k] for k in fields}, {k: fr[k] for k in fields}, (d.hex()[:12], grounded))
                watched = set(fr["watch"])
                self.assertEqual(rf["seals"], sorted(sid for sid, x in T.seals.items() if x.h_target in watched))
                n += 1
        return n

    def test_21_a_frame_reads_from_its_leaves_alone(self):
        """revindex.py: from the root of the tip's reverse index, the leaves of a frame with their paths, and the
        frame's own cells, a reader reads the frame frame.py reads from the whole store, and the seals on every watched
        cell: on chains with a retires edge into a decision and into a verdict, an invalidates edge under a Stale
        verdict, and on every decision of the live chain at the named tip, for Settled and for Grounded."""
        for c, d, _ in (author_chain(False), author_chain(True), retired_invalid_chain(), stale_invalid_chain()):
            self.assertEqual(self._rev_frames(FR.Tip(V, c.repo, SCOPE, c.tip), [d.id]), 2)
        self.assertEqual(self._rev_frames(*named_store()), 2)
        repo = V.GitVarsRepo(ROOT)
        if repo.ref_commit("minds") is None:
            if os.environ.get("MINDS_REQUIRE_CHAIN") == "1":
                self.fail("refs/vars/heads/minds is not fetched, and MINDS_REQUIRE_CHAIN=1 requires it")
            self.skipTest("refs/vars/heads/minds is not fetched in this clone")
        T = FR.Tip(V, repo, "minds", LIVE_TIP)
        decisions = sorted(x for x, c in T.cells.items() if c.h_schema == V.H_SCHEMA["decision"])
        self.assertEqual(self._rev_frames(T, decisions), 94)
        ix = RX.Index(T)
        self.assertEqual((ix.root.hex(), len(ix.keys)),
                         ("5baad8aa1855158c9eb4d0f497173bc2480f8017b8b44de046c5fb8230eb503e", 651), "the named tip's root")
        # The table of README.md, byte for byte: at five tips the bundle grows with the store, the message does not
        chain = repo.commit_chain(LIVE_TIP)
        tips = [chain[i] for i in sorted({len(chain) // 8, len(chain) // 4, len(chain) // 2, 3 * len(chain) // 4,
                                          len(chain) - 1})]
        pinned = json.loads((HERE / "revindex-minds-7c6899b.json").read_text())
        self.assertEqual(RX.measure(V, repo, "minds", tips, PR.prove, FR), pinned)
        first, last = pinned[0], pinned[-1]
        self.assertEqual((first["cells"], last["cells"]), (36, 651))
        self.assertGreater(last["bundle_median"], 12 * first["bundle_median"])
        self.assertLess(last["message_median"], 2 * first["message_median"])
        self.assertGreater(last["bundle_median"], 18 * last["message_median"])

    def test_22_a_leaf_off_the_root_or_a_missing_part_is_no_answer(self):
        """A leaf that does not lead to the root is refused, and a part without a leaf, a cell of `guard`, or a seal
        on a watched cell the reading needs is Incomplete: the reader never fills a gap with "nothing"."""
        c, d, vs = stale_invalid_chain()
        T = FR.Tip(V, c.repo, SCOPE, c.tip)
        fr = FR.frame(T, d.id)
        part = RX.closed_part(T, RX.Index(T), fr)
        self.assertEqual(RX.reader_frame(V, part, d.id)["guard"], fr["guard"])
        forged = json.loads(json.dumps(part))
        lf = next(x for x in forged["leaves"] if x["key"] == d.id.hex())
        lf["payload"] = lf["payload"][1:]  # hide a verdict on d
        with self.assertRaisesRegex(ValueError, "does not lead to the root"):
            RX.reader_frame(V, forged, d.id)
        for drop in ("leaves", "cells", "seals"):
            short = json.loads(json.dumps(part))
            if drop == "leaves":
                short["leaves"] = [x for x in short["leaves"] if x["key"] != d.id.hex()]
            elif drop == "cells":
                short["cells"] = [x for x in short["cells"]
                                  if hashlib.sha256(bytes.fromhex(x)).digest() != vs["ana"].id]
            else:
                short["seals"] = short["seals"][1:]
            with self.assertRaises(RX.Incomplete, msg=drop):
                RX.reader_frame(V, short, d.id)

    def test_23_a_lying_root_is_refuted_by_one_object(self):
        """The root is the signer's claim, so a root over a leaf that hides a verdict on d gives a reader a smaller
        frame, and its paths check. What the signer cannot do is lie cheaply: `refute` finds, against the store, the
        one object the leaf leaves out or the id it lists falsely, and `judge` accepts that proof by reading that object
        alone. An honest leaf has no refutation, and a refutation does not transfer to the honest root."""
        c, d, vs = stale_invalid_chain()
        T = FR.Tip(V, c.repo, SCOPE, c.tip)
        honest = RX.Index(T)
        fr = FR.frame(T, d.id)
        for kind, lie in (("attests", "omit"), ("seals", "omit"), ("attests", "list")):
            entries = {k: {kk: list(v) for kk, v in e.items()} for k, e in honest.entries.items()}
            target = d.id if kind != "seals" else vs["ana"].id
            if lie == "omit":
                hidden = entries[target][kind][0]
                for kk in (("attests", "payload") if kind == "attests" else (kind,)):  # a verdict attests d and is on d
                    entries[target][kk] = [x for x in entries[target][kk] if x != hidden]
            else:
                hidden = d.id  # d does not attest itself
                entries[target][kind] = sorted(entries[target][kind] + [hidden])
            liar = RX.Index(T, entries)
            self.assertNotEqual(liar.root, honest.root)
            lf = liar.leaf(target)
            if (kind, lie) == ("attests", "omit"):
                rf = RX.reader_frame(V, RX.closed_part(T, liar, fr), d.id)
                self.assertEqual(set(fr["judges"]) - set(rf["judges"]), {hidden},
                                 "the lying root's paths check, and its frame lacks the hidden verdict")
            fraud = RX.refute(T, lf)
            self.assertEqual((fraud["kind"], "omits" in fraud), (kind, lie == "omit"))
            self.assertTrue(RX.judge(T, liar.root, len(liar.keys), fraud), (kind, lie))
            self.assertFalse(RX.judge(T, honest.root, len(honest.keys), fraud), "the proof names the lying root's leaf")
            if lie == "omit":
                self.assertEqual(hashlib.sha256(bytes.fromhex(fraud["omits"])).digest(), hidden)
            else:
                self.assertEqual(bytes.fromhex(fraud["lists"]), hidden)
        self.assertIsNone(RX.refute(T, honest.leaf(d.id)))
        true_attester = honest.leaf(d.id)["attests"][0]
        accused = {"leaf": honest.leaf(d.id), "kind": "attests", "lists": true_attester}
        self.assertFalse(RX.judge(T, honest.root, len(honest.keys), accused), "an id that does attest d is no lie")
        true_leaf = honest.leaf(d.id)
        listed = {"leaf": true_leaf, "kind": "payload", "omits": T.cells[bytes.fromhex(true_leaf["payload"][0])].encode().hex()}
        self.assertFalse(RX.judge(T, honest.root, len(honest.keys), listed), "an object the leaf lists refutes nothing")

    def test_24_a_fraud_proof_carries_its_own_evidence(self):
        """`portable` puts into `refute`'s proof the git objects from the tip's commit down to the object it names (and
        to the edge list that object's field names), and `judge_portable` decides it from the signed root and the tip's
        commit id alone, with no store. A git tree lists every entry, so the same path proves an id absent. A proof
        with one byte changed, under another tip, or against the honest root is refused, and an honest leaf has none."""
        c, d, vs = stale_invalid_chain()
        T = FR.Tip(V, c.repo, SCOPE, c.tip)
        honest = RX.Index(T)
        nowhere = hashlib.sha256(b"no such cell").digest()
        lies = (("attests", lambda e: [x for x in e if x != vs["ana"].id], d.id),
                ("seals", lambda e: e[1:], vs["ana"].id),
                ("attests", lambda e: sorted(e + [d.id]), d.id),        # d does not attest itself
                ("payload", lambda e: sorted(e + [nowhere]), d.id))     # no such cell at the tip
        absent = 0
        for kind, lie, target in lies:
            entries = {k: {kk: list(v) for kk, v in e.items()} for k, e in honest.entries.items()}
            entries[target][kind] = lie(entries[target][kind])
            if kind == "attests" and vs["ana"].id not in entries[target][kind]:
                entries[target]["payload"] = [x for x in entries[target]["payload"] if x != vs["ana"].id]
            liar = RX.Index(T, entries)
            fraud = RX.portable(T, RX.refute(T, liar.leaf(target)))
            self.assertTrue(RX.judge_portable(V, c.tip, liar.root, len(liar.keys), fraud), kind)
            if kind == "attests" and fraud["omits"]:
                self.assertEqual(len(fraud["proofs"]), 2, "the verdict and the edge list its attests field names")
                self.assertFalse(RX.judge_portable(V, c.tip, liar.root, len(liar.keys), fraud | {"proofs": fraud["proofs"][:1]}),
                                 "an edge kind needs the edge list shown")
            absent += any(RX.verify_object(c.tip, x) is None for x in fraud["proofs"])
            self.assertFalse(RX.judge_portable(V, c.tip, honest.root, len(honest.keys), fraud), "another root")
            other = json.loads(json.dumps(fraud))
            parent = c.repo.commit_chain(c.tip)[-2]
            self.assertFalse(RX.judge_portable(V, parent, liar.root, len(liar.keys), other), "another tip")
            for part in ("trees", "object", "commit"):
                bent = json.loads(json.dumps(fraud))
                x = bent["proofs"][0]
                if part not in x:
                    continue
                v = x[part][-1] if part == "trees" else x[part]
                v = v[:-2] + ("00" if v[-2:] != "00" else "01")
                if part == "trees":
                    x["trees"][-1] = v
                else:
                    x[part] = v
                self.assertFalse(RX.judge_portable(V, c.tip, liar.root, len(liar.keys), bent), (kind, part))
        self.assertEqual(absent, 1, "the id no cell has is shown absent by the tree that would list it")
        true_leaf = honest.leaf(d.id)
        accused = RX.portable(T, {"leaf": true_leaf, "kind": "attests", "lists": true_leaf["attests"][0]})
        self.assertFalse(RX.judge_portable(V, c.tip, honest.root, len(honest.keys), accused), "it does attest d")


def status(lens, d: bytes, grounded: bool = True):
    """(stands, Settled) of a cell, and Grounded where the frame is Grounded's."""
    st = (bool(lens["active"].get(d)) and not lens["stale"].get(d), bool(lens["settled"].get(d)))
    return (*st, bool(lens["grounded"].get(d))) if grounded else st


def frame_holds(test, repo, scope: str, tips, schemas=("contract", "decision", "question")) -> collections.Counter:
    """Over every tip of `tips` (a chain's tips, oldest first), every evaluated cell there, its frame for Settled and
    its frame for Grounded, and every later tip: if no object of the commits between touches the frame, the status at
    the later tip is the status at the earlier. Returns how often nothing touched, each reason something did, and how
    often the status then changed."""
    Ts = [FR.Tip(V, repo, scope, t) for t in tips]
    per = [FR.delta(Ts[j - 1], tips[j]) if j else None for j in range(len(tips))]
    wanted = {V.H_SCHEMA[s] for s in schemas}
    seen = collections.Counter()
    for i, T in enumerate(Ts):
        subjects = sorted(x for x, c in T.cells.items() if c.h_schema in wanted)
        if not subjects:
            continue
        atoms, memo = {}, {}
        open_ = {(d, gr): FR.frame(T, d, gr) for d in subjects for gr in (False, True)}
        for j in range(i + 1, len(Ts)):
            atoms.update(per[j][0])
            for (d, gr), fr in list(open_.items()):
                t = FR.touches(T, fr, atoms, per[j][1], per[j][2], memo)
                before, after = status(T.lens, d, gr), status(Ts[j].lens, d, gr)
                if t is None:
                    test.assertEqual(before, after, f"nothing touched the frame of {d.hex()[:8]} "
                                     f"({'Grounded' if gr else 'Settled'}) between tips {i} and {j}, yet its status changed")
                    seen["untouched"] += 1
                else:  # the same object touches it at every later tip
                    seen[t[0]] += 1
                    seen["changed"] += any(status(Ts[m].lens, d, gr) != before for m in range(j, len(Ts)))
                    del open_[(d, gr)]
    return seen


def random_walk(seed: int, rules: bytes, thr: int, steps: int):
    """A chain and its tips: a base, then `steps` random commits, each admitted by the gate or left out."""
    rnd = random.Random(seed)
    c = Chain(scratch(), rules=rules, admission=(thr, MEMBERS))
    tips = [c.tip]
    g, k = c.axiom("ground/g"), c.axiom("check/k")
    c.commit((g, MEMBERS[:thr]), (k, MEMBERS[:thr]))
    d1 = c.decision("decision/d1", [k], thr=2)
    d2 = c.decision("decision/d2", [d1], thr=1)
    e = V.Cell(h_schema=V.H_SCHEMA["decision"], h_slot_name=c.utf8(f"{SCOPE}/decision/e"), h_payload=c.utf8("e"),
               h_relies=c.hv([g.id]), slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY))
    q = V.Cell(V.H_SCHEMA["question"], c.utf8(f"{SCOPE}/question/q"), c.utf8("q"), slots=(V.H_SCHEMA["axiom"], V.H_EMPTY))
    c.commit(*((x, MEMBERS[:thr]) for x in (d1, d2, e, q)))
    tips.append(c.tip)
    plain, decisions, names = [g, k], [d1, d2, e], {}
    everything = [g, k, d1, d2, e, q]
    members = list(MEMBERS)
    for i in range(steps):
        who = rnd.choice(members)
        kind = rnd.choice(("axiom", "notice", "notice", "attest", "attest", "attest", "invalid", "seal", "seal", "retire",
                           "supersede", "answer", "rotate"))
        try:
            if kind == "axiom":
                x = c.axiom(f"cell/{i}", [rnd.choice(plain)])
                c.commit((x, who))
                plain.append(x)
            elif kind == "notice":
                x = c.axiom(f"notice/{i}", invalidates=[rnd.choice(everything)])
                c.commit((x, who))
            elif kind in ("attest", "invalid"):
                d = rnd.choice(decisions)
                x = c.verdict(d, f"verdict/{i}", [rnd.choice(plain)], verifier=rnd.choice(members),
                              code=V.H_ATTESTED if kind == "attest" else V.H_VERDICT_INVALID)
                c.commit((x, who))
            elif kind == "seal":
                c.seal(rnd.choice(everything), who)
                x = None
            elif kind == "retire":
                x = c.axiom(f"retire/{i}", retires=[rnd.choice(everything)])
                c.commit((x, who))
            elif kind == "supersede":
                old = rnd.choice(plain)
                name = names.get(old.id, V.parse_utf8(c.repo.read_cas_tree(c.tip)[0][old.h_slot_name]).split("/", 1)[1])
                x = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=c.utf8(f"{SCOPE}/{name}"), h_payload=c.utf8(f"again/{i}"),
                           h_supersedes=c.hv([old.id]), h_loss=c.utf8("replaced"))
                c.commit((x, who))
                names[x.id] = name
                plain.append(x)
            elif kind == "answer":
                x = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=c.utf8(f"{SCOPE}/answer/{i}"),
                           h_payload=c.utf8(f"answer/{i}"), h_attests=c.hv([q.id]))
                c.commit((x, who))
            else:
                keep = rnd.sample(list(MEMBERS), rnd.choice((2, 3)))
                x = c.rotate(tuple(sorted(keep)), f"rotation/{i}", sealer=who)
        except V.VarsError:
            c.atoms = {}
            continue
        if x is not None:
            everything.append(x)
        c.ctx = c.governing()
        members = [m for m in MEMBERS if c.pk[m] in roster_keys(c)] or list(MEMBERS)
        tips.append(c.tip)
    return c, tips


def roster_keys(c) -> set:
    atoms, cells, _ = c.repo.read_cas_tree(c.tip)
    return set(V.parse_hvec(atoms[V.parse_pol1(atoms[cells[c.ctx].slots[0]])[1]], require_sorted=True))


def mutants(only=()) -> int:
    """Run every named test unmutated (refuse a red baseline), then each mutant of mutants.json against a copy of
    its file (check.py, or the `file` it names: frame.py), with no bytecode cache: its test must fail on an
    assertion. Returns the number that survived."""
    ms = json.loads((HERE / "mutants.json").read_text())
    if only:
        missing = sorted(set(only) - set(ms))
        if missing:
            print(f"no such mutant: {' '.join(missing)}")
            return len(missing)
        ms = {mid: m for mid, m in ms.items() if mid in only}
    env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
    run = lambda test, extra: subprocess.run([sys.executable, str(Path(__file__)), f"T.{test}"],  # noqa: E731
                                             capture_output=True, text=True, env={**env, **extra}, cwd=ROOT)
    for test in sorted({m["kills"] for m in ms.values()}):
        if run(test, {}).returncode:
            print(f"BASELINE_RED {test}")
            return len(ms)
    survived = 0
    sources = {name: (HERE / name).read_text() for name in MUTATED}
    for mid, m in ms.items():
        name = m.get("file", "check.py")
        src = sources[name]
        if src.count(m["find"]) != 1:
            print(f"lost     {mid}: its text is not in {name} exactly once")
            survived += 1
            continue
        copy = WORK / f"mutant-{mid}.py"
        try:
            copy.write_text(src.replace(m["find"], m["replace"]))
            r = run(m["kills"], {MUTATED[name]: str(copy)})
        finally:
            copy.unlink(missing_ok=True)
        out = r.stdout + r.stderr
        killed = r.returncode != 0 and "AssertionError" in out and "Error: " not in out.replace("AssertionError: ", "")
        print(f"{'killed' if killed else 'SURVIVED'} {mid}: {m['kills']}")
        survived += not killed
    return survived


if __name__ == "__main__":
    if sys.argv[1:2] == ["--mutants"]:  # --mutants [ID...]: all of them, or the named ones
        sys.exit(1 if mutants(sys.argv[2:]) else 0)
    unittest.main(argv=[sys.argv[0], *sys.argv[1:]], verbosity=1)
