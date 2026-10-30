"""Tests of the witness spike (README.md). Run from the repository root:

    .venv/bin/python experiments/witness/test_witness.py              # the tests
    .venv/bin/python experiments/witness/test_witness.py --mutants    # each mutant in mutants.json must fail its test

A mutant must fail its named test on an assertion (an error is not a kill), and the named tests must pass unmutated
first. Chains are built through the real gate (vars1.py); the checker under test is check.py, or the file named by
WITNESS_SOURCE (a mutant).
"""
import contextlib
import hashlib
import importlib.util
import io
import itertools
import json
import os
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
import prove as PR  # noqa: E402


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


SOURCE = Path(os.environ.get("WITNESS_SOURCE", HERE / "check.py"))
CK = _load("witness_check", SOURCE)
g6 = _load("g6", ROOT / "experiments" / "g6" / "g6.py")
WORK = Path.home() / "Projects" / ".worktrees" / "witness-work"
WORK.mkdir(parents=True, exist_ok=True)
MEMBERS = ("ana", "bo", "cy")
SCOPE = "proj"
_CACHE = {}


def scratch() -> Path:
    return Path(tempfile.mkdtemp(dir=WORK))


class Chain:
    """A hand-built chain admitted through the gate: genesis sealed by ana, every cell sealed by whoever files it."""

    def __init__(self, path: Path, rules: bytes = V.H_LENS_KERNEL, admission=(1, MEMBERS)) -> None:
        subprocess.run(["git", "init", "-q", str(path)], check=True)
        for k, v in (("user.name", "witness"), ("user.email", "witness@local"), ("gc.auto", "0")):
            subprocess.run(["git", "-C", str(path), "config", k, v], check=True)
        self.path, self.repo = path, V.GitVarsRepo(path)
        self.sk = {m: hashlib.sha256(b"witness/" + m.encode()).digest() for m in MEMBERS}
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
        return CK.check(str(self.path), term, pin)


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


def g6_chain(i: int):
    """History i of the seed `witness` (S, L, S, ...), built by the G6 generator through the gate, before and after
    its failed ground's notice is admitted."""
    if i not in _CACHE:
        s, size = g6.seeds("witness", i + 1)[i]
        h = g6.history(s, size)
        path = scratch()
        ch = g6.build_chain(h, s, path)
        repo, before = ch["repo"], ch["repo"].ref_commit(g6.SCOPE)
        a = {}
        put = lambda raw: (a.__setitem__(V.sha256(raw), raw), V.sha256(raw))[1]  # noqa: E731
        notice = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=put(V.atom_utf8(f"{g6.SCOPE}/notice/{h['failed']}")),
                        h_payload=put(V.atom_utf8(f"{h['failed']} was found invalid")),
                        h_invalidates=put(V.atom_hvec([ch["ids"][h["failed"]]])))
        ctx = repo._evaluate_commit_chain(g6.SCOPE, repo.commit_chain(before))["active_scope_id"]
        after = repo.build_candidate_commit(g6.SCOPE, a, [notice], [V.Seal.sign(g6._key(s, ch["reporter"]), notice.id, ctx)],
                                            parent_commit=before)
        repo.admit_and_advance(g6.SCOPE, after, expected_old=before)
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
        self.assertEqual((CK.H_EMPTY, CK.H_ATTESTED, CK.H_VERDICT_INVALID, CK.H_LENS_KERNEL),
                         (V.H_EMPTY, V.H_ATTESTED, V.H_VERDICT_INVALID, V.H_LENS_KERNEL))

    def test_03_before_the_failure_every_decision_is_held(self):
        """On a G6 history of each size, every decision in force before the notice gets a witness the checker holds."""
        for i in (0, 1):
            h, ch, path, before, _ = g6_chain(i)
            for d in h["decisions"]:
                r = CK.check(str(path), PR.prove(ch["repo"], g6.SCOPE, ch["ids"][d["id"]], before))
                self.assertEqual(r["result"], "HELD", (i, d["id"], r))

    def test_04_after_the_failure_held_only_what_the_lens_settles(self):
        """After the notice: a decision the lens settles gets a witness the checker holds, one it does not gets none;
        and no term over any subset of a decision's verdicts, each with its whole cone, is HELD for a decision the
        lens does not settle."""
        seen = set()
        for i in (0, 1):
            h, ch, path, _, after = g6_chain(i)
            repo, lens = ch["repo"], ch["repo"].lens(g6.SCOPE)
            for dd in h["decisions"]:
                d = ch["ids"][dd["id"]]
                settled = bool(lens["settled"].get(d) and lens["active"].get(d) and not lens["stale"].get(d))
                if settled:
                    self.assertEqual(CK.check(str(path), PR.prove(repo, g6.SCOPE, d, after))["result"], "HELD", dd)
                else:
                    with self.assertRaises(PR.NotHeld):
                        PR.prove(repo, g6.SCOPE, d, after)
                vs = verdicts_on(repo, after, d)
                for r in range(1, len(vs) + 1):
                    for sub in itertools.combinations(vs, r):
                        out = CK.check(str(path), term(repo, after, d, sub))
                        seen.add((out["result"], out.get("code")))
                        if out["result"] == "HELD":
                            self.assertTrue(settled, (i, dd["id"], out))
        self.assertTrue({("NOT_COVERED", "KILL_EDGE"), ("REFUSED", "THRESHOLD"), ("HELD", None)} <= seen, seen)

    def test_05_a_term_that_hides_part_of_its_cone_is_refused(self):
        """A lost decision cannot be passed off by leaving the fallen ground or a stale verdict out of the cone."""
        h, ch, path, _, after = g6_chain(0)
        repo, kinds = ch["repo"], g6.kinds(h)
        fallen = ch["ids"][h["failed"]]
        own = next(ch["ids"][x] for x, k in kinds.items() if k == "own")
        cone = [x for x in closure(repo, after, [own, *verdicts_on(repo, after, own)]) if x != fallen]
        r = CK.check(str(path), term(repo, after, own, verdicts_on(repo, after, own), cone=cone))
        self.assertEqual((r["result"], r.get("code")), ("REFUSED", "CONE_OPEN"))
        lost = next(ch["ids"][x] for x, k in kinds.items() if k == "approvals")
        vs = verdicts_on(repo, after, lost)
        r = CK.check(str(path), term(repo, after, lost, vs, cone=closure(repo, after, [lost])))
        self.assertEqual((r["result"], r.get("code")), ("REFUSED", "CONE_OPEN"), "a stale verdict outside the cone")
        r = CK.check(str(path), term(repo, after, own, verdicts_on(repo, after, own)))
        self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "KILL_EDGE"), "the whole cone holds the fallen ground")

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
        """Settled by the lens but outside the fragment: a ground whose notice was itself invalidated, an INVALID
        verdict on the decision, a rotation, the v2 rules. And a decision whose unauthorized supersedes edge leaves it
        not Active is not HELD either."""
        c = Chain(scratch())
        g, k, d, vs = c.basic()
        n = c.axiom("notice/g", invalidates=[g])
        c.commit((n, "cy"))
        m = c.axiom("notice/not-g", invalidates=[n])
        c.commit((m, "bo"))
        self.assertTrue(c.repo.lens(SCOPE)["settled"].get(d.id), "the notice is withdrawn: the lens settles d")
        r = c.check(PR.prove(c.repo, SCOPE, d.id))
        self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "KILL_EDGE"), r)

        c = Chain(scratch())
        g, k, d, vs = c.basic()
        bad = c.verdict(d, "decision/d/invalid-by-cy", [k], code=V.H_VERDICT_INVALID, verifier="cy")
        c.commit((bad, "cy"))
        self.assertTrue(c.repo.lens(SCOPE)["settled"].get(d.id), "cy's INVALID withdraws cy's verifier only")
        r = c.check(PR.prove(c.repo, SCOPE, d.id))
        self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "INVALID_VERDICT"), r)

        c = Chain(scratch())
        g, k, d, vs = c.basic()
        a = {}
        pol = c.pol(a, 1, MEMBERS)
        s1 = V.Cell(V.H_SCHEMA["scope"], c.put(a, V.atom_utf8(f"{SCOPE}/SCOPE")), c.put(a, V.atom_utf8("same roster")),
                    h_supersedes=c.put(a, V.atom_hvec([c.scope.id])), h_loss=c.put(a, V.atom_utf8("rotation")),
                    slots=(pol, pol, V.H_LENS_KERNEL))
        c.atoms = a
        c.commit((s1, "ana"))
        self.assertTrue(c.repo.lens(SCOPE)["settled"].get(d.id))
        r = c.check(term(c.repo, c.tip, d.id, [vs["ana"].id, vs["bo"].id]))
        self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "SCOPES"), r)

        c = Chain(scratch(), rules=V.H_LENS_KERNEL_V2)
        g, k, d, vs = c.basic()
        self.assertTrue(c.repo.lens(SCOPE)["settled"].get(d.id))
        r = c.check(PR.prove(c.repo, SCOPE, d.id))
        self.assertEqual((r["result"], r.get("code")), ("NOT_COVERED", "RULES"), r)

        c = Chain(scratch())
        g = c.axiom("ground/g")
        c.commit((g, "ana"))
        d1 = c.decision("decision/d", [g], thr=3, members=MEMBERS)
        c.commit((d1, ("ana", "bo")))
        d2 = c.decision("decision/d", [g], thr=1, members=MEMBERS, supersedes=[d1])
        v2 = c.verdict(d2, "decision/d2/by-ana", [g])
        c.commit((d2, "cy"), (v2, "ana"))
        lens = c.repo.lens(SCOPE)
        self.assertFalse(lens["active"].get(d2.id), "cy meets neither d1's policy (3 of 3) nor any of its initial "
                         "endorsers (ana, bo): the supersedes edge is not authorized, so d2 is not Active")
        r = c.check(term(c.repo, c.tip, d2.id, [v2.id]))
        self.assertNotEqual(r["result"], "HELD", r)
        self.assertEqual(r.get("code"), "KILL_EDGE", r)

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
        crash = CK.check_text
        CK.check_text = lambda *a: 1 // 0
        try:
            self.assertEqual(cli(text.encode()), (3, None))
        finally:
            CK.check_text = crash


def mutants() -> int:
    """Run every named test unmutated (refuse a red baseline), then each mutant of mutants.json against a copy of
    check.py, with no bytecode cache: its test must fail on an assertion. Returns the number that survived."""
    ms = json.loads((HERE / "mutants.json").read_text())
    env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
    run = lambda test, extra: subprocess.run([sys.executable, str(Path(__file__)), f"T.{test}"],  # noqa: E731
                                             capture_output=True, text=True, env={**env, **extra}, cwd=ROOT)
    for test in sorted({m["kills"] for m in ms.values()}):
        if run(test, {}).returncode:
            print(f"BASELINE_RED {test}")
            return len(ms)
    survived = 0
    src = (HERE / "check.py").read_text()
    for mid, m in ms.items():
        if src.count(m["find"]) != 1:
            print(f"lost     {mid}: its text is not in check.py exactly once")
            survived += 1
            continue
        copy = WORK / f"mutant-{mid}.py"
        try:
            copy.write_text(src.replace(m["find"], m["replace"]))
            r = run(m["kills"], {"WITNESS_SOURCE": str(copy)})
        finally:
            copy.unlink(missing_ok=True)
        out = r.stdout + r.stderr
        killed = r.returncode != 0 and "AssertionError" in out and "Error: " not in out.replace("AssertionError: ", "")
        print(f"{'killed' if killed else 'SURVIVED'} {mid}: {m['kills']}")
        survived += not killed
    return survived


if __name__ == "__main__":
    if sys.argv[1:] == ["--mutants"]:
        sys.exit(1 if mutants() else 0)
    unittest.main(argv=[sys.argv[0], *sys.argv[1:]], verbosity=1)
