#!/usr/bin/env python3
"""Check a witness that a decision is Settled at a tip of a VARS-1 chain, without the lens.

    python3 -I check.py REPO TERM.json [--scope-cell HEX]
    python3 -I check.py --lean REPO TERM.json [--scope-cell HEX] | proofs/.lake/build/bin/vars1witness
    python3 -I check.py --lean --prove REPO TERM.json [--scope-cell HEX] | proofs/.lake/build/bin/vars1witness --prove
    python3 -I check.py --lean --ground REPO TERM.json [--scope-cell HEX] | proofs/.lake/build/bin/vars1witness --ground
    python3 -I check.py --unfounded REPO TERM.json [--scope-cell HEX]   # a certificate that it is not Grounded

A witness (format `minds.witness.held@1`) is a proof term for one decision at one commit: the decision's cone (the
cells it and its counted verdicts rely on, closed under `relies`) and seals, by distinct keys of its evaluator
policy, on ATTESTED verdicts that judge it. This file reads the commit's tree with git, checks the term against the
store's bytes and answers HELD, REFUSED or NOT_COVERED. It shares no code with vars1.py or verify/minds_verify.py:
the constants are VARS-1-SPEC.md's tables, the parsers and the Ed25519 check are its own, standard library only.

What HELD rests on (README.md):
- the positive part is checked from bytes: every object hashes to its name, the seals verify under their keys, each
  under a scope of the governing chain and by a key of its roster, the keys are in the evaluator policy that the
  decision's id fixes, and the threshold is met;
- the negative part (no cell invalidates, retires or supersedes a cone cell; no INVALID verdict on the decision,
  under an endorsing verdict's verifier id, is sealed by the endorsing key; the scope cells are the governing chain,
  under v1 or v2, and its newest rotation cannot be waiting; no foreign cells) is read over the store at the tip, so
  it holds only if that store is the admitted chain, complete: the reader's pin, which this file does not check (it
  runs no gate).

Outside the fragment the answer is NOT_COVERED, never HELD: the lens decides there.

The term must read one way: a term that is not UTF-8 JSON, or whose object names a key twice (Python keeps the last
value, other readers the first), is REFUSED (FORMAT), never read by one convention. Exit 0 is HELD, 1 REFUSED or
NOT_COVERED, 2 a wrong command line; 3 is an error of this checker, which no verdict uses.
"""
import hashlib
import json
import re
import subprocess
import sys
from typing import Dict, List, Optional, Set, Tuple

FORMAT = "minds.witness.held@1"

# VARS-1-SPEC.md §1.1 intrinsics and §2 standard schema ids
H_EMPTY = bytes.fromhex("f7607964cdb9f811072ded78efc20c622f54483eb7b101da5605329dc908872e")
H_ATTESTED = bytes.fromhex("7e5f2fdf987cac883a0453016a9541553d700e3a6f3a807839f22d5ca07b802c")
H_VERDICT_INVALID = bytes.fromhex("b3966965c112d6d2613255fc018e34774dbc17c8517705b95946ea925b95096d")
H_LENS_KERNEL = bytes.fromhex("874e714dd14e6d7c144a4c377ae649f4124ea3788b17fa1ff86cf1be8a168ecb")
H_LENS_KERNEL_V2 = bytes.fromhex("1ca798b5013bf45735d3de836ecff23ca148e5bac2f6ca2c7d6289c2cf26707e")
H_META_SCHEMA = bytes.fromhex("7f0f250c08d367c8f2ba2c3b700f1a9bacbb44c240dade81c5c39c9ea7f9f15e")
H_OWNER = bytes.fromhex("4f97d7922a77cd279f75b8483542a9235330d4402ab15373e23c21bb7877905e")
SCHEMA = {name: bytes.fromhex(h) for name, h in {
    "axiom": "aaf70509e078bf1f833492eb82a116e4122232d424cf1668c05a9dd25855dcda",
    "contract": "391bbd2090d93f580fe033df9109cff948d46a07db24b9db05d55dc84e84277b",
    "computation": "1c97bc0b74ffc978ade540c55592b294b0d9f2502b94b969f89ef00d99dd10bb",
    "checkpoint": "77655a8f5ca5b1c6347634e9a5848fdacee6efefd58569242d39f43410747639",
    "cycle_witness": "065f1b5b54fa199d65fb7f3e185e6f024d7523e829af1ad98269de018a8fb548",
    "decision": "5a48e9c69afc5c3cebb3ca2980052151f2aaa539052702e0e23f7ba5504eb6fb",
    "question": "1293a1513baa6e0e1edfdcf8c8f4b992efa1391ddbc0889efe9698d59c9b0cdf",
    "acceptance": "c661936c020c0d817b8516b93454af5a30fe4282d854c1b0f628731c80f95d66",
    "scope": "9aab50548f8fc7c5e2090fa89a73440af7de5e92d800b928261f13f20a4bd2a9",
    "verdict": "ad702699d5fc7b3d94138c38643c9889f1520a6e1c20760aa6b11a8e273dfdae",
    "projection": "8029ae880cb62a8034f47ec44e8f5c5982ebc14a14be2c6893a3ab8f968aa818",
}.items()}
STANDARD = set(SCHEMA.values())


class Refused(Exception):
    def __init__(self, result: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.result, self.code, self.detail = result, code, detail


def refuse(code: str, detail: str) -> Refused:
    return Refused("REFUSED", code, detail)


def uncovered(code: str, detail: str) -> Refused:
    return Refused("NOT_COVERED", code, detail)


# --- Ed25519 (RFC 8032), strict and cofactorless -------------------------------------------------------------------

P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = -121665 * pow(121666, P - 2, P) % P
SQRT_M1 = pow(2, (P - 1) // 4, P)
ZERO = (0, 1, 1, 0)


def _add(p, q):
    x1, y1, z1, t1 = p
    x2, y2, z2, t2 = q
    a, b = (y1 - x1) * (y2 - x2) % P, (y1 + x1) * (y2 + x2) % P
    c, d = 2 * t1 * t2 * D % P, 2 * z1 * z2 % P
    e, f, g, h = b - a, d - c, d + c, b + a
    return (e * f % P, g * h % P, f * g % P, e * h % P)


def _mul(s: int, p):
    q = ZERO
    while s:
        if s & 1:
            q = _add(q, p)
        p, s = _add(p, p), s >> 1
    return q


def _decode(b: bytes):
    """A point from its canonical 32-byte encoding, else None."""
    y = int.from_bytes(b, "little")
    sign, y = y >> 255, y & ((1 << 255) - 1)
    if y >= P:
        return None
    x2 = (y * y - 1) * pow(D * y * y + 1, P - 2, P) % P
    if x2 == 0:
        if sign:
            return None
        return (0, y, 1, 0)
    x = pow(x2, (P + 3) // 8, P)
    if (x * x - x2) % P:
        x = x * SQRT_M1 % P
    if (x * x - x2) % P:
        return None
    if x & 1 != sign:
        x = P - x
    return (x, y, 1, x * y % P)


def _encode(p) -> bytes:
    x, y, z, _ = p
    zi = pow(z, P - 2, P)
    x, y = x * zi % P, y * zi % P
    return (y | ((x & 1) << 255)).to_bytes(32, "little")


B = _decode((4 * pow(5, P - 2, P) % P).to_bytes(32, "little"))


def ed25519_verify(pub: bytes, msg: bytes, sig: bytes) -> bool:
    """[S]B = R + [k]A with A and R canonical, S < L, and A not of small order."""
    if len(pub) != 32 or len(sig) != 64:
        return False
    a, r, s = _decode(pub), _decode(sig[:32]), int.from_bytes(sig[32:], "little")
    if a is None or r is None or s >= L:
        return False
    if _encode(_mul(8, a)) == _encode(ZERO):
        return False
    k = int.from_bytes(hashlib.sha512(sig[:32] + pub + msg).digest(), "little") % L
    return _encode(_mul(s, B)) == _encode(_add(r, _mul(k, a)))


# --- the store at a commit -----------------------------------------------------------------------------------------

KILLS = ("supersedes", "retires", "invalidates")  # the Lean checker's kinds 0, 1, 2
ENTRY = re.compile(r"(100644) blob ([0-9a-f]{40}|[0-9a-f]{64})\tcas/(atoms|cells|seals)/([0-9a-f]{2})/([0-9a-f]{62})")
EDGES = ("relies", "attests", "supersedes", "retires", "invalidates")


def _git(repo: str, *args: str, data: Optional[bytes] = None) -> bytes:
    r = subprocess.run(["git", "-C", repo, *args], input=data, capture_output=True)
    if r.returncode:
        raise refuse("STORE", f"git {args[0]} failed: {r.stderr.decode(errors='replace').strip()}")
    return r.stdout


def read_store(repo: str, tip: str) -> Dict[str, Dict[bytes, bytes]]:
    """Every object of the commit's tree, each checked to hash to its name; any other entry is refused."""
    if not isinstance(tip, str) or not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", tip):
        raise refuse("TIP", "the tip is not a full lowercase commit id")
    if _git(repo, "rev-parse", "--verify", "--end-of-options", tip + "^{commit}").decode().strip() != tip:
        raise refuse("TIP", "the tip does not name itself as a commit")
    lines = _git(repo, "ls-tree", "-r", "--full-tree", tip).decode().splitlines()
    entries = []
    for line in lines:
        m = ENTRY.fullmatch(line)
        if not m:
            raise refuse("STORE", f"not a store entry: {line}")
        entries.append((m.group(2), m.group(3), bytes.fromhex(m.group(4) + m.group(5))))
    out = _git(repo, "cat-file", "--batch", data="".join(f"{oid}\n" for oid, _, _ in entries).encode())
    store: Dict[str, Dict[bytes, bytes]] = {"atoms": {}, "cells": {}, "seals": {}}
    pos = 0
    for oid, kind, name in entries:
        header_end = out.index(b"\n", pos)
        header = out[pos:header_end].split()
        if header[1:2] == [b"blob"]:
            size = int(header[2])
            raw, pos = out[header_end + 1:header_end + 1 + size], header_end + 2 + size
        else:  # missing: no bytes, which the hash refuses
            raw, pos = b"", header_end + 1
        if hashlib.sha256(raw).digest() != name:
            raise refuse("STORE", f"cas/{kind}/{name.hex()} does not hash to its name")
        store[kind][name] = raw
    return store


def cell(raw: bytes) -> Dict[str, object]:
    if len(raw) < 296 or raw[:7] != b"VAR1\0\0\0" or raw[7] > 64 or len(raw) != 296 + 32 * raw[7]:
        raise refuse("STORE", "a cell is malformed")
    f = lambda i: raw[8 + 32 * i:40 + 32 * i]  # noqa: E731
    out = {"schema": f(0), "name": f(1), "payload": f(2), "loss": f(8),
           "slots": [raw[296 + 32 * j:328 + 32 * j] for j in range(raw[7])]}
    out.update(zip(EDGES, (f(3), f(4), f(5), f(6), f(7))))
    return out


def seal(raw: bytes) -> Dict[str, bytes]:
    if len(raw) != 164 or raw[:4] != b"SEAL":
        raise refuse("STORE", "a seal is malformed")
    return {"target": raw[4:36], "ctx": raw[36:68], "key": raw[68:100], "signature": raw[100:164], "signed": raw[:100]}


def hvec(atoms: Dict[bytes, bytes], h: bytes) -> List[bytes]:
    if h == H_EMPTY:
        return []
    raw = atoms.get(h)
    if raw is None or raw[:4] != b"HVEC" or (len(raw) - 4) % 32:
        raise refuse("STORE", f"{h.hex()} is not a stored HVEC atom")
    items = [raw[4 + 32 * i:36 + 32 * i] for i in range((len(raw) - 4) // 32)]
    if any(a >= b for a, b in zip(items, items[1:])):
        raise refuse("STORE", f"{h.hex()} is not strictly ascending")
    return items


def policy(atoms: Dict[bytes, bytes], h: bytes) -> Tuple[int, Set[bytes]]:
    raw = atoms.get(h)
    if raw is None or len(raw) != 38 or raw[:4] != b"POL1":
        raise refuse("STORE", f"{h.hex()} is not a stored POL1 atom")
    keys = hvec(atoms, raw[6:38])
    thr = int.from_bytes(raw[4:6], "big")
    if not 1 <= thr <= len(keys):
        raise refuse("STORE", f"{h.hex()} has a threshold outside its keys")
    return thr, set(keys)


def origin(atoms: Dict[bytes, bytes], c: Dict[str, object]) -> str:
    raw = atoms.get(c["name"])
    try:
        if raw is None or raw[:4] != b"UTF8":
            raise ValueError
        return raw[4:].decode("utf-8").split("/", 1)[0]
    except ValueError:
        raise refuse("STORE", "a cell's name is not a stored UTF8 atom") from None


# --- the term ------------------------------------------------------------------------------------------------------

def _ids(xs, what: str) -> List[bytes]:
    if not isinstance(xs, list) or not all(isinstance(x, str) and re.fullmatch(r"[0-9a-f]{64}", x) for x in xs):
        raise refuse("FORMAT", f"{what} is not a list of 64-hex ids")
    return [bytes.fromhex(x) for x in xs]


def read_term(raw: bytes) -> object:
    """The term in `raw`, read one way only: bytes that are not UTF-8 JSON (Python's json would read NaN, Infinity
    and -Infinity, which are not JSON), or an object that names a key twice, are REFUSED (FORMAT)."""
    def one_reading(pairs: List[Tuple[str, object]]) -> Dict[str, object]:
        keys = [k for k, _ in pairs]
        if len(set(keys)) != len(keys):
            raise refuse("FORMAT", "an object of the term names a key twice")
        return dict(pairs)

    def not_json(token: str) -> object:
        raise refuse("FORMAT", f"{token} is not JSON")
    try:
        return json.loads(raw.decode("utf-8"), object_pairs_hook=one_reading, parse_constant=not_json)
    except ValueError:
        raise refuse("FORMAT", "the term is not UTF-8 JSON") from None


def check_text(repo: str, raw: bytes, scope_cell: Optional[bytes] = None) -> Dict[str, object]:
    """check() of the term in `raw` (read_term)."""
    try:
        term = read_term(raw)
    except Refused as e:
        return {"result": e.result, "code": e.code, "detail": e.detail}
    return check(repo, term, scope_cell)


def check(repo: str, term: Dict[str, object], scope_cell: Optional[bytes] = None) -> Dict[str, object]:
    """HELD iff the term proves its decision Settled at its tip, within the fragment; otherwise REFUSED (the term is
    wrong) or NOT_COVERED (the fragment does not reach this decision: ask the lens)."""
    try:
        return {"result": "HELD", **_check(repo, term, scope_cell)}
    except Refused as e:
        return {"result": e.result, "code": e.code, "detail": e.detail}


def _read(repo: str, term: Dict[str, object], pin: Optional[bytes]):
    """The term's parts and the store at its tip, decoded, within the fragment: the scope cells form one chain of
    rotations from the genesis to the one scope cell no other supersedes (the reader's pin, if given), each naming the
    v1 or the v2 rules, and the newest rotation cannot be waiting; no foreign cell. Returns the chain, tip first. Both
    checkers read the store through here."""
    if not isinstance(term, dict) or term.get("format") != FORMAT or not isinstance(term.get("scope"), str):
        raise refuse("FORMAT", f"not a {FORMAT} term")
    d = _ids([term.get("decision")], "decision")[0]
    cone = set(_ids(term.get("cone"), "cone"))
    ends = term.get("endorsements")
    if not isinstance(ends, list) or not all(isinstance(e, dict) and set(e) == {"verdict", "seal"} for e in ends):
        raise refuse("FORMAT", "endorsements are not a list of {verdict, seal}")
    ends = [(_ids([e["verdict"]], "verdict")[0], _ids([e["seal"]], "seal")[0]) for e in ends]
    atoms, cells, seals, chain, sc = _fragment(repo, term, pin)
    return d, cone, ends, atoms, cells, seals, chain, sc


def _fragment(repo: str, term: Dict[str, object], pin: Optional[bytes]):
    """The store at the term's tip, decoded, within the fragment (see `_read`)."""
    store = read_store(repo, term.get("tip"))
    atoms = store["atoms"]
    cells = {cid: cell(raw) for cid, raw in store["cells"].items()}
    seals = {sid: seal(raw) for sid, raw in store["seals"].items()}

    # the fragment: the scope cells that governed, under v1 or v2, and nothing foreign
    scopes = {cid: c for cid, c in cells.items() if c["schema"] == SCHEMA["scope"]}
    if any(len(c["slots"]) != 3 for c in scopes.values()):
        raise refuse("STORE", "a scope cell is malformed")
    superseded = {t for c in scopes.values() for t in hvec(atoms, c["supersedes"])}
    tips = [cid for cid in scopes if cid not in superseded]
    if len(tips) != 1:
        raise uncovered("SCOPES", f"{len(tips)} scope cells that no other supersedes (a vetoed rules change?)")
    tip = tips[0]
    if pin is not None and pin != tip:
        if pin in superseded:
            raise uncovered("WAITING", "a scope cell supersedes the pinned one: a rotation waits, or the pin is old")
        raise refuse("SCOPE", "the scope cell is not the one the reader pinned")
    # the governing chain: the tip's scope, then the one scope each supersedes, back to the genesis. Cell ids name
    # their content, so supersedes edges form no cycle, and with one tip every scope cell of the store is on it
    chain = [tip]
    while hvec(atoms, scopes[chain[-1]]["supersedes"]):
        prev = hvec(atoms, scopes[chain[-1]]["supersedes"])
        if len(prev) != 1 or prev[0] not in scopes:
            raise refuse("STORE", "a scope cell does not supersede exactly one scope cell")
        chain.append(prev[0])
    sc = scopes[tip]
    if origin(atoms, sc) != term["scope"]:
        raise refuse("SCOPE", "the store's scope is not the term's")
    if any(cid not in STANDARD and origin(atoms, c) != term["scope"] for cid, c in cells.items()):
        raise uncovered("FOREIGN", "the store holds foreign cells")
    if any(scopes[x]["slots"][2] not in (H_LENS_KERNEL, H_LENS_KERNEL_V2) for x in chain):
        raise uncovered("RULES", "a scope names rules other than v1 and v2")
    # only the newest rotation can still wait (a new scope is refused while one waits, E-24); under v2 it waits if it
    # removes a key without its seal or changes the rules (§4.1 latches 4a, 4b), so the fragment leaves those out
    if len(chain) > 1:
        new, base = scopes[chain[0]], scopes[chain[1]]
        if base["slots"][2] != H_LENS_KERNEL and (new["slots"][2] != base["slots"][2] or any(
                not policy(atoms, base["slots"][i])[1] <= policy(atoms, new["slots"][i])[1] for i in (0, 1))):
            raise uncovered("WAITING", "the newest rotation removes a key or changes the rules under v2: it may wait")
    return atoms, cells, seals, chain, sc


# --- the rules both checkers read the store by ----------------------------------------------------------------------

def _and(xs) -> Optional[bool]:
    """Kleene's AND: False if one is False, else None if one is None, else True."""
    out: Optional[bool] = True
    for x in xs:
        if x is False:
            return False
        if x is None:
            out = None
    return out


def _or(xs) -> Optional[bool]:
    """Kleene's OR: True if one is True, else None if one is None, else False."""
    out: Optional[bool] = False
    for x in xs:
        if x is True:
            return True
        if x is None:
            out = None
    return out


class Rules:
    """The rules of the Lean checker (proofs/Vars1/Witness.lean), read over the store at the tip. Each answer is True
    when the Lean checker can derive it, False when it can derive the opposite (an edge `unlatched` against `latch`, a
    cell `dead` against `eff`, ...), and None when the store does not decide it: an edge whose quorum fails while a key
    of its target seals its source (the author clause reads InitialEndorsers, fixed at the target's birth), an edge to
    an acceptance cell, or one from a scope or schema cell whose quorum is met."""

    def __init__(self, atoms, cells, seals, chain, scope: str) -> None:
        self.atoms, self.cells, self.seals, self.chain, self.scope = atoms, cells, seals, chain, scope
        self.rosters = {x: policy(atoms, cells[x]["slots"][0])[1] for x in chain}
        self.on: Dict[bytes, List[bytes]] = {}
        for sid, y in seals.items():
            self.on.setdefault(y["target"], []).append(sid)
        self.sources: Dict[Tuple[str, bytes], List[bytes]] = {}
        for cid in sorted(cells):
            for kind in KILLS:
                for t in hvec(atoms, cells[cid][kind]):
                    self.sources.setdefault((kind, t), []).append(cid)
        self.ok: Dict[bytes, bool] = {}
        self.memo: Dict[tuple, Optional[bool]] = {}

    def verifies(self, sid: bytes) -> bool:
        if sid not in self.ok:
            y = self.seals[sid]
            self.ok[sid] = ed25519_verify(y["key"], y["signed"], y["signature"])
        return self.ok[sid]

    def into(self, kind: str, x: bytes) -> List[bytes]:
        """The cells with an edge of `kind` to `x`."""
        return self.sources.get((kind, x), [])

    def sealers(self, y: bytes, ctx: bytes) -> Set[bytes]:
        """The keys of the verified seals on `y` under the scope cell `ctx`, by keys of its admission roster."""
        return {self.seals[sid]["key"] for sid in self.on.get(y, ()) if self.seals[sid]["ctx"] == ctx
                and self.seals[sid]["key"] in self.rosters[ctx] and self.verifies(sid)}

    def local(self, x: bytes) -> bool:
        return x in STANDARD or origin(self.atoms, self.cells[x]) == self.scope

    def non_inv(self, w: bytes) -> bool:
        c = self.cells[w]
        return c["schema"] == SCHEMA["verdict"] and c["slots"][1:2] != [H_VERDICT_INVALID]

    def pol_at(self, ctx: bytes, x: bytes) -> bytes:
        """Pol(x) while `ctx` governed (§4.1's table, the acceptance row aside)."""
        c, adm = self.cells[x], self.cells[ctx]["slots"][0]
        if c["schema"] in (SCHEMA["contract"], SCHEMA["decision"]):
            own = c["slots"][3] if len(c["slots"]) > 3 else H_EMPTY
            return adm if c["slots"][:1] == [H_OWNER] or own == H_EMPTY else own
        if c["schema"] == SCHEMA["question"]:
            own = c["slots"][1] if len(c["slots"]) > 1 else H_EMPTY
            return adm if own == H_EMPTY else own
        return adm

    def can_evict(self, x: bytes) -> bool:
        c = self.cells[x]
        if c["schema"] == SCHEMA["scope"]:
            return False
        if c["schema"] in (SCHEMA["contract"], SCHEMA["decision"]):
            return c["slots"][:1] != [H_OWNER]
        return True

    def meets(self, y: bytes, ctx: bytes, x: bytes) -> bool:
        thr, keys = policy(self.atoms, self.pol_at(ctx, x))
        return len(self.sealers(y, ctx) & keys) >= thr

    def latch(self, y: bytes, x: bytes, kind: str) -> Optional[bool]:
        """Did the edge y -> x of `kind` latch (§4.1 latch 3)? True by a quorum of Pol(x) under a scope that governed;
        False when under none it meets Pol(x) and the author clause cannot apply."""
        c, t = self.cells.get(y), self.cells.get(x)
        if c is None or t is None or x not in hvec(self.atoms, c[kind]):
            return None
        if t["schema"] == SCHEMA["acceptance"] or c["schema"] == SCHEMA["scope"]:
            return None
        if any(self.meets(y, ctx, x) for ctx in self.chain):
            return None if c["schema"] == H_META_SCHEMA else True
        if kind != "invalidates" and self.can_evict(x) and self.local(x):
            ys = set().union(*(self.sealers(y, ctx) for ctx in self.chain))
            if ys & set().union(*(self.sealers(x, ctx) for ctx in self.chain)):
                return None
        return False

    def _memo(self, key: tuple, f) -> Optional[bool]:
        if key not in self.memo:
            self.memo[key] = None  # a cycle, which content addressing rules out, reads as undecided
            self.memo[key] = f()
        return self.memo[key]

    def eff(self, y: bytes) -> Optional[bool]:
        """Effective: every cell that invalidates y is a verdict that is not INVALID, is dead, or did not latch."""
        def f():
            if y not in self.cells:
                return False

            def covered(w):
                if self.non_inv(w):
                    return True
                return _or(x for x in (_not(self.latch(w, y, "invalidates")), self.dead(w)))
            return _and(covered(w) for w in self.into("invalidates", y))
        return self._memo(("eff", y), f)

    def dead(self, x: bytes) -> Optional[bool]:
        """Invalidated: an Effective local killer (not a verdict, or an INVALID one) invalidates x by a latched edge."""
        return self._memo(("dead", x), lambda: _or(
            _and((self.latch(y, x, "invalidates"), self.eff(y))) for y in self.into("invalidates", x)
            if self.local(y) and not self.non_inv(y)))

    def unsup(self, w: bytes) -> Optional[bool]:
        """Not Superseded: every cell that supersedes w did not latch, or is dead and not Superseded itself."""
        return self._memo(("unsup", w), lambda: _and(
            _or((_not(self.latch(u, w, "supersedes")), _and((self.dead(u), self.unsup(u)))))
            for u in self.into("supersedes", w)))

    def stand(self, c: bytes) -> Optional[bool]:
        """Active and not Stale: local, Effective, not Superseded, not Retired by a cell that counts, its supersedes
        edges latched, and what it relies on standing."""
        def f():
            if c not in self.cells or not self.local(c):
                return False
            return _and((self.eff(c), self.unsup(c),
                         _and(_or((_not(self.latch(w, c, "retires")), self.dead(w))) for w in self.into("retires", c)),
                         _and(self.latch(c, u, "supersedes") for u in hvec(self.atoms, self.cells[c]["supersedes"])),
                         _and(self.stand(r) for r in hvec(self.atoms, self.cells[c]["relies"]))))
        return self._memo(("stand", c), f)

    def down(self, b: bytes) -> Optional[bool]:
        """Not live because Invalidated, or because it relies on a cell that is down."""
        return self._memo(("down", b), lambda: _or((self.dead(b), _or(
            self.down(r) for r in hvec(self.atoms, self.cells[b]["relies"])) if b in self.cells else False)))


def _not(x: Optional[bool]) -> Optional[bool]:
    return None if x is None else not x


def _check(repo: str, term: Dict[str, object], pin: Optional[bytes]) -> Dict[str, object]:
    d, cone, ends, atoms, cells, seals, chain, sc = _read(repo, term, pin)
    dc = cells.get(d)
    if dc is None or dc["schema"] not in (SCHEMA["decision"], SCHEMA["contract"]):
        raise refuse("DECISION", "not a contract or decision cell of the store")
    if dc["slots"][1:2] != [H_EMPTY]:
        raise uncovered("COMPUTATION", "the decision requires a computation: replay decides it")

    # the cone: present, closed under relies, holding the decision and every endorsing verdict
    missing = [x for x in cone if x not in cells]
    if missing:
        raise refuse("CONE_MISSING", f"{missing[0].hex()} is not a cell of the store")
    present = sorted(x for x in cone if x in cells)
    if d not in cone:
        raise refuse("CONE_OPEN", "the cone lacks the decision")
    if any(w not in cone for w, _ in ends):
        raise refuse("CONE_OPEN", "the cone lacks an endorsing verdict")
    for x in present:
        if any(r not in cone for r in hvec(atoms, cells[x]["relies"])):
            raise refuse("CONE_OPEN", f"{x.hex()} relies on a cell outside the cone")
    # every cone cell stands: the edges into it and its own supersedes edges are read by the rules (Rules)
    rules = Rules(atoms, cells, seals, chain, term["scope"])
    standing = {x: rules.stand(x) for x in present}
    for x in present:
        if standing[x] is False:
            raise refuse("KILLED", f"{x.hex()} does not stand: an edge that counts invalidates, retires or supersedes it "
                         "or what it relies on, or one of its supersedes edges did not latch")
    for x in present:
        if standing[x] is None:
            raise uncovered("LATCH", f"whether {x.hex()} stands the store does not decide: an edge into or out of what "
                            "it rests on may have latched by the author clause, which reads its target's initial "
                            "endorsers")

    # the endorsements: ATTESTED verdicts on the decision, each sealed under a scope that governed, by a key of its
    # admission roster, by distinct keys of the evaluator policy
    own = dc["slots"][3:4]
    thr, keys = policy(atoms, own[0] if own and own[0] != H_EMPTY else sc["slots"][0])
    rosters = {x: policy(atoms, cells[x]["slots"][0])[1] for x in chain}
    # an INVALID verdict on the decision withdraws an endorsement under its verifier id by a key that seals it, and no
    # other (§4.2 Pass 3: a verifier id is free text), if it is live: the checker tells that where it stands, as a cone
    # cell does, and that it is not where it is down (Invalidated, or resting on an Invalidated cell)
    invalid = [b for b, c in cells.items() if c["schema"] == SCHEMA["verdict"] and c["payload"] == d
               and c["slots"][1:2] == [H_VERDICT_INVALID]]

    def sealed(b: bytes, k: bytes) -> bool:
        return any(y["target"] == b and y["key"] == k and y["ctx"] in chain and k in rosters[y["ctx"]]
                   and ed25519_verify(y["key"], y["signed"], y["signature"]) for y in seals.values())
    counted: Set[bytes] = set()
    for w, s in ends:
        v = cells.get(w, {"schema": None, "slots": []})
        if v["schema"] != SCHEMA["verdict"] or v["slots"][1:2] != [H_ATTESTED]:
            raise refuse("VERDICT", f"{w.hex()} is not an ATTESTED verdict")
        if v["payload"] != d or d not in hvec(atoms, v["attests"]):
            raise refuse("VERDICT", f"{w.hex()} does not judge and attest the decision")
        x = seals.get(s, {"target": None})
        if x["target"] != w:
            raise refuse("SEAL", f"{s.hex()} is not a seal of the store on {w.hex()}")
        if x["ctx"] not in chain:
            raise refuse("SEAL", f"{s.hex()} is sealed under another scope than those that governed")
        if x["key"] not in rosters.get(x["ctx"], set()):
            raise refuse("KEY", f"{x['key'].hex()} is not a key of the roster it sealed under")
        if not ed25519_verify(x["key"], x["signed"], x["signature"]):
            raise refuse("SEAL", f"{s.hex()} does not verify")
        if x["key"] not in keys:
            raise refuse("KEY", f"{x['key'].hex()} is not a key of the evaluator policy")
        for b in invalid:
            if cells[b]["slots"][2:3] == v["slots"][2:3] and sealed(b, x["key"]):
                if rules.stand(b) is True:
                    raise refuse("WITHDRAWN", f"{b.hex()}, an INVALID verdict under {w.hex()}'s verifier id sealed "
                                 f"by {x['key'].hex()}, withdraws that endorsement")
                if rules.down(b) is True:
                    continue  # not live: it withdraws nothing
                raise uncovered("INVALID_VERDICT", f"{b.hex()} would withdraw {x['key'].hex()}'s endorsement through "
                                f"{w.hex()}, and whether it is live the fragment does not decide")
        counted.add(x["key"])
    if len(counted) < thr:
        raise refuse("THRESHOLD", f"{len(counted)} distinct policy keys of {thr}")
    return {"decision": d.hex(), "tip": term["tip"], "scope_cell": chain[0].hex(), "threshold": thr,
            "endorsers": sorted(k.hex() for k in counted), "cone": len(cone), "store_cells": len(cells)}


UNFOUNDED = "minds.witness.unfounded@1"


def check_unfounded(repo: str, term: Dict[str, object], pin: Optional[bytes] = None) -> Dict[str, object]:
    """UNFOUNDED iff the term's cells form an unfounded set holding its decision (proofs/Vars1/WitnessGrounded.lean,
    `unfounded_of_each`), so the decision is not Grounded at the tip; otherwise REFUSED (a member satisfies Grounded's
    equation given the cells outside the set) or NOT_COVERED (the fragment does not decide a member)."""
    try:
        return {"result": "UNFOUNDED", **_check_unfounded(repo, term, pin)}
    except Refused as e:
        return {"result": e.result, "code": e.code, "detail": e.detail}


def _check_unfounded(repo: str, term: Dict[str, object], pin: Optional[bytes]) -> Dict[str, object]:
    """A term `{format, scope, tip, decision, unfounded: [cell ids]}`. For each member `v`, Grounded's equation must
    fail when only the cells outside the set are given (`GΦ` of the complement): `v` is down (Invalidated, or relying
    on a cell that is: the Lean checker's `down`), or does not stand by the rules below (retired, superseded, one of
    its edges unlatched: `stand` answers False, which no Lean rule concludes, so this reason is held by tests, not by
    `Witness.lean`), or relies on a member, or it is a contract or decision without a computation whose evaluator
    policy the keys counting through its witnesses outside the set cannot meet. Those keys are read from above: every key of the policy that seals,
    under a scope that governed and by a key of its roster, an ATTESTED verdict outside the set that judges and attests
    `v` with an empty witness slot and is not down, unless an INVALID verdict on `v` under that verdict's verifier id,
    sealed by the key, stands. A key the lens would not count only makes the check harder to pass, never wrong."""
    if not isinstance(term, dict) or term.get("format") != UNFOUNDED or not isinstance(term.get("scope"), str):
        raise refuse("FORMAT", f"not a {UNFOUNDED} term")
    d = _ids([term.get("decision")], "decision")[0]
    members = _ids(term.get("unfounded"), "unfounded")
    U = set(members)
    if d not in U:
        raise refuse("UNFOUNDED", "the set does not hold the decision")
    atoms, cells, seals, chain, sc = _fragment(repo, term, pin)
    absent = next((x for x in members if x not in cells), None)
    if absent is not None:
        raise refuse("UNFOUNDED", f"{absent.hex()} is not a cell of the store")
    rules = Rules(atoms, cells, seals, chain, term["scope"])
    reasons: Dict[str, str] = {}
    for v in sorted(U):
        c = cells[v]
        if rules.down(v) is True:
            reasons[v.hex()] = "down"
            continue
        if rules.stand(v) is False:
            reasons[v.hex()] = "not live"
            continue
        if any(r in U for r in hvec(atoms, c["relies"])):
            reasons[v.hex()] = "relies"
            continue
        if c["schema"] in (SCHEMA["contract"], SCHEMA["decision"]) and c["slots"][1:2] == [H_EMPTY]:
            own = c["slots"][3:4]
            thr, keys = policy(atoms, sc["slots"][0] if not own or own[0] == H_EMPTY else own[0])
            invalid = [b for b, x in cells.items() if x["schema"] == SCHEMA["verdict"] and x["payload"] == v
                       and x["slots"][1:2] == [H_VERDICT_INVALID]]
            upper: Set[bytes] = set()
            for w, x in cells.items():
                if (w in U or x["schema"] != SCHEMA["verdict"] or x["slots"][1:2] != [H_ATTESTED] or x["payload"] != v
                        or v not in hvec(atoms, x["attests"]) or x["slots"][:1] != [H_EMPTY] or rules.down(w) is True):
                    continue
                for k in set().union(*(rules.sealers(w, ctx) for ctx in chain)) & keys:
                    if not any(cells[b]["slots"][2:3] == x["slots"][2:3] and rules.stand(b) is True
                               and k in set().union(*(rules.sealers(b, ctx) for ctx in chain)) for b in invalid):
                        upper.add(k)
            if len(upper) < thr:
                reasons[v.hex()] = "quorum"
                continue
        if c["schema"] in (SCHEMA["contract"], SCHEMA["decision"], SCHEMA["question"], SCHEMA["scope"], H_META_SCHEMA) \
                and not (c["schema"] in (SCHEMA["contract"], SCHEMA["decision"]) and c["slots"][1:2] == [H_EMPTY]):
            raise uncovered("MEMBER", f"{v.hex()} is a scope, schema, question or computation's contract: its equation "
                            "is not read here")
        if rules.stand(v) is not True:
            raise uncovered("LIVENESS", f"whether {v.hex()} is live the fragment does not decide, and nothing else "
                            "shows its equation failing")
        raise refuse("FOUNDED", f"{v.hex()} satisfies Grounded's equation given the cells outside the set")
    return {"decision": d.hex(), "tip": term["tip"], "scope_cell": chain[0].hex(), "members": len(U),
            "reasons": reasons}


# --- the Lean checker's input --------------------------------------------------------------------------------------

LEAN_SCHEMA = {SCHEMA["scope"]: 0, SCHEMA["acceptance"]: 1, SCHEMA["contract"]: 2, SCHEMA["decision"]: 3,
               SCHEMA["question"]: 4, SCHEMA["verdict"]: 5, H_META_SCHEMA: 6, SCHEMA["checkpoint"]: 7,
               SCHEMA["cycle_witness"]: 8, SCHEMA["computation"]: 9, SCHEMA["axiom"]: 10}  # anything else: 11


def lean_line(repo: str, term: Dict[str, object], scope_cell: Optional[bytes] = None, prove: bool = False,
              ground: bool = False) -> str:
    """The store at the term's tip and the term as a derivation, in the line `vars1witness` reads
    (proofs/Vars1WitnessMain.lean). The decode is this file's: what `_read` refuses is refused here, and only seals that
    verify are written: every one on an INVALID verdict (the Lean checker reads from them which keys an INVALID verdict
    withdraws), on a cell with an invalidates, retires or supersedes edge, and on a cell such an edge retires or
    supersedes (it reads from them whether the edge latched). The rest is the Lean checker's to judge.

    The derivation: for each cone cell, after the cells it relies on, the lines the rules (Rules) derive for it (edges
    `latch`ed or `unlatched`, cells `dead` or `eff`, `unsup`), then its `stand` line; an `endorse` line per endorsement;
    `down` lines for the INVALID verdicts on the decision the rules prove not live; and a `settle` line whose premises
    are that the decision and each endorsing verdict stand, every endorsement, and those `down` lines. A conclusion the
    rules do not derive is left out, and the line that needs it fails in the Lean checker.

    With `prove`, the term's cone and endorsements are not read: the line carries every seal that verifies on a
    verdict whose payload is the decision, and no derivation, for `vars1witness --prove` to build one from the store
    alone (proofs/Vars1/WitnessComplete.lean `prove`). With `ground` as well, the line carries every seal that
    verifies on any verdict and the evaluator policy of every contract and decision, for `vars1witness --ground` to
    decide whether the decision is Grounded (proofs/Vars1/WitnessGrounded.lean `proveGround`, `accepts_iff_grounded`):
    Grounded reads the quorums of everything the decision rests on, and of their verdicts."""
    d, cone, ends, atoms, cells, seals, chain, sc = _read(repo, term, scope_cell)
    rules = Rules(atoms, cells, seals, chain, term["scope"])
    order = sorted(cells)
    ids = {cid: i for i, cid in enumerate(order)}
    num = lambda h: ids.setdefault(h, len(ids))  # noqa: E731  an id the store does not hold gets a number >= N
    keys: Dict[object, int] = {}
    key = lambda k: keys.setdefault(k, len(keys))  # noqa: E731
    pols: Dict[bytes, int] = {}
    pol = lambda h: pols.setdefault(h, len(pols))  # noqa: E731
    out: List[int] = [len(order)]
    for cid in order:
        c = cells[cid]
        slots = c["slots"]
        kind = LEAN_SCHEMA.get(c["schema"], 11)
        custom = slots[3] if kind in (2, 3) and len(slots) > 3 else slots[1] if kind == 4 and len(slots) > 1 else H_EMPTY
        local = cid in STANDARD or origin(atoms, c) == term["scope"]
        out += [kind, int(local), ids[c["payload"]] + 1 if c["payload"] in cells else 0,
                0 if custom == H_EMPTY else pol(custom) + 1, int(kind in (2, 3) and slots[:1] == [H_OWNER]),
                int(slots[1:2] == [H_ATTESTED]),
                int(slots[1:2] == [H_VERDICT_INVALID]), int(slots[:1] in ([], [H_EMPTY])),
                int(kind not in (2, 3) or slots[1:2] == [H_EMPTY]),
                num(slots[2]) if kind == 5 and len(slots) > 2 else 0]
        for edge in EDGES:
            items = hvec(atoms, c[edge])
            out += [len(items), *map(num, items)]
    pol0 = sc["slots"][0]
    used = [pol0] + ([cells[d]["slots"][3]] if d in cells and LEAN_SCHEMA.get(cells[d]["schema"]) in (2, 3)
                     and len(cells[d]["slots"]) > 3 and cells[d]["slots"][3] != H_EMPTY else [])
    out += [ids[chain[0]], pol(pol0), len(chain), *(n for x in chain for n in (ids[x], pol(cells[x]["slots"][0])))]
    used += [cells[x]["slots"][0] for x in chain]
    # the policies an edge reads: Pol(x) of every cell x an edge reaches is a scope's admission policy, written above,
    # or x's own, written here whatever its tier, which the Lean checker reads from its row
    sources = {cid for cid, c in cells.items() if any(hvec(atoms, c[k]) for k in KILLS)}
    targets = {t for cid in sources for k in KILLS for t in hvec(atoms, cells[cid][k]) if t in cells}

    def own(cid: bytes) -> bytes:
        slots, kind = cells[cid]["slots"], LEAN_SCHEMA.get(cells[cid]["schema"], 11)
        return slots[3] if kind in (2, 3) and len(slots) > 3 else slots[1] if kind == 4 and len(slots) > 1 else H_EMPTY
    used += [own(t) for t in sorted(targets) if own(t) != H_EMPTY]
    if ground:
        used += [own(x) for x in order if LEAN_SCHEMA.get(cells[x]["schema"]) in (2, 3) and own(x) != H_EMPTY]
    out += [len(set(used))]
    for h in dict.fromkeys(used):
        thr, ks = policy(atoms, h)
        out += [pol(h), thr, len(ks), *(key(k) for k in sorted(ks))]
    good = []
    named = [s for _, s in ends] if not prove else [sid for sid, x in seals.items() if x["target"] in cells
                                                    and cells[x["target"]]["schema"] == SCHEMA["verdict"]
                                                    and (ground or cells[x["target"]]["payload"] == d)]
    named += [sid for sid, x in seals.items() if x["target"] in cells
              and cells[x["target"]]["schema"] == SCHEMA["verdict"]
              and cells[x["target"]]["slots"][1:2] == [H_VERDICT_INVALID]]
    evicted = {t for cid in sources for k in ("retires", "supersedes") for t in hvec(atoms, cells[cid][k])}
    named += sorted(sid for sid, x in seals.items() if x["target"] in sources | evicted)
    for s in named:
        x = seals.get(s)
        if x is not None and ed25519_verify(x["key"], x["signed"], x["signature"]):
            good.append((num(x["target"]), num(x["ctx"]), key(x["key"])))
    good = list(dict.fromkeys(good))
    out += [len(good), *(n for g in good for n in g)]
    if prove:
        return " ".join(map(str, out + [0, num(d)]))

    lines: List[Tuple[int, tuple, list]] = []
    made: Set[tuple] = set()
    tag = {"stands": 0, "endorsed": 1, "settled": 2, "latch": 3, "unlatched": 4, "dead": 5, "eff": 6, "unsup": 7,
           "down": 8}

    def put(concl: tuple, prem: list) -> tuple:
        if concl not in made:
            made.add(concl)
            lines.append((tag[concl[0]], concl, [p for p in prem if p is not None]))
        return concl

    def edge(y: bytes, x: bytes, kind: str) -> Optional[tuple]:
        l = rules.latch(y, x, kind)
        return None if l is None else put(("latch" if l else "unlatched", y, x, kind), [])

    def eff(y: bytes) -> Optional[tuple]:
        if rules.eff(y) is not True:
            return None
        prem = [edge(w, y, "invalidates") if rules.latch(w, y, "invalidates") is False else dead(w)
                for w in rules.into("invalidates", y) if not rules.non_inv(w)]
        return put(("eff", y), prem)

    def dead(x: bytes) -> Optional[tuple]:
        if rules.dead(x) is not True:
            return None
        prem = [p for y in rules.into("invalidates", x) if rules.local(y) and not rules.non_inv(y)
                and rules.latch(y, x, "invalidates") is True and rules.eff(y) is True
                for p in (edge(y, x, "invalidates"), eff(y))]
        return put(("dead", x), prem)

    def unsup(w: bytes) -> Optional[tuple]:
        if rules.unsup(w) is not True:
            return None
        prem = [p for u in rules.into("supersedes", w) for p in
                ((edge(u, w, "supersedes"),) if rules.latch(u, w, "supersedes") is False else (dead(u), unsup(u)))]
        return put(("unsup", w), prem)

    def down(b: bytes) -> Optional[tuple]:
        if rules.down(b) is not True:
            return None
        prem = [dead(b)] if rules.dead(b) is True else [down(r) for r in hvec(atoms, cells[b]["relies"])
                                                       if rules.down(r) is True]
        return put(("down", b), prem)

    def stand(x: bytes) -> None:
        prem: list = []
        if x in cells:
            prem += [eff(x), unsup(x)]
            prem += [edge(w, x, "retires") if rules.latch(w, x, "retires") is False else dead(w)
                     for w in rules.into("retires", x)]
            prem += [edge(x, u, "supersedes") for u in hvec(atoms, cells[x]["supersedes"])]
            prem += [("stands", r) for r in hvec(atoms, cells[x]["relies"])]
        put(("stands", x), prem)

    seen: Set[bytes] = set()

    def visit(x: bytes) -> None:
        if x in seen:
            return
        seen.add(x)
        if x in cells:
            for r in hvec(atoms, cells[x]["relies"]):
                if r in cone:
                    visit(r)
        stand(x)
    for x in sorted(cone):
        visit(x)
    by = [(w, seals[s]["key"] if s in seals else ("absent", s)) for w, s in ends]
    for w, k in by:
        put(("endorsed", w, k), [])
    downs = [down(b) for b in sorted(cells) if cells[b]["schema"] == SCHEMA["verdict"] and cells[b]["payload"] == d
             and cells[b]["slots"][1:2] == [H_VERDICT_INVALID]]
    prem = [("stands", d)] + [p for w, k in by for p in (("stands", w), ("endorsed", w, k))] + downs
    put(("settled", d), prem)

    def enc(c: tuple) -> List[int]:
        if c[0] == "endorsed":
            return [1, num(c[1]), key(c[2])]
        if c[0] in ("latch", "unlatched"):
            return [tag[c[0]], num(c[1]), num(c[2]), KILLS.index(c[3])]
        return [tag[c[0]], num(c[1])]
    out += [len(lines), *(n for rule, c, ps in lines for n in (rule, *enc(c), len(ps), *(m for p in ps for m in enc(p)))),
            num(d)]
    return " ".join(map(str, out))


def main(argv: List[str]) -> int:
    unfounded = argv[:1] == ["--unfounded"]
    argv = argv[1:] if unfounded else argv
    lean = not unfounded and argv[:1] == ["--lean"]
    argv = argv[1:] if lean else argv
    prove = lean and argv[:1] == ["--prove"]
    argv = argv[1:] if prove else argv
    ground = lean and not prove and argv[:1] == ["--ground"]
    argv = argv[1:] if ground else argv
    if len(argv) not in (2, 4) or (len(argv) == 4 and (argv[2] != "--scope-cell"
                                                       or not re.fullmatch(r"[0-9a-f]{64}", argv[3]))):
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    try:
        with open(argv[1], "rb") as f:
            raw, pin = f.read(), bytes.fromhex(argv[3]) if len(argv) == 4 else None
        if lean:
            try:
                print(lean_line(argv[0], read_term(raw), pin, prove or ground, ground))
                return 0
            except Refused as e:
                out = {"result": e.result, "code": e.code, "detail": e.detail}
        elif unfounded:
            try:
                out = check_unfounded(argv[0], read_term(raw), pin)
            except Refused as e:
                out = {"result": e.result, "code": e.code, "detail": e.detail}
        else:
            out = check_text(argv[0], raw, pin)
    except Exception as e:  # a crash is not a verdict: Python would exit 1, which reads as REFUSED
        print(f"error: {type(e).__name__}: {e}", file=sys.stderr)
        return 3
    print(json.dumps(out, indent=1))
    return 0 if out["result"] in ("HELD", "UNFOUNDED") else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
