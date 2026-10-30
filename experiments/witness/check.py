#!/usr/bin/env python3
"""Check a witness that a decision is Settled at a tip of a VARS-1 chain, without the lens.

    python3 -I check.py REPO TERM.json [--scope-cell HEX]
    python3 -I check.py --lean REPO TERM.json [--scope-cell HEX] | proofs/.lake/build/bin/vars1witness

A witness (format `minds.witness.held@1`) is a proof term for one decision at one commit: the decision's cone (the
cells it and its counted verdicts rely on, closed under `relies`) and seals, by distinct keys of its evaluator
policy, on ATTESTED verdicts that judge it. This file reads the commit's tree with git, checks the term against the
store's bytes and answers HELD, REFUSED or NOT_COVERED. It shares no code with vars1.py or verify/minds_verify.py:
the constants are VARS-1-SPEC.md's tables, the parsers and the Ed25519 check are its own, standard library only.

What HELD rests on (README.md):
- the positive part is checked from bytes: every object hashes to its name, the seals verify under their keys, the
  keys are in the evaluator policy that the decision's id fixes, and the threshold is met;
- the negative part (no cell invalidates, retires or supersedes a cone cell; no INVALID verdict judges the
  decision; one scope; no foreign cells) is read over the store at the tip, so it holds only if that store is the
  admitted chain, complete: the reader's pin, which this file does not check (it runs no gate).

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
H_META_SCHEMA = bytes.fromhex("7f0f250c08d367c8f2ba2c3b700f1a9bacbb44c240dade81c5c39c9ea7f9f15e")
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
    """The term's parts and the store at its tip, decoded, within the fragment: one scope (the pinned one, which the
    term names), the v1 rules, no foreign cell. Both checkers read the store through here."""
    if not isinstance(term, dict) or term.get("format") != FORMAT or not isinstance(term.get("scope"), str):
        raise refuse("FORMAT", f"not a {FORMAT} term")
    d = _ids([term.get("decision")], "decision")[0]
    cone = set(_ids(term.get("cone"), "cone"))
    ends = term.get("endorsements")
    if not isinstance(ends, list) or not all(isinstance(e, dict) and set(e) == {"verdict", "seal"} for e in ends):
        raise refuse("FORMAT", "endorsements are not a list of {verdict, seal}")
    ends = [(_ids([e["verdict"]], "verdict")[0], _ids([e["seal"]], "seal")[0]) for e in ends]
    store = read_store(repo, term.get("tip"))
    atoms = store["atoms"]
    cells = {cid: cell(raw) for cid, raw in store["cells"].items()}
    seals = {sid: seal(raw) for sid, raw in store["seals"].items()}

    # the fragment: one scope, the v1 rules, nothing foreign
    scopes = [cid for cid, c in cells.items() if c["schema"] == SCHEMA["scope"]]
    if len(scopes) != 1:
        raise uncovered("SCOPES", f"{len(scopes)} scope cells: a rotation or a foreign scope")
    sc = cells[scopes[0]]
    if len(sc["slots"]) != 3:
        raise refuse("STORE", "the scope cell is malformed")
    if pin is not None and scopes[0] != pin:
        raise refuse("SCOPE", "the scope cell is not the one the reader pinned")
    if origin(atoms, sc) != term["scope"]:
        raise refuse("SCOPE", "the store's scope is not the term's")
    if sc["slots"][2] != H_LENS_KERNEL:
        raise uncovered("RULES", "the scope names rules other than v1")
    if any(cid not in STANDARD and origin(atoms, c) != term["scope"] for cid, c in cells.items()):
        raise uncovered("FOREIGN", "the store holds foreign cells")
    return d, cone, ends, atoms, cells, seals, scopes, sc


def _check(repo: str, term: Dict[str, object], pin: Optional[bytes]) -> Dict[str, object]:
    d, cone, ends, atoms, cells, seals, scopes, sc = _read(repo, term, pin)
    dc = cells.get(d)
    if dc is None or dc["schema"] not in (SCHEMA["decision"], SCHEMA["contract"]):
        raise refuse("DECISION", "not a contract or decision cell of the store")
    if dc["slots"][1:2] != [H_EMPTY]:
        raise uncovered("COMPUTATION", "the decision requires a computation: replay decides it")
    if any(c["schema"] == SCHEMA["verdict"] and c["payload"] == d and c["slots"][1:2] == [H_VERDICT_INVALID]
           for c in cells.values()):
        raise uncovered("INVALID_VERDICT", "an INVALID verdict judges the decision")

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
    for x in present:
        if hvec(atoms, cells[x]["supersedes"]):
            raise uncovered("KILL_EDGE", f"{x.hex()} supersedes a cell")
    for cid, c in cells.items():
        for kind in ("invalidates", "retires", "supersedes"):
            hit = cone.intersection(hvec(atoms, c[kind]))
            if hit:
                raise uncovered("KILL_EDGE", f"{cid.hex()} {kind} {min(hit).hex()} of the cone")

    # the endorsements: ATTESTED verdicts on the decision, sealed under the scope by distinct policy keys
    own = dc["slots"][3:4]
    thr, keys = policy(atoms, own[0] if own and own[0] != H_EMPTY else sc["slots"][0])
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
        if x["ctx"] != scopes[0]:
            raise refuse("SEAL", f"{s.hex()} is sealed under another scope")
        if not ed25519_verify(x["key"], x["signed"], x["signature"]):
            raise refuse("SEAL", f"{s.hex()} does not verify")
        if x["key"] not in keys:
            raise refuse("KEY", f"{x['key'].hex()} is not a key of the evaluator policy")
        counted.add(x["key"])
    if len(counted) < thr:
        raise refuse("THRESHOLD", f"{len(counted)} distinct policy keys of {thr}")
    return {"decision": d.hex(), "tip": term["tip"], "scope_cell": scopes[0].hex(), "threshold": thr,
            "endorsers": sorted(k.hex() for k in counted), "cone": len(cone), "store_cells": len(cells)}


# --- the Lean checker's input --------------------------------------------------------------------------------------

LEAN_SCHEMA = {SCHEMA["scope"]: 0, SCHEMA["acceptance"]: 1, SCHEMA["contract"]: 2, SCHEMA["decision"]: 3,
               SCHEMA["question"]: 4, SCHEMA["verdict"]: 5, H_META_SCHEMA: 6, SCHEMA["checkpoint"]: 7,
               SCHEMA["cycle_witness"]: 8, SCHEMA["computation"]: 9, SCHEMA["axiom"]: 10}  # anything else: 11


def lean_line(repo: str, term: Dict[str, object], scope_cell: Optional[bytes] = None) -> str:
    """The store at the term's tip and the term as a derivation, in the line `vars1witness` reads
    (proofs/Vars1WitnessMain.lean). The decode is this file's: what `_read` refuses is refused here, and only seals that
    verify are written. The rest is the Lean checker's to judge: the cone, the kill edges, the verdicts, the keys.

    The derivation: a `stand` line per cone cell, each after the cells it relies on, whose premises are that each of
    them stands; an `endorse` line per endorsement; and a `settle` line for the decision whose premises are that it
    and each endorsing verdict stand and every endorsement."""
    d, cone, ends, atoms, cells, seals, scopes, sc = _read(repo, term, scope_cell)
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
                0 if custom == H_EMPTY else pol(custom) + 1, int(slots[1:2] == [H_ATTESTED]),
                int(slots[1:2] == [H_VERDICT_INVALID]), int(slots[:1] in ([], [H_EMPTY])),
                int(kind not in (2, 3) or slots[1:2] == [H_EMPTY])]
        for edge in EDGES:
            items = hvec(atoms, c[edge])
            out += [len(items), *map(num, items)]
    pol0 = sc["slots"][0]
    used = [pol0] + ([cells[d]["slots"][3]] if d in cells and LEAN_SCHEMA.get(cells[d]["schema"]) in (2, 3)
                     and len(cells[d]["slots"]) > 3 and cells[d]["slots"][3] != H_EMPTY else [])
    out += [ids[scopes[0]], pol(pol0), len(set(used))]
    for h in dict.fromkeys(used):
        thr, ks = policy(atoms, h)
        out += [pol(h), thr, len(ks), *(key(k) for k in sorted(ks))]
    good = []
    for w, s in ends:
        x = seals.get(s)
        if x is not None and ed25519_verify(x["key"], x["signed"], x["signature"]):
            good.append((num(x["target"]), num(x["ctx"]), key(x["key"])))
    good = list(dict.fromkeys(good))
    out += [len(good), *(n for g in good for n in g)]

    stands, seen = [], set()

    def visit(x: bytes) -> None:
        if x in seen:
            return
        seen.add(x)
        if x in cells:
            for r in hvec(atoms, cells[x]["relies"]):
                if r in cone:
                    visit(r)
        stands.append(x)
    for x in sorted(cone):
        visit(x)
    by = [(w, seals[s]["key"] if s in seals else ("absent", s)) for w, s in ends]
    lines = [[0, 0, num(x), *([len(hvec(atoms, cells[x]["relies"]))] + [n for r in hvec(atoms, cells[x]["relies"])
                                                                         for n in (0, num(r))]
                              if x in cells else [0])] for x in stands]
    lines += [[1, 1, num(w), key(k), 0] for w, k in by]
    prem = [[0, num(d)]] + [p for w, k in by for p in ([0, num(w)], [1, num(w), key(k)])]
    lines.append([2, 2, num(d), len(prem), *(n for p in prem for n in p)])
    out += [len(lines), *(n for ln in lines for n in ln), num(d)]
    return " ".join(map(str, out))


def main(argv: List[str]) -> int:
    lean = argv[:1] == ["--lean"]
    argv = argv[1:] if lean else argv
    if len(argv) not in (2, 4) or (len(argv) == 4 and (argv[2] != "--scope-cell"
                                                       or not re.fullmatch(r"[0-9a-f]{64}", argv[3]))):
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    try:
        with open(argv[1], "rb") as f:
            raw, pin = f.read(), bytes.fromhex(argv[3]) if len(argv) == 4 else None
        if lean:
            try:
                print(lean_line(argv[0], read_term(raw), pin))
                return 0
            except Refused as e:
                out = {"result": e.result, "code": e.code, "detail": e.detail}
        else:
            out = check_text(argv[0], raw, pin)
    except Exception as e:  # a crash is not a verdict: Python would exit 1, which reads as REFUSED
        print(f"error: {type(e).__name__}: {e}", file=sys.stderr)
        return 3
    print(json.dumps(out, indent=1))
    return 0 if out["result"] == "HELD" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
