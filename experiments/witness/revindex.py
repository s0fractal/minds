"""An address for negative facts: a committed reverse index (experiments only; no format of spec §4.4 changes).

A cell names what it points at and never what will point at it, so "nothing else at the tip touches this frame" has no
address, and a reader who checks it reads the store (proofs/Vars1/Reader.lean `reader_reads_commit`). frame.py's
`message` therefore carries that part as a vouch. This module gives it an address.

At a tip every id that a cell or a seal points at, and every cell, gets a leaf: the sorted ids of the cells that
attest it, of the verdicts on it, of the verdicts that name it as their checkpoint or cycle witness, of the cells with
an invalidates, retires or supersedes edge into it, and of the seals on it. The leaves, sorted by id, are hashed into
one Merkle tree (RFC 9162 §2.1: 0x00 before a leaf, 0x01 before a node). A reader who holds the root reads a
decision's frame from its frame's leaves, their paths and the frame's own cells: O(|frame| log N) bytes, not the store
(`reader_frame`, which the tests hold equal to frame.py's `frame` on every decision of the live chain).

What it does not do is prove the root. That each leaf is the store's and that no leaf is missing is the claim of
whoever signs the root, as the vouch was. Two things change. One root serves every decision and every reader at the
tip: one signature, not one vouch each, and two readers holding one root read one answer. And a wrong root costs one
object to refute: the cell or seal a leaf leaves out, or an id it lists that does not point at its key, with that
leaf's path (`refute`); whoever holds the store checks it by reading that object, not the store (`judge`).

Like frame.py it reads vars1 through the `V` it is given and imports nothing of minds.
"""
import hashlib
import struct
from typing import Dict, List, Optional, Tuple

FORMAT = "minds.revindex.draft@0"
# what points at a key, one sorted list of ids per kind, in this order in the leaf
KINDS = ("attests", "payload", "named", "invalidates", "retires", "supersedes", "seals")
EVICT = ("invalidates", "retires", "supersedes")


class Incomplete(Exception):
    """The message lacks a leaf or a cell the frame reads: the reader cannot decide, which is no answer."""


def _sha(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()


def reverse(T) -> Dict[bytes, Dict[str, List[bytes]]]:
    """The store's reverse facts at the tip: for every cell and every id something points at, what points at it."""
    V = T.V
    out: Dict[bytes, Dict[str, List[bytes]]] = {}
    at = lambda key: out.setdefault(key, {k: [] for k in KINDS})  # noqa: E731
    for cid in T.cells:
        at(cid)
    for cid, c in T.cells.items():
        for t in T.hv(c.h_attests):
            at(t)["attests"].append(cid)
        if c.h_schema == V.H_SCHEMA["verdict"]:
            at(c.h_payload)["payload"].append(cid)
            if c.slots[0] != V.H_EMPTY:
                at(c.slots[0])["named"].append(cid)
        for kind in EVICT:
            for t in T.hv(getattr(c, "h_" + kind)):
                at(t)[kind].append(cid)
    for sid, s in T.seals.items():
        at(s.h_target)["seals"].append(sid)
    for entry in out.values():
        for k in KINDS:
            entry[k] = sorted(set(entry[k]))
    return out


def leaf_bytes(key: bytes, entry: Dict[str, List[bytes]]) -> bytes:
    out = bytearray(key)
    for k in KINDS:
        out += struct.pack(">H", len(entry[k])) + b"".join(entry[k])
    return bytes(out)


def leaf_hash(key: bytes, entry: Dict[str, List[bytes]]) -> bytes:
    return _sha(b"\x00" + leaf_bytes(key, entry))


def _split(n: int) -> int:
    k = 1
    while k * 2 < n:
        k *= 2
    return k


class Tree:
    """RFC 9162 Merkle tree hash over leaf hashes, with audit paths."""

    def __init__(self, hashes: List[bytes]) -> None:
        self.hashes = hashes
        self.memo: Dict[Tuple[int, int], bytes] = {}

    def mth(self, lo: int, hi: int) -> bytes:
        if (lo, hi) not in self.memo:
            if hi - lo == 1:
                self.memo[(lo, hi)] = self.hashes[lo]
            else:
                k = lo + _split(hi - lo)
                self.memo[(lo, hi)] = _sha(b"\x01" + self.mth(lo, k) + self.mth(k, hi))
        return self.memo[(lo, hi)]

    @property
    def root(self) -> bytes:
        return self.mth(0, len(self.hashes))

    def path(self, m: int) -> List[bytes]:
        lo, hi, out = 0, len(self.hashes), []
        while hi - lo > 1:
            k = lo + _split(hi - lo)
            if m < k:
                out.append(self.mth(k, hi))
                hi = k
            else:
                out.append(self.mth(lo, k))
                lo = k
        return out[::-1]


def verify_path(root: bytes, size: int, index: int, leaf: bytes, path: List[bytes]) -> bool:
    """RFC 9162 §2.1.3.2: does `leaf` sit at `index` of a tree of `size` leaves whose root is `root`?"""
    if not 0 <= index < size:
        return False
    fn, sn, r = index, size - 1, leaf
    for p in path:
        if sn == 0:
            return False
        if fn & 1 or fn == sn:
            r = _sha(b"\x01" + p + r)
            while not fn & 1 and fn != 0:
                fn >>= 1
                sn >>= 1
        else:
            r = _sha(b"\x01" + r + p)
        fn >>= 1
        sn >>= 1
    return sn == 0 and r == root


class Index:
    """The committed reverse index of a tip, as whoever signs its root computes it."""

    def __init__(self, T, entries: Optional[Dict[bytes, Dict[str, List[bytes]]]] = None) -> None:
        self.tip = T.tip
        self.entries = reverse(T) if entries is None else entries
        self.keys = sorted(self.entries)
        self.at = {k: i for i, k in enumerate(self.keys)}
        self.tree = Tree([leaf_hash(k, self.entries[k]) for k in self.keys])
        self.root = self.tree.root

    def leaf(self, key: bytes) -> Dict[str, object]:
        i = self.at[key]
        return {"key": key.hex(), "index": i, "path": [p.hex() for p in self.tree.path(i)],
                **{k: [x.hex() for x in self.entries[key][k]] for k in KINDS}}


def leaf_keys(fr: Dict[str, object]) -> List[bytes]:
    """The keys whose leaves a reader of this frame needs: what judges each evaluated cell, what names each checkpoint,
    what points an eviction edge into each cell of `guard`, and the seals on each watched cell."""
    return sorted(set(fr["evaluated"]) | set(fr["named"]) | set(fr["guard"]) | set(fr["watch"]))


def closed_part(T, ix: Index, fr: Dict[str, object]) -> Dict[str, object]:
    """The closed-world part of a message for frame `fr`: the root, the leaves its frame reads with their paths, the
    cells of `guard` (whose own fields the reading follows: relies, supersedes, schema, a verdict's checkpoint) with the
    atoms of those fields, and every seal on a watched cell, as bytes."""
    leaves = [ix.leaf(k) for k in leaf_keys(fr)]
    watched = set(fr["watch"])
    on_watch = {bytes.fromhex(x) for lf in leaves if bytes.fromhex(lf["key"]) in watched for x in lf["seals"]}
    need = set()
    for x in fr["guard"]:
        need |= {T.cells[x].h_relies, T.cells[x].h_supersedes}
    return {"format": FORMAT, "tip": ix.tip, "root": ix.root.hex(), "size": len(ix.keys), "leaves": leaves,
            "cells": sorted(T.cells[x].encode().hex() for x in fr["guard"]),
            "seals": sorted(T.seals[x].encode().hex() for x in on_watch),
            "atoms": sorted(T.atoms[h].hex() for h in need if h != T.V.H_EMPTY and h in T.atoms)}


def reader_frame(V, part: Dict[str, object], d: bytes, grounded: bool = False) -> Dict[str, object]:
    """frame.py's `frame`, read from a closed-world part alone: every leaf's path is checked against the part's root,
    and every lookup of what points at a cell goes to its leaf. A leaf or cell the reading needs and the part lacks is
    `Incomplete`; a path that does not lead to the root is `ValueError`."""
    root, size = bytes.fromhex(part["root"]), part["size"]
    leaves: Dict[bytes, Dict[str, List[bytes]]] = {}
    for lf in part["leaves"]:
        key = bytes.fromhex(lf["key"])
        entry = {k: [bytes.fromhex(x) for x in lf[k]] for k in KINDS}
        if not verify_path(root, size, lf["index"], leaf_hash(key, entry), [bytes.fromhex(p) for p in lf["path"]]):
            raise ValueError(f"the leaf of {key.hex()[:12]} does not lead to the root")
        leaves[key] = entry
    cells = {}
    for h in part["cells"]:
        c = V.Cell.decode(bytes.fromhex(h))
        cells[c.id] = c
    atoms = {_sha(bytes.fromhex(a)): bytes.fromhex(a) for a in part["atoms"]}
    seals = {_sha(bytes.fromhex(s)) for s in part["seals"]}

    def leaf(v: bytes) -> Dict[str, List[bytes]]:
        if v not in leaves:
            raise Incomplete(f"no leaf for {v.hex()[:12]}")
        return leaves[v]

    def cell(v: bytes):
        if v not in cells:
            raise Incomplete(f"no cell {v.hex()[:12]}")
        return cells[v]

    def hv(h: bytes) -> List[bytes]:
        if h == V.H_EMPTY:
            return []
        if h not in atoms:
            raise Incomplete(f"no atom {h.hex()[:12]}")
        return V.parse_hvec(atoms[h], require_sorted=True)

    def judges_of(v: bytes):
        direct = set(leaf(v)["attests"]) | set(leaf(v)["payload"])
        named = set()
        for w in direct:
            c = cell(w)
            if c.h_schema == V.H_SCHEMA["verdict"] and c.slots[0] != V.H_EMPTY:
                named.add(c.slots[0])
        return direct | {b for n in named for b in leaf(n)["named"]}, {n for n in named if n in cells}

    def down(roots) -> set:
        out, todo = set(roots), list(roots)
        while todo:
            for r in hv(cell(todo.pop()).h_relies):
                if r not in out:
                    out.add(r)
                    todo.append(r)
        return out

    def is_evaluated(c) -> bool:
        return c.h_schema in (V.H_SCHEMA["contract"], V.H_SCHEMA["decision"], V.H_SCHEMA["question"])

    def own(c) -> bytes:
        return c.slots[1] if c.h_schema == V.H_SCHEMA["question"] else c.slots[3]

    into = lambda x: {y for k in EVICT for y in leaf(x)[k]}  # noqa: E731
    judges, named = judges_of(d)
    ev = {d}
    read = down({d} | judges | named)
    while grounded:
        more = {v for v in read if is_evaluated(cell(v))} - ev
        if not more:
            break
        ev |= more
        for v in more:
            j, n = judges_of(v)
            judges |= j
            named |= n
        read = down(read | judges | named)
    guard, todo = set(read), list(read)
    while todo:
        x = todo.pop()
        for y in into(x) | set(hv(cell(x).h_supersedes)):
            if y not in guard:
                guard.add(y)
                todo.append(y)
    sources = {w for x in guard for w in into(x)}
    latching = {x for x in guard if cell(x).h_schema in (V.H_META_SCHEMA, V.H_SCHEMA["acceptance"], V.H_SCHEMA["scope"])}
    watch = judges | sources | latching
    on_watch = {s for w in watch for s in leaf(w)["seals"]}
    if not on_watch <= seals:
        raise Incomplete("a seal on a watched cell is not in the part")
    return {"decision": d, "grounded": grounded, "read": sorted(read), "guard": sorted(guard),
            "judges": sorted(judges), "named": sorted(named), "sources": sorted(sources), "evaluated": sorted(ev),
            "watch": sorted(watch), "fallback": sorted(v for v in ev if own(cell(v)) == V.H_EMPTY),
            "seals": sorted(on_watch)}


def refute(T, lf: Dict[str, object]) -> Optional[Dict[str, object]]:
    """Against the store at the tip, the first fact a claimed leaf gets wrong, as a fraud proof: an object the leaf
    leaves out (`omits`), or an id it lists that does not point at its key (`lists`). None when the leaf is the store's."""
    key = bytes.fromhex(lf["key"])
    true = reverse(T).get(key, {k: [] for k in KINDS})
    for k in KINDS:
        claimed = {bytes.fromhex(x) for x in lf[k]}
        for x in sorted(set(true[k]) - claimed):
            obj = T.seals[x] if k == "seals" else T.cells[x]
            return {"leaf": lf, "kind": k, "omits": obj.encode().hex()}
        for x in sorted(claimed - set(true[k])):
            return {"leaf": lf, "kind": k, "lists": x.hex()}
    return None


def _points(T, obj_id: bytes, kind: str, key: bytes) -> bool:
    """Does the stored object `obj_id` point at `key` in the way `kind` names?"""
    V = T.V
    if kind == "seals":
        return obj_id in T.seals and T.seals[obj_id].h_target == key
    c = T.cells.get(obj_id)
    if c is None:
        return False
    if kind == "attests":
        return key in T.hv(c.h_attests)
    if kind == "payload":
        return c.h_schema == V.H_SCHEMA["verdict"] and c.h_payload == key
    if kind == "named":
        return c.h_schema == V.H_SCHEMA["verdict"] and c.slots[0] == key
    return key in T.hv(getattr(c, "h_" + kind))


def judge(T, root: bytes, size: int, fraud: Dict[str, object]) -> bool:
    """Is `fraud` a proof that the tree under `root` is not the store's at the tip? Its leaf must lead to the root, and
    the one object it names must contradict that leaf; the judge reads that object, never the whole store."""
    lf, k = fraud["leaf"], fraud["kind"]
    key = bytes.fromhex(lf["key"])
    entry = {kk: [bytes.fromhex(x) for x in lf[kk]] for kk in KINDS}
    if not verify_path(root, size, lf["index"], leaf_hash(key, entry), [bytes.fromhex(p) for p in lf["path"]]):
        return False
    if "omits" in fraud:
        raw = bytes.fromhex(fraud["omits"])
        oid = _sha(raw)
        return oid not in entry[k] and _points(T, oid, k, key)
    x = bytes.fromhex(fraud["lists"])
    return x in entry[k] and not _points(T, x, k, key)


def measure(V, repo, scope: str, tips: List[str], prove, F) -> List[Dict[str, object]]:
    """For each tip: the store's size, and over every Settled decision with a covering projection the median bytes
    (compact JSON, objects in hex) of the message whose closed world is this module's part, signed as a projection is
    (`signed_by`: the covering projection's cell and seals, standing in for a root carried the same way), against the
    attestation bundle a client receives today. `F` is frame.py."""
    out = []
    for tip in tips:
        T = F.Tip(V, repo, scope, tip)
        ix = Index(T)
        rev, bundle, closed = [], [], []
        for d, c in sorted(T.cells.items()):
            if c.h_schema != V.H_SCHEMA["decision"] or not T.lens["settled"].get(d):
                continue
            pid = F.covering_at(T, d)
            if pid is None:
                continue
            fr = F.frame(T, d)
            part = closed_part(T, ix, fr)
            carrier = {"kind": "projection", **F.projection_at(T, pid, with_data=False)}
            rev.append(F._hex_json(F.message(T, prove(repo, scope, d, tip), {"kind": "revindex", "signed_by": carrier,
                                                                            **part})))
            closed.append(F._hex_json(part))
            bundle.append(F._hex_json(F.bundle_at(T, d, pid)))
        med = lambda xs: sorted(xs)[len(xs) // 2] if xs else None  # noqa: E731
        out.append({"tip": tip, "cells": len(T.cells), "leaves": len(ix.keys), "decisions": len(rev),
                    "closed_median": med(closed), "message_median": med(rev), "bundle_median": med(bundle),
                    "message_max": max(rev, default=None), "bundle_max": max(bundle, default=None)})
    return out


if __name__ == "__main__":
    # python experiments/witness/revindex.py [REPO [SCOPE [TIP]]]: the table of README.md at five tips, as JSON
    import json
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import vars1  # noqa: E402
    import frame as _frame  # noqa: E402
    import prove as _prove  # noqa: E402
    _a = sys.argv[1:]
    _repo = vars1.GitVarsRepo(Path(_a[0] if _a else Path(__file__).resolve().parents[2]))
    _scope = _a[1] if len(_a) > 1 else "minds"
    _chain = _repo.commit_chain(_a[2] if len(_a) > 2 else _repo.ref_commit(_scope))
    _tips = [_chain[i] for i in sorted({len(_chain) // 8, len(_chain) // 4, len(_chain) // 2, 3 * len(_chain) // 4,
                                         len(_chain) - 1})]
    print(json.dumps(measure(vars1, _repo, _scope, _tips, _prove.prove, _frame), indent=1, sort_keys=True))
