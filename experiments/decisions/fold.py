#!/usr/bin/env python3
"""What each of several candidate readings of one event would do to the graph (`fold-candidates`).

    python3 experiments/decisions/fold.py REPO SCOPE CANDIDATES.json [--tip COMMIT] [--no-gate]

A model or a person reading an unstructured event (a message, a pull request, a bug report) can offer several readings
of what it is in the graph: a notice that invalidates a check, an INVALID verdict on a decision, a seal, nothing at
all. This file asks the graph, not a probability, what each would change: for a batch of candidates
(`minds.decisions.candidates@1`) it reads, without moving the ref,

- `admissible`: whether the candidate passes the gate (its seals supposed, `GitVarsRepo.what_if(assume=True)`), and if
  not, why;
- `flipped_settled`, `flipped_grounded`: the contracts, decisions and questions whose Settled or Grounded it changes;
- `classes`: the candidates grouped by the vector of (Settled, Grounded) they leave on every such cell, so two readings
  that act alike are one question, not two;
- `discriminating`: for two classes that act differently, the cells on which they part, so what is asked of a person or
  a verifier is about those cells, not the raw text.

A candidate is read in two steps. First in memory, from below (`experiments/witness/delta.py`, `delta.dirty`, held to
`touches` on every pair of tips by test 25 of `test_witness.py`): the cells whose Grounded frame its objects touch. A
frame nothing touches keeps its status (tests 17–19), so a candidate that dirties no cell changes nothing, and needs
the gate only to say whether it is admissible. Then, for the rest, the gate (`what_if` with `statuses`) gives the
exact changes. With `--no-gate` the first step alone answers, and a candidate that dirties a cell is `unread`.

Candidates: `{"format": "minds.decisions.candidates@1", "candidates": [{"id": str, "keys": [hex], "acts": [...]}]}`,
each act one of
- `{"act": "verdict", "on": CELL, "code": "ATTESTED" | "INVALID", "verifier": str, "relies": [CELL]}`: a new verdict;
- `{"act": "notice", "edge": "invalidates" | "retires", "target": CELL}`: a new axiom with that edge;
- `{"act": "seal", "target": CELL}`: a seal on a cell of the chain;
- `{"act": "none"}`: nothing (a comment that changes no edge).
Every new cell and every seal is sealed by each key of `keys`, supposed (a zero signature). It reads vars1.py and the
witness spike's `delta.py` and `frame.py`, the standard library, and no network.
"""
import json
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "experiments" / "witness"))
import vars1 as V  # noqa: E402
import frame as FR  # noqa: E402
import delta as DX  # noqa: E402

FORMAT = "minds.decisions.candidates@1"
CODES = {"ATTESTED": V.H_ATTESTED, "INVALID": V.H_VERDICT_INVALID}
EDGES = {"invalidates": "h_invalidates", "retires": "h_retires"}


class Bad(Exception):
    """A candidate file that does not read one way."""


def _put(atoms: Dict[bytes, bytes], raw: bytes) -> bytes:
    h = V.sha256(raw)
    atoms[h] = raw
    return h


def _cell(T, hexid: object, what: str) -> bytes:
    if not isinstance(hexid, str) or len(hexid) != 64:
        raise Bad(f"{what} is not a 64-digit cell id")
    cid = bytes.fromhex(hexid)
    if cid not in T.cells:
        raise Bad(f"{what} {hexid[:12]} is not a cell of the tip")
    return cid


def build(T, scope: str, cand: Dict[str, object]) -> Tuple[Dict[bytes, bytes], List["V.Cell"], List["V.Seal"]]:
    """The candidate's objects as the gate reads them: its new cells and its seals, each by each of its keys, with a
    zero signature."""
    keys = cand.get("keys")
    if not isinstance(keys, list) or not keys or not all(isinstance(k, str) and len(k) == 64 for k in keys):
        raise Bad(f"candidate {cand.get('id')!r}: `keys` is not a list of 64-digit keys")
    keys = [bytes.fromhex(k) for k in keys]
    atoms: Dict[bytes, bytes] = {}
    cells: List[V.Cell] = []
    targets: List[bytes] = []
    for n, act in enumerate(cand.get("acts") or []):
        kind = act.get("act") if isinstance(act, dict) else None
        name = lambda what: _put(atoms, V.atom_utf8(f"{scope}/decisions/{cand['id']}/{n}/{what}"))  # noqa: E731
        if kind == "none":
            continue
        if kind == "verdict":
            on = _cell(T, act.get("on"), "the verdict's cell")
            if act.get("code") not in CODES or not isinstance(act.get("verifier"), str):
                raise Bad(f"candidate {cand['id']!r}: a verdict needs a code of {sorted(CODES)} and a verifier id")
            atoms[CODES[act["code"]]] = V.atom_utf8(act["code"])
            relies = sorted(_cell(T, r, "a relied cell") for r in act.get("relies") or [])
            extra = {"h_relies": _put(atoms, V.atom_hvec(relies))} if relies else {}
            c = V.Cell(h_schema=V.H_SCHEMA["verdict"], h_slot_name=name("verdict"), h_payload=on,
                       h_attests=_put(atoms, V.atom_hvec([on])),
                       slots=(V.H_EMPTY, CODES[act["code"]], _put(atoms, V.atom_utf8(act["verifier"]))), **extra)
        elif kind == "notice":
            if act.get("edge") not in EDGES:
                raise Bad(f"candidate {cand['id']!r}: a notice's edge is one of {sorted(EDGES)}")
            target = _cell(T, act.get("target"), "the notice's target")
            extra = {EDGES[act["edge"]]: _put(atoms, V.atom_hvec([target]))}
            if act["edge"] == "retires":
                extra["h_loss"] = _put(atoms, V.atom_utf8("retired"))
            c = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=name("notice"),
                       h_payload=_put(atoms, V.atom_utf8(f"notice {cand['id']} {n}")), **extra)
        elif kind == "seal":
            targets.append(_cell(T, act.get("target"), "the sealed cell"))
            continue
        else:
            raise Bad(f"candidate {cand.get('id')!r}: unknown act {kind!r}")
        cells.append(c)
        targets.append(c.id)
    seals = [V.Seal(h_target=t, h_scope_ctx=T.governing, actor_pubkey=k, signature=V.ZERO_SIGNATURE)
             for t in targets for k in keys]
    return atoms, cells, seals


def read_candidates(raw: bytes) -> List[Dict[str, object]]:
    def one_reading(pairs):
        keys = [k for k, _ in pairs]
        if len(keys) != len(set(keys)):
            raise Bad("an object names a key twice")
        return dict(pairs)
    try:
        doc = json.loads(raw.decode("utf-8"), object_pairs_hook=one_reading)
    except (UnicodeDecodeError, json.JSONDecodeError) as e:
        raise Bad(f"not UTF-8 JSON: {e}") from None
    if not isinstance(doc, dict) or doc.get("format") != FORMAT or not isinstance(doc.get("candidates"), list):
        raise Bad(f"not a {FORMAT} document")
    ids = [c.get("id") if isinstance(c, dict) else None for c in doc["candidates"]]
    if not all(isinstance(i, str) and i for i in ids) or len(set(ids)) != len(ids):
        raise Bad("every candidate needs an id of its own")
    return doc["candidates"]


def fold_candidates(repo: "V.GitVarsRepo", scope: str, candidates: List[Dict[str, object]], tip: Optional[str] = None,
                    gate: bool = True) -> Dict[str, object]:
    """The consequence matrix of a batch of candidates at one tip (see the module's text)."""
    t0 = time.perf_counter()
    T = FR.Tip(V, repo, scope, tip)
    up = DX.Up(T, grounded=True)
    evaluated = set(up.evaluated)
    t1 = time.perf_counter()
    rows: List[Dict[str, object]] = []
    gate_s = 0.0
    for cand in candidates:
        atoms, cells, seals = build(T, scope, cand)
        if not cells and not seals:  # nothing to add: admissible, and nothing changes
            rows.append({"id": cand["id"], "admissible": True, "dirty": 0, "dirty_cells": [], "flips": {}, "read": "empty"})
            continue
        dirty = DX.dirty(up, atoms, {c.id: c for c in cells}, {s.id: s for s in seals}) & evaluated
        row: Dict[str, object] = {"id": cand["id"], "dirty": len(dirty), "dirty_cells": sorted(x.hex() for x in dirty)}
        if not gate and dirty:
            rows.append(dict(row, admissible=None, flips=None, read="unread"))
            continue
        if not gate:
            rows.append(dict(row, admissible=None, flips={}, read="frame"))
            continue
        g0 = time.perf_counter()
        try:
            rep = repo.what_if(scope, atoms, cells, seals, assume=True, statuses=True)
        except V.VarsError as e:
            gate_s += time.perf_counter() - g0
            rows.append(dict(row, admissible=False, refusal=str(e), flips={}, read="gate"))
            continue
        gate_s += time.perf_counter() - g0
        flips: Dict[str, Dict[str, Tuple[bool, bool]]] = {}
        for h, st in rep.get("statuses", {}).items():
            cid = bytes.fromhex(h)
            if cid not in evaluated:
                continue
            b, a = st["before"], st["after"]
            moved = {bit: (bool(b.get(bit)), bool(a.get(bit))) for bit in ("settled", "grounded") if b.get(bit) != a.get(bit)}
            if moved:
                flips[h] = moved
        rows.append(dict(row, admissible=True, flips=flips, read="frame" if not dirty else "gate"))
    t2 = time.perf_counter()
    for row in rows:
        f = row.get("flips") or {}
        row["flipped_settled"] = sorted(h for h, m in f.items() if "settled" in m)
        row["flipped_grounded"] = sorted(h for h, m in f.items() if "grounded" in m)
    classes = classify(rows)
    return {"scope": scope, "tip": T.tip, "candidates": rows, "classes": classes["classes"],
            "discriminating": classes["discriminating"],
            "timing": {"frames_s": round(t1 - t0, 4), "candidates_s": round(t2 - t1, 4), "gate_s": round(gate_s, 4),
                       "filter_s": round(t2 - t1 - gate_s, 4), "candidates": len(rows),
                       "dirty_none": sum(1 for r in rows if r["dirty"] == 0)}}


def classify(rows: List[Dict[str, object]]) -> Dict[str, object]:
    """Group the candidates by what they leave: an admissible candidate by the (Settled, Grounded) it gives every cell it
    changes (two candidates with the same changes leave the same vector on every cell), a refused one by its refusal,
    an unread one alone. For two admissible classes, `cells` are those on which their vectors part."""
    def after(row) -> Dict[str, Dict[str, bool]]:
        return {h: {bit: v[1] for bit, v in m.items()} for h, m in (row["flips"] or {}).items()}

    groups: Dict[str, Dict[str, object]] = {}
    for row in rows:
        if row["admissible"] is False:
            key = "refused: " + row["refusal"]
        elif row["flips"] is None:
            key = "unread: " + row["id"]
        else:
            key = json.dumps(after(row), sort_keys=True)
        g = groups.setdefault(key, {"members": [], "admissible": row["admissible"], "after": None})
        g["members"].append(row["id"])
        if row["admissible"] and row["flips"] is not None:
            g["after"] = after(row)
    out = []
    for n, (key, g) in enumerate(sorted(groups.items(), key=lambda kv: kv[1]["members"][0])):
        out.append({"class": n, "members": g["members"], "admissible": g["admissible"],
                    "changes": g["after"] if g["after"] is not None else None,
                    **({"refusal": key[len("refused: "):]} if key.startswith("refused: ") else {})})
    for c in out:
        for r in rows:
            if r["id"] in c["members"]:
                r["class"] = c["class"]
    disc = []
    open_ = [c for c in out if c["admissible"] and c["changes"] is not None]
    for i, a in enumerate(open_):
        for b in open_[i + 1:]:
            cells = sorted(h for h in set(a["changes"]) | set(b["changes"]) if a["changes"].get(h) != b["changes"].get(h))
            disc.append({"classes": [a["class"], b["class"]], "cells": cells})
    return {"classes": out, "discriminating": disc}


def main(argv: List[str]) -> int:
    gate = "--no-gate" not in argv
    argv = [a for a in argv if a != "--no-gate"]
    tip = None
    if "--tip" in argv:
        i = argv.index("--tip")
        tip = argv[i + 1] if i + 1 < len(argv) else None
        argv = argv[:i] + argv[i + 2:]
    if len(argv) != 3 or (tip is not None and not tip):
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    try:
        cands = read_candidates(Path(argv[2]).read_bytes())
        out = fold_candidates(V.GitVarsRepo(argv[0]), argv[1], cands, tip, gate)
    except Bad as e:
        print(json.dumps({"refused": str(e)}))
        return 1
    print(json.dumps(out, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
