"""What a reader must read to decide a decision's status at a tip: its frame (proofs/Vars1/Reader.lean).

`frame` computes, from the store at a tip, the cells a contract's, decision's or question's Settled (or Grounded) reads:

- `read`: the cells whose standing (Active, not Stale) the status reads. For Settled: the cell, every cell that judges
  it (one that attests it, a verdict on it, a verdict on a checkpoint or cycle witness one of those names), the
  checkpoints they name, and everything those rely on. For Grounded also the judges of every contract, decision or
  question so reached, since Grounded asks Settled of what it rests on.
- `guard`: `read`, with every cell that has an invalidates, retires or supersedes edge into the set, latched or not,
  and every cell a member supersedes, to the fixed point: the cells whose Pass 1 bits the standing of `read` reads.
- `watch`: the cells on which a new seal can change the status: the judges (their endorsers are counted), the sources
  of edges into `guard` (a seal can latch the edge), and the scope, acceptance and custom-schema cells of `guard`
  (a seal can latch Authorized).
- `fallback`: the evaluated cells that name no evaluator policy, so read the governing scope's admission policy: the
  scope caveat. For them a rotation is in the frame.

`touches` reads the objects a later tip adds and says whether any touches the frame: a new cell with an eviction edge
into `guard`, a new cell that judges an evaluated cell, a new seal on a cell of `watch`, and, where `fallback` is not
empty, a new scope cell or a rotation that waited. A rotation to other rules touches every frame: other rules read
the history again. `settled_frame` and `grounded_frame` say that if nothing touches it the status is unchanged; the
frame theorems ask every cell of `guard` to be local, so a frame that holds a foreign cell is `NOT_COVERED`.

`message` builds the smallest thing two parties exchange for "d is in force at T" and counts its bytes
(experiments only: no format of spec §4.4 changes). It has three parts. The claim: scope, decision, tip, the governing
scope cell (the epoch) and the rules identity. The proof: a `minds.witness.held@1` term and the objects it names, so
the positive part (cone and endorsements) is checked from bytes. The vouch: the closed-world part, that the tip holds
no further edge, verdict or seal that touches the frame; nothing proves it short of reading the tip
(`reader_reads_commit`), so someone who read it says so under a key.

This module reads vars1 through the `V` it is given and imports nothing of minds itself, so a copy of it runs anywhere.
"""
import json
import statistics
from typing import Dict, Iterable, List, Optional, Set, Tuple

EVICT = ("h_invalidates", "h_retires", "h_supersedes")
DRAFT = "minds.inforce.draft@0"


class Tip:
    """The store at a tip of a scope's chain and what the lens and the fold say of it."""

    def __init__(self, V, repo, scope: str, tip: Optional[str] = None) -> None:
        self.V, self.repo, self.scope = V, repo, scope
        self.tip = tip or repo.ref_commit(scope)
        self.chain = repo.commit_chain(self.tip)
        self.atoms, self.cells, self.seals = repo.read_cas_tree(self.tip)
        self.lens = repo.lens(scope, at=self.tip)
        fold = repo._evaluate_commit_chain(scope, self.chain)
        self.governing, self.waiting, self.rules = fold["active_scope_id"], fold["waiting"], fold["rules"]
        self._born: Optional[Dict[bytes, int]] = None
        self._kernel: Dict[str, Tuple[bytes, bytes]] = {}

    def born(self, cid: bytes) -> int:
        """The index of the commit that first held the cell."""
        if self._born is None:
            self._born = {}
            for i, (_, cells, _) in enumerate(self.repo.chain_deltas(self.chain)):
                for c in cells:
                    self._born.setdefault(c, i)
        return self._born[cid]

    def kernel_at(self, commit: str) -> Tuple[bytes, bytes]:
        """The kernel's input and output for the chain up to `commit`, a commit of this chain."""
        if commit not in self._kernel:
            deltas = self.repo.chain_deltas(self.repo.commit_chain(commit))
            kernel_input, _ = self.V.kernel_facts(self.scope, deltas)
            out = self.V.kernel_runner(self.V.chain_rules(self.scope, deltas)).run(kernel_input)
            self._kernel[commit] = (kernel_input, out)
        return self._kernel[commit]

    def hv(self, h: bytes) -> List[bytes]:
        return [] if h == self.V.H_EMPTY else self.V.parse_hvec(self.atoms[h], require_sorted=True)

    def is_local(self, cid: bytes) -> bool:
        if cid in self.V.STD_SCHEMA_IDS:
            return True
        return self.V.parse_utf8(self.atoms[self.cells[cid].h_slot_name]).split("/", 1)[0] == self.scope


def evaluated(V, c) -> bool:
    return c.h_schema in (V.H_SCHEMA["contract"], V.H_SCHEMA["decision"], V.H_SCHEMA["question"])


def own_policy(V, c) -> bytes:
    """The evaluator policy a contract, decision or question names, or H_EMPTY."""
    return c.slots[1] if c.h_schema == V.H_SCHEMA["question"] else c.slots[3]


def named_slot(V, c) -> Optional[bytes]:
    """The checkpoint or cycle witness a verdict names, if it names one."""
    if c.h_schema == V.H_SCHEMA["verdict"] and c.slots[0] != V.H_EMPTY:
        return c.slots[0]
    return None


def frame(T: Tip, d: bytes, grounded: bool = False) -> Dict[str, object]:
    """The frame of `d`'s Settled at the tip, or of its Grounded."""
    V, cells = T.V, T.cells
    attesters: Dict[bytes, Set[bytes]] = {}
    on_payload: Dict[bytes, Set[bytes]] = {}
    on_named: Dict[bytes, Set[bytes]] = {}
    into: Dict[bytes, Set[bytes]] = {}
    for cid, c in cells.items():
        for t in T.hv(c.h_attests):
            attesters.setdefault(t, set()).add(cid)
        if c.h_schema == V.H_SCHEMA["verdict"]:
            on_payload.setdefault(c.h_payload, set()).add(cid)
            if named_slot(V, c) is not None:
                on_named.setdefault(c.slots[0], set()).add(cid)
        for field in EVICT:
            for t in T.hv(getattr(c, field)):
                into.setdefault(t, set()).add(cid)

    def judges_of(v: bytes) -> Tuple[Set[bytes], Set[bytes]]:
        direct = attesters.get(v, set()) | on_payload.get(v, set())
        named = {n for w in direct for n in [named_slot(V, cells[w])] if n is not None}
        return direct | {b for n in named for b in on_named.get(n, set())}, {n for n in named if n in cells}

    def down(roots: Iterable[bytes]) -> Set[bytes]:
        out, todo = set(roots), list(roots)
        while todo:
            for r in T.hv(cells[todo.pop()].h_relies):
                if r not in out:
                    out.add(r)
                    todo.append(r)
        return out

    judges, named = judges_of(d)
    ev = {d}
    read = down({d} | judges | named)
    while grounded:
        more = {v for v in read if evaluated(V, cells[v])} - ev
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
        for y in into.get(x, set()) | set(T.hv(cells[x].h_supersedes)):
            if y not in guard:
                guard.add(y)
                todo.append(y)
    sources = {w for x in guard for w in into.get(x, set())}
    latching = {x for x in guard if cells[x].h_schema in (V.H_META_SCHEMA, V.H_SCHEMA["acceptance"], V.H_SCHEMA["scope"])}
    return {
        "decision": d, "grounded": grounded, "tip": T.tip,
        "read": sorted(read), "guard": sorted(guard), "judges": sorted(judges), "named": sorted(named),
        "sources": sorted(sources), "evaluated": sorted(ev), "watch": sorted(judges | sources | latching),
        "fallback": sorted(v for v in ev if own_policy(V, cells[v]) == V.H_EMPTY),
        "covered": all(T.is_local(x) for x in guard),
        "waiting": T.waiting is not None, "rules_change_waiting": bool(T.waiting and T.waiting[2]),
        "rules": cells[T.governing].slots[2],
    }


def delta(T: Tip, later: str) -> Tuple[Dict[bytes, bytes], Dict[bytes, object], Dict[bytes, object]]:
    """What the commits after `T.tip` up to `later` add: the objects a reader renewing a witness reads."""
    chain = T.repo.commit_chain(later)
    if chain[:len(T.chain)] != T.chain:
        raise ValueError("the later tip does not extend the earlier one")
    atoms: Dict[bytes, bytes] = {}
    cells: Dict[bytes, object] = {}
    seals: Dict[bytes, object] = {}
    for a, c, s in T.repo.chain_deltas(chain[len(T.chain):]):
        atoms.update(a)
        cells.update(c)
        seals.update(s)
    return atoms, cells, seals


def touches(T: Tip, fr: Dict[str, object], new_atoms, new_cells, new_seals, memo: Optional[dict] = None
            ) -> Optional[Tuple[str, str]]:
    """The first object of a later tip that touches the frame, as (reason, id), or None: then the status the frame
    is of is what it was. Reads only the frame and the new objects."""
    V = T.V
    if not fr["covered"]:
        return ("NOT_COVERED", fr["decision"].hex())
    if fr["rules_change_waiting"]:
        return ("RULES", "a rules change waits at the tip")
    if fr["fallback"] and fr["waiting"]:
        return ("WAITING", "a rotation waits at the tip")
    guard, ev, named, watch = set(fr["guard"]), set(fr["evaluated"]), set(fr["named"]), set(fr["watch"])

    memo = {} if memo is None else memo

    def hv(h: bytes) -> List[bytes]:
        if h not in memo:
            memo[h] = [] if h == V.H_EMPTY else V.parse_hvec(new_atoms[h] if h in new_atoms else T.atoms[h],
                                                             require_sorted=True)
        return memo[h]

    for cid in sorted(new_cells):
        c = new_cells[cid]
        if c.h_schema == V.H_SCHEMA["scope"]:
            if c.slots[2] != fr["rules"]:
                return ("RULES", cid.hex())
            if fr["fallback"]:
                return ("SCOPE", cid.hex())
        if any(t in guard for field in EVICT for t in hv(getattr(c, field))):
            return ("EDGE", cid.hex())
        if any(t in ev for t in hv(c.h_attests)):
            return ("JUDGE", cid.hex())
        if c.h_schema == V.H_SCHEMA["verdict"] and (c.h_payload in ev or named_slot(V, c) in named):
            return ("JUDGE", cid.hex())
    for sid in sorted(new_seals):
        if new_seals[sid].h_target in watch:
            return ("SEAL", sid.hex())
    return None


# --- measurements -------------------------------------------------------------------------------------------------

def _hex_json(obj) -> int:
    """The bytes of a message as it travels: compact JSON, objects in hex, as the bundles of spec §4.4 are."""
    return len(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode())


def _raw(obj) -> int:
    """The bytes of the objects a bundle carries, each counted once as bytes and not as hex."""
    if isinstance(obj, dict):
        return sum(_raw(v) for k, v in obj.items() if k != "format")
    if isinstance(obj, list):
        return sum(_raw(v) for v in obj)
    return len(obj) // 2 if isinstance(obj, str) else 0


def frame_objects(T: Tip, fr: Dict[str, object]) -> Dict[str, List[bytes]]:
    """The bytes the frame is made of: its cells, the seals on its watched cells, the atoms their fields name (edge
    lists, verifier ids, slot names, policies and their key lists), and the governing scope with its policy."""
    V = T.V
    cells = [T.cells[x] for x in fr["guard"]]
    seals = [s for s in T.seals.values() if s.h_target in set(fr["watch"])]
    need: Set[bytes] = set()
    for c in cells:
        need |= {c.h_slot_name, c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates}
        if c.h_schema == V.H_SCHEMA["verdict"]:
            need.add(c.slots[2])
        if evaluated(V, c) and own_policy(V, c) != V.H_EMPTY:
            need |= {own_policy(V, c), V.parse_pol1(T.atoms[own_policy(V, c)])[1]}
    scope = []
    if fr["fallback"]:
        g = T.cells[T.governing]
        scope = [g]
        need |= {g.slots[0], V.parse_pol1(T.atoms[g.slots[0]])[1]}
    return {"cells": [c.encode() for c in cells], "seals": [s.encode() for s in seals], "scope": [c.encode() for c in scope],
            "atoms": [T.atoms[h] for h in sorted(need) if h != V.H_EMPTY and h in T.atoms]}


def message(T: Tip, term: Dict[str, object], vouch: Dict[str, object]) -> Dict[str, object]:
    """The draft message "d is in force at T": the claim, the proof (the witness term with every object it names:
    the cone's cells, the endorsing seals, the atoms those name, and the scope cells the seals are under with their
    rosters), and the vouch for the closed-world part. `vouch` is given: who says that nothing else at the tip
    touches the frame, and under which seals."""
    V = T.V
    cone = [T.cells[bytes.fromhex(x)] for x in term["cone"]]
    seals = [T.seals[bytes.fromhex(e["seal"])] for e in term["endorsements"]]
    need: Set[bytes] = set()
    for c in cone:
        need |= {c.h_slot_name, c.h_relies, c.h_attests}
        if evaluated(V, c) and own_policy(V, c) != V.H_EMPTY:
            need |= {own_policy(V, c), V.parse_pol1(T.atoms[own_policy(V, c)])[1]}
    scopes, x = [], T.governing
    wanted = {s.h_scope_ctx for s in seals} | {T.governing}
    while x is not None:  # the governing scope and each it supersedes, back to the oldest one a seal is under
        c = T.cells[x]
        scopes.append(c)
        need |= {c.h_slot_name, c.h_supersedes, c.slots[0], V.parse_pol1(T.atoms[c.slots[0]])[1]}
        wanted.discard(x)
        x = next(iter(T.hv(c.h_supersedes)), None) if wanted else None
    return {
        "format": DRAFT,
        "claim": {"scope": T.scope, "decision": term["decision"], "tip": T.tip, "epoch": T.governing.hex(),
                  "rules": T.cells[T.governing].slots[2].hex()},
        "proof": {"term": term, "cells": sorted(c.encode().hex() for c in cone),
                  "seals": sorted(s.encode().hex() for s in seals),
                  "scopes": [c.encode().hex() for c in scopes],
                  "atoms": sorted(T.atoms[h].hex() for h in need if h != V.H_EMPTY and h in T.atoms)},
        "vouch": vouch,
    }


def covering_at(T: Tip, d: bytes) -> Optional[bytes]:
    """The latest projection of the tip's store whose own tip already holds `d`, preferring one the lens settles
    (witnessed): `tools/minds_chain.py`'s choice, read at this tip and not at the ref."""
    V, best = T.V, None
    for pid, c in T.cells.items():
        if c.h_schema != V.H_SCHEMA["projection"]:
            continue
        at = V.parse_utf8(T.atoms[c.slots[0]])
        if at in T.chain and T.born(d) <= T.chain.index(at):
            key = (bool(T.lens["settled"].get(pid)), T.chain.index(at), pid)
            if best is None or key > best:
                best = key
    return None if best is None else best[2]


def projection_at(T: Tip, pid: bytes, with_data: bool = True) -> Dict[str, object]:
    """`vars1.export_projection`'s bundle, from the store at this tip and not at the ref."""
    V, cell = T.V, T.cells[pid]
    pol = T.atoms[cell.slots[4]]
    need = [cell.slots[0], cell.slots[4], V.parse_pol1(pol)[1]]
    bundle: Dict[str, object] = {
        "format": V.BUNDLE_FORMAT, "cell": cell.encode().hex(), "atoms": [T.atoms[h].hex() for h in need],
        "seals": sorted(s.encode().hex() for s in T.seals.values() if s.h_target == pid)}
    if with_data:
        kernel_input, out = T.kernel_at(V.parse_utf8(T.atoms[cell.slots[0]]))
        bundle["input"], bundle["output"] = kernel_input.hex(), out.hex()
    return bundle


def bundle_at(T: Tip, d: bytes, pid: Optional[bytes] = None) -> Dict[str, object]:
    """`vars1.export_attestation`'s bundle, from the store at this tip and not at the ref (test 19 holds the two
    equal where the tip is the ref's)."""
    V, dc, at = T.V, T.cells[d], T.tip
    if pid is not None:
        at = V.parse_utf8(T.atoms[T.cells[pid].slots[0]])
    s_cell = T.cells[T.repo._evaluate_commit_chain(T.scope, T.repo.commit_chain(at))["active_scope_id"]]
    pol = dc.slots[3] if dc.slots[3] != V.H_EMPTY else s_cell.slots[0]
    verdicts = [c for c in T.cells.values() if c.h_schema == V.H_SCHEMA["verdict"] and c.h_payload == d]
    need = [pol, V.parse_pol1(T.atoms[pol])[1], dc.h_payload]
    for w in verdicts:
        need += [w.h_attests, w.slots[2]]
    targets = {d} | {w.id for w in verdicts}
    bundle: Dict[str, object] = {
        "format": V.ATTESTATION_FORMAT, "cell": dc.encode().hex(), "scope": s_cell.encode().hex(),
        "atoms": sorted({T.atoms[h].hex() for h in need if h in T.atoms}),
        "verdicts": sorted(w.encode().hex() for w in verdicts),
        "seals": sorted(x.encode().hex() for x in T.seals.values() if x.h_target in targets)}
    if pid is not None:
        bundle["projection"] = projection_at(T, pid)
    return bundle


def measure(V, repo, scope: str, tip: Optional[str] = None, prove=None) -> Dict[str, object]:
    """The table for one tip: for every decision the lens settles, the size of what its status reads, in cells and in
    bytes, against the attestation bundle a client receives today; and how many decisions read the scope's policy."""
    T = Tip(V, repo, scope, tip)
    lens = T.lens
    decisions = sorted(cid for cid, c in T.cells.items() if c.h_schema == V.H_SCHEMA["decision"])
    settled = [d for d in decisions if lens["settled"].get(d)]
    rows = []
    for d in settled:
        fs, fg = frame(T, d), frame(T, d, grounded=True)
        objs = frame_objects(T, fs)
        row = {"read": len(fs["read"]), "guard": len(fs["guard"]), "guard_grounded": len(fg["guard"]),
               "watched_seals": len(objs["seals"]),
               "frame_bytes": sum(len(x) for k in ("cells", "seals", "scope", "atoms") for x in objs[k]),
               "frame_json": _hex_json({k: [x.hex() for x in v] for k, v in objs.items()})}
        if prove is not None:
            term = prove(repo, scope, d, T.tip)
            row["cone"] = len(term["cone"])
            row["proof_json"] = _hex_json(message(T, term, {})["proof"])
            pid = covering_at(T, d)
            if pid is not None:
                vouch = {"kind": "projection", **projection_at(T, pid, with_data=False)}
                row["vouch_json"] = _hex_json(vouch)
                row["message_json"] = _hex_json(message(T, term, vouch))
                bundle = bundle_at(T, d, pid)
                row["bundle_json"] = _hex_json(bundle)
                row["bundle_bytes"] = _raw(bundle)
                row["bundle_input"] = len(bundle["projection"]["input"]) // 2
        rows.append(row)

    def mmm(key: str):
        xs = [r[key] for r in rows if key in r]
        return [min(xs), statistics.median(xs), max(xs)] if xs else None

    fallback = [d for d in decisions if own_policy(V, T.cells[d]) == V.H_EMPTY]
    out = {
        "tip": T.tip, "scope": scope, "governing_scope": T.governing.hex(), "rules": T.rules.hex(),
        "store": {"cells": len(T.cells), "seals": len(T.seals), "atoms": len(T.atoms), "commits": len(T.chain)},
        "decisions": len(decisions), "settled": len(settled),
        "scope_caveat": {"decisions": len(fallback), "settled": sum(d in fallback for d in settled)},
        "kernel_input_at_tip": len(lens["kernel_input"]),
        "min_median_max": {k: mmm(k) for k in ("read", "guard", "guard_grounded", "watched_seals", "cone", "frame_bytes",
                                                 "frame_json", "proof_json", "vouch_json", "message_json", "bundle_json",
                                                 "bundle_bytes", "bundle_input")},
        "with_bundle": sum("bundle_json" in r for r in rows),
    }
    return out


if __name__ == "__main__":
    # python experiments/witness/frame.py [REPO [SCOPE [TIP]]]: the table of README.md, as JSON
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import vars1  # noqa: E402
    import prove as _prove  # noqa: E402
    _a = sys.argv[1:]
    print(json.dumps(measure(vars1, vars1.GitVarsRepo(Path(_a[0] if _a else Path(__file__).resolve().parents[2])),
                             _a[1] if len(_a) > 1 else "minds", _a[2] if len(_a) > 2 else None, _prove.prove),
                     indent=1, sort_keys=True))
