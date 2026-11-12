"""Make a witness (format `minds.witness.held@1`) that a decision is Settled at a tip, from the lens.

The prover may use anything: it reads the lens through vars1.py. What it produces is checked by check.py, which
uses none of it. A decision the lens does not hold Settled gets no witness (NotHeld). Among its standing ATTESTED
verdicts the prover prefers those whose cones no cell invalidates, retires or supersedes, since such cones need
no edge decided; it names only the keys the lens counts through each (an INVALID verdict under the same verifier id
withdraws the keys that seal it), and takes verdicts until their distinct policy keys meet the threshold.
"""
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import vars1 as V  # noqa: E402

FORMAT = "minds.witness.held@1"


class NotHeld(Exception):
    pass


def prove(repo: "V.GitVarsRepo", scope: str, decision: bytes, tip: Optional[str] = None) -> Dict[str, object]:
    tip = tip or repo.ref_commit(scope)
    lens = repo.lens(scope, at=tip)
    if not (lens["active"].get(decision) and not lens["stale"].get(decision) and lens["settled"].get(decision)):
        raise NotHeld(f"{decision.hex()} is not Settled at {tip}")
    atoms, cells, seals = repo.read_cas_tree(tip)
    scope_id = repo._evaluate_commit_chain(scope, repo.commit_chain(tip))["active_scope_id"]
    hv = lambda h: [] if h == V.H_EMPTY else V.parse_hvec(atoms[h], require_sorted=True)  # noqa: E731
    # the scopes that governed: the active one and each it supersedes; a seal under one counts by a key of its roster
    rosters, x = {}, scope_id
    while x is not None:
        rosters[x] = set(V.parse_hvec(atoms[V.parse_pol1(atoms[cells[x].slots[0]])[1]], require_sorted=True))
        x = next(iter(hv(cells[x].h_supersedes)), None)
    d = cells[decision]
    thr, keys_h = V.parse_pol1(atoms[d.slots[3] if d.slots[3] != V.H_EMPTY else cells[scope_id].slots[0]])
    keys = set(V.parse_hvec(atoms[keys_h], require_sorted=True))
    killed = {t for c in cells.values() for h in (c.h_invalidates, c.h_retires, c.h_supersedes) for t in hv(h)}

    def closure(roots: List[bytes]) -> Set[bytes]:
        out, todo = set(roots), list(roots)
        while todo:
            for r in hv(cells[todo.pop()].h_relies):
                if r not in out:
                    out.add(r)
                    todo.append(r)
        return out

    standing = lambda c: lens["active"].get(c) and not lens["stale"].get(c)  # noqa: E731
    counts = lens["counted_witnesses"].get(decision, {})
    verdicts = [w for w in cells.values() if w.h_schema == V.H_SCHEMA["verdict"] and w.h_payload == decision
                and decision in hv(w.h_attests) and w.slots[0] == V.H_EMPTY and w.slots[1] == V.H_ATTESTED
                and standing(w.id)]
    clean = lambda w: not (closure([w.id]) & killed)  # noqa: E731
    chosen, counted, ends = [], set(), []
    for w in sorted(verdicts, key=lambda w: (not clean(w), w.id)):
        new = sorted((s.actor_pubkey, sid) for sid, s in seals.items() if s.h_target == w.id
                     and s.actor_pubkey in rosters.get(s.h_scope_ctx, ()) and s.actor_pubkey in keys
                     and s.actor_pubkey in counts.get(w.id, ()) and s.actor_pubkey not in counted)
        if not new:
            continue
        chosen.append(w.id)
        for k, sid in new:
            if k not in counted and len(counted) < thr:
                counted.add(k)
                ends.append({"verdict": w.id.hex(), "seal": sid.hex()})
        if len(counted) >= thr:
            break
    if len(counted) < thr:
        raise NotHeld(f"the lens holds {decision.hex()} Settled, but no {thr} sealed policy keys were found")
    return {"format": FORMAT, "scope": scope, "tip": tip, "decision": decision.hex(),
            "cone": sorted(x.hex() for x in closure([decision, *chosen])), "endorsements": ends}


UNFOUNDED = "minds.witness.unfounded@1"


def prove_unfounded(repo: "V.GitVarsRepo", scope: str, decision: bytes, tip: Optional[str] = None) -> Dict[str, object]:
    """A certificate (format `minds.witness.unfounded@1`) that a decision is not Grounded at a tip: the cells that are
    not Grounded among those its Grounded reads, from the decision down `relies` and to the verdicts that judge an
    evaluated cell (`unfounded_complete`: the cells that are not Grounded form an unfounded set; this keeps the part
    the decision's equation reaches). check.py verifies it with none of this."""
    tip = tip or repo.ref_commit(scope)
    lens = repo.lens(scope, at=tip)
    if lens["grounded"].get(decision):
        raise NotHeld(f"{decision.hex()} is Grounded at {tip}")
    atoms, cells, _ = repo.read_cas_tree(tip)
    hv = lambda h: [] if h == V.H_EMPTY else V.parse_hvec(atoms[h], require_sorted=True)  # noqa: E731
    judges: Dict[bytes, List[bytes]] = {}
    for w, c in cells.items():
        if c.h_schema == V.H_SCHEMA["verdict"]:
            judges.setdefault(c.h_payload, []).append(w)
    out, todo = set(), [decision]
    while todo:
        x = todo.pop()
        if x in out or x not in cells or lens["grounded"].get(x):
            continue
        out.add(x)
        todo += hv(cells[x].h_relies) + judges.get(x, [])
    return {"format": UNFOUNDED, "scope": scope, "tip": tip, "decision": decision.hex(),
            "unfounded": sorted(x.hex() for x in out)}
