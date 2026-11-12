#!/usr/bin/env python3
"""Which tensions on a decision profile's goals are worth a question, and which questions are silence.

    python3 experiments/decisions/profile.py REPO SCOPE PROFILE.json [--tip COMMIT] [--since COMMIT]
                                             [--candidates CANDIDATES.json]

A graph that can say what to ask next (`minds_chain.py next`) and what a reading would change (`fold.py`) holds
thousands of open points. A decision profile (`minds.decisions.profile@1`) names what matters to its reader:

    {"format": "minds.decisions.profile@1",
     "goals": [CELL, ...],          contracts, decisions or questions whose Settled and Grounded matter
     "obligations": [CELL, ...],    evaluated cells that must stay live (not Invalidated, not Stale)
     "max_cost_steps": 1000,        a goal more keys than this from Settled is out of budget, not a question
     "preferences": {"min_cut_threshold": 2},   a Grounded goal that fewer keys than this can unsettle is fragile
     "precedents": [{"kind", "target_goal", "signature", "chosen"}, ...]}     tensions already resolved

`filter_tensions` reads, at a tip, only each goal's frame (the cells its Grounded reads, `frame.py`), and names four
kinds of tension:

- INCOMPLETENESS: a live goal short of its quorum (`deficit` keys of its policy), or Settled and not Grounded (the
  cells it rests on that are not founded, `prove_unfounded`). Its `competing_trajectories` are the sets of missing
  keys that would close it: one is a missing fact (will that key attest?), several a missing criterion (which way?);
- CONTRADICTION: a goal or obligation that is not live, or a goal with a live ATTESTED and a live INVALID verdict;
- FRAGILITY: a Grounded goal whose quorum fewer than `min_cut_threshold` withdrawals undo (its margin plus one: the
  goal's own quorum, not the cut over its whole frame, which `GitVarsRepo.power` reads);
- UNREALIZED_POSSIBILITY: with `since`, a goal whose deficit fell from more than one to one: one key from Settled
  because of what others filed.

Everything outside the goals' frames is silence (`proofs/Vars1/Silence.lean`, `silence_outside_reads`: a change
outside every frame leaves every goal's Settled and Grounded as it was). So are candidate readings (`fold.py`'s format)
whose objects touch no goal's frame (`delta.dirty`, held to `touches` by test 25 of `test_witness.py`): they are
listed `silent`, and the rest `loud` with the goals they touch. A tension whose signature a precedent records is
`suppressed`; `record_resolution` adds one. It reads vars1.py and the witness spike's `frame.py`, `delta.py` and
`prove.py`, the standard library, and no network.
"""
import hashlib
import itertools
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "experiments" / "witness"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import vars1 as V  # noqa: E402
import frame as FR  # noqa: E402
import delta as DX  # noqa: E402
import prove as PR  # noqa: E402
import fold as FO  # noqa: E402

PROFILE = "minds.decisions.profile@1"
KINDS = ("INCOMPLETENESS", "CONTRADICTION", "FRAGILITY", "UNREALIZED_POSSIBILITY")
EVALUATED = (V.H_SCHEMA["contract"], V.H_SCHEMA["decision"], V.H_SCHEMA["question"])
TRAJECTORIES = 8  # at most this many key sets are listed; `trajectories` counts them all


class Bad(Exception):
    """A profile that does not read one way."""


@dataclass
class Tension:
    kind: str
    target_goal: str
    evidence_gap: List[str]
    competing_trajectories: List[Dict[str, object]]
    blast_radius_on_goals: int
    question_prompt: str
    signature: str = ""
    detail: Dict[str, object] = field(default_factory=dict)


def _hex64(x: object) -> bool:
    return isinstance(x, str) and len(x) == 64 and all(ch in "0123456789abcdef" for ch in x)


def read_profile(raw: bytes) -> Dict[str, object]:
    """The profile, one reading only: UTF-8 JSON, no key named twice, the fields above and no others."""
    def one_reading(pairs):
        keys = [k for k, _ in pairs]
        if len(keys) != len(set(keys)):
            raise Bad("an object names a key twice")
        return dict(pairs)
    try:
        doc = json.loads(raw.decode("utf-8"), object_pairs_hook=one_reading)
    except (UnicodeDecodeError, json.JSONDecodeError) as e:
        raise Bad(f"not UTF-8 JSON: {e}") from None
    return check_profile(doc)


def check_profile(doc: object) -> Dict[str, object]:
    if not isinstance(doc, dict) or doc.get("format") != PROFILE:
        raise Bad(f"not a {PROFILE} document")
    extra = set(doc) - {"format", "goals", "obligations", "max_cost_steps", "preferences", "precedents"}
    if extra:
        raise Bad(f"unknown fields: {sorted(extra)}")
    goals, obligations = doc.get("goals"), doc.get("obligations", [])
    for name, xs in (("goals", goals), ("obligations", obligations)):
        if not isinstance(xs, list) or not all(_hex64(x) for x in xs) or len(set(xs)) != len(xs):
            raise Bad(f"`{name}` is not a list of distinct 64-digit cell ids")
    budget = doc.get("max_cost_steps", 1000)
    if not isinstance(budget, int) or isinstance(budget, bool) or budget < 0:
        raise Bad("`max_cost_steps` is not a natural number")
    prefs = doc.get("preferences", {})
    if not isinstance(prefs, dict) or set(prefs) - {"min_cut_threshold"}:
        raise Bad("`preferences` holds `min_cut_threshold` only")
    mct = prefs.get("min_cut_threshold", 1)
    if not isinstance(mct, int) or isinstance(mct, bool) or mct < 1:
        raise Bad("`min_cut_threshold` is not a positive integer")
    precedents = doc.get("precedents", [])
    if not isinstance(precedents, list) or not all(
            isinstance(p, dict) and p.get("kind") in KINDS and _hex64(p.get("target_goal"))
            and _hex64(p.get("signature")) for p in precedents):
        raise Bad("`precedents` is not a list of {kind, target_goal, signature, chosen}")
    return {"format": PROFILE, "goals": list(goals), "obligations": list(obligations), "max_cost_steps": budget,
            "preferences": {"min_cut_threshold": mct}, "precedents": list(precedents)}


def _sig(kind: str, goal: str, evidence: List[str]) -> str:
    return hashlib.sha256(json.dumps([kind, goal, sorted(evidence)]).encode()).hexdigest()


def _state(T, g: bytes) -> Dict[str, object]:
    """What the lens says of an evaluated cell: live, Settled, Grounded, its policy and the keys that count."""
    lens = T.lens
    live = bool(lens["active"].get(g)) and not lens["stale"].get(g)
    thr, keys = lens["evaluators"].get(g, (0, set()))
    counted: Set[bytes] = set().union(*lens["counted_witnesses"].get(g, {}).values()) & set(keys)
    verdicts = [w for w, c in T.cells.items() if c.h_schema == V.H_SCHEMA["verdict"] and c.h_payload == g
                and lens["active"].get(w) and not lens["stale"].get(w)]
    return {"live": live, "settled": bool(lens["settled"].get(g)), "grounded": bool(lens["grounded"].get(g)),
            "thr": thr, "keys": set(keys), "counted": counted, "deficit": max(0, thr - len(counted)),
            "margin": len(counted) - thr,
            "attested": sorted(w for w in verdicts if T.cells[w].slots[1] == V.H_ATTESTED),
            "invalid": sorted(w for w in verdicts if T.cells[w].slots[1] == V.H_VERDICT_INVALID)}


def _short(x: bytes) -> str:
    return x.hex()[:8]


def filter_tensions(repo: "V.GitVarsRepo", scope: str, profile: Dict[str, object], tip: Optional[str] = None,
                    candidates: Optional[List[Dict[str, object]]] = None, since: Optional[str] = None) -> Dict[str, object]:
    """The tensions on the profile's goals and obligations at `tip`, and which candidate readings are silent."""
    profile = check_profile(profile)
    T = FR.Tip(V, repo, scope, tip)
    goals = [bytes.fromhex(x) for x in profile["goals"]]
    obligations = [bytes.fromhex(x) for x in profile["obligations"]]
    absent = [x.hex() for x in goals + obligations if x not in T.cells or T.cells[x].h_schema not in EVALUATED]
    goals = [x for x in goals if x.hex() not in absent]
    obligations = [x for x in obligations if x.hex() not in absent]
    frames = {g: set(FR.frame(T, g, grounded=True)["read"]) for g in goals}
    radius = lambda g: sum(1 for o in goals if g in frames[o])  # noqa: E731
    before = FR.Tip(V, repo, scope, since) if since else None
    mct, budget = profile["preferences"]["min_cut_threshold"], profile["max_cost_steps"]
    done = {(p["kind"], p["target_goal"], p["signature"]) for p in profile["precedents"]}
    tensions: List[Tension] = []
    over_budget: List[str] = []

    def add(kind: str, g: bytes, evidence: List[str], prompt: str, paths=(), **detail) -> None:
        t = Tension(kind, g.hex(), sorted(evidence), list(paths), radius(g) if g in frames else 0, prompt,
                    _sig(kind, g.hex(), evidence), dict(detail))
        tensions.append(t)

    for g in obligations:
        if not _state(T, g)["live"] and g not in goals:
            dead = [x.hex() for x in sorted(set(FR.frame(T, g)["read"])) if not T.lens["active"].get(x)
                    or T.lens["stale"].get(x)]
            add("CONTRADICTION", g, dead, f"obligation {_short(g)} is not live ({len(dead)} cells it rests on are "
                "not): was that meant?", reason="obligation not live")
    for g in goals:
        st = _state(T, g)
        if not st["live"]:
            dead = [x.hex() for x in sorted(frames[g]) if not T.lens["active"].get(x) or T.lens["stale"].get(x)]
            add("CONTRADICTION", g, dead, f"goal {_short(g)} is not live ({len(dead)} cells of its frame are not): was "
                "that meant?", reason="goal not live")
            continue
        if st["attested"] and st["invalid"]:
            ev = [x.hex() for x in st["attested"] + st["invalid"]]
            add("CONTRADICTION", g, ev, f"goal {_short(g)} has {len(st['attested'])} live ATTESTED and "
                f"{len(st['invalid'])} live INVALID verdicts: which stands?", reason="verdicts disagree")
        if not st["settled"]:
            missing = sorted(st["keys"] - st["counted"])
            if st["deficit"] > budget:
                over_budget.append(g.hex())
                continue
            ways = list(itertools.combinations(missing, st["deficit"]))
            trajectories = [{"keys": [k.hex() for k in w]} for w in ways[:TRAJECTORIES]]
            was = _state(before, g) if before and g in before.cells else None
            if was is not None and not was["settled"] and was["deficit"] > 1 and st["deficit"] == 1:
                add("UNREALIZED_POSSIBILITY", g, [k.hex() for k in missing],
                    f"goal {_short(g)} is one key from Settled since {since[:8]} (it was {was['deficit']}): ask "
                    f"{'it' if len(missing) == 1 else f'one of {len(missing)} keys'}?", trajectories,
                    deficit=st["deficit"], deficit_before=was["deficit"], trajectories=len(ways))
            elif len(ways) == 1:
                add("INCOMPLETENESS", g, [k.hex() for k in missing], f"goal {_short(g)} needs {st['deficit']} more key(s), "
                    f"and only one set can give it: will {', '.join(_short(k) for k in ways[0])} attest it? (a missing "
                    "fact)", trajectories, deficit=st["deficit"], trajectories=1)
            else:
                add("INCOMPLETENESS", g, [k.hex() for k in missing], f"goal {_short(g)} needs {st['deficit']} of "
                    f"{len(missing)} keys: which of {len(ways)} ways should close it? (a missing criterion)",
                    trajectories, deficit=st["deficit"], trajectories=len(ways))
        elif not st["grounded"]:
            loose = sorted(set(PR.prove_unfounded(repo, scope, g, T.tip)["unfounded"]) - {g.hex()})
            add("INCOMPLETENESS", g, loose, f"goal {_short(g)} is Settled and not Grounded: {len(loose)} cells it "
                "rests on are not founded; which should be?", reason="support not founded")
        elif st["margin"] + 1 < mct:
            add("FRAGILITY", g, [k.hex() for k in st["counted"]], f"goal {_short(g)} is Grounded, and {st['margin'] + 1} "
                f"withdrawal(s) of its {len(st['counted'])} counted keys unsettle it; the profile asks for {mct}",
                margin=st["margin"])
    kept = [t for t in tensions if (t.kind, t.target_goal, t.signature) not in done]
    out: Dict[str, object] = {
        "scope": scope, "tip": T.tip, "since": since, "absent": absent, "over_budget": over_budget,
        "tensions": [asdict(t) for t in kept],
        "suppressed": [t.signature for t in tensions if (t.kind, t.target_goal, t.signature) in done]}
    if candidates is not None:
        up = DX.Up(T, grounded=True)
        goalset = set(goals) | set(obligations)
        silent, loud = [], {}
        for cand in candidates:
            atoms, cells, seals = FO.build(T, scope, cand)
            touched = DX.dirty(up, atoms, {c.id: c for c in cells}, {s.id: s for s in seals}) & goalset
            if touched:
                loud[cand["id"]] = sorted(x.hex() for x in touched)
            else:
                silent.append(cand["id"])
        out["candidates"] = {"silent": silent, "loud": loud}
    return out


def record_resolution(profile: Dict[str, object], tension: Dict[str, object], chosen: object) -> Dict[str, object]:
    """The profile with the tension recorded as a precedent: the lens does not raise it again while its evidence is the
    same. The profile given is not changed."""
    p = check_profile(json.loads(json.dumps(profile)))
    p["precedents"] = p["precedents"] + [{"kind": tension["kind"], "target_goal": tension["target_goal"],
                                          "signature": tension["signature"], "chosen": chosen}]
    return check_profile(p)


def main(argv: List[str]) -> int:
    opts: Dict[str, str] = {}
    for flag in ("--tip", "--since", "--candidates"):
        if flag in argv:
            i = argv.index(flag)
            if i + 1 >= len(argv):
                print(__doc__.split("\n\n")[1], file=sys.stderr)
                return 2
            opts[flag] = argv[i + 1]
            argv = argv[:i] + argv[i + 2:]
    if len(argv) != 3:
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    try:
        profile = read_profile(Path(argv[2]).read_bytes())
        cands = FO.read_candidates(Path(opts["--candidates"]).read_bytes()) if "--candidates" in opts else None
        out = filter_tensions(V.GitVarsRepo(argv[0]), argv[1], profile, opts.get("--tip"), cands, opts.get("--since"))
    except (Bad, FO.Bad) as e:
        print(json.dumps({"refused": str(e)}))
        return 1
    print(json.dumps(out, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
