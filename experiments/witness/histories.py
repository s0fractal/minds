"""The histories the witness tests run on: a project kept by three maintainers, built as a real VARS-1 chain.

Grounds, checks resting on grounds, decisions resting on checks, and approvals, each relying on the checks its
maintainer ran. A decision is in force with two approvals that stand. Then one ground is found invalid.

This is the generator of the G6 usability pilot (roadmap G6, withdrawn; experiments/g6/RETIRED.md), kept unchanged
where it shapes a history: the seeds, the draw, the constraints and the chain. The `g6/` that `seeds` hashes is part of
every history's seed. What the pilot added around it (renderings, prompts, a model runner, a scorer) is retired.
"""
import hashlib
import random
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import vars1 as V  # noqa: E402

SCOPE = "proj"
MEMBERS = ("ana", "bo", "cy")
THRESHOLD = 2
SIZES = {"S": (7, 14, 12), "L": (10, 24, 30)}  # grounds, checks, decisions
BOUNDS = {"S": (3, 8, 3), "L": (5, 20, 5)}  # fewest and most decisions no longer in force; fewest still in force
RELY, DROP = "RELY", "DO_NOT_RELY"

GROUND_KINDS = [  # (name pattern, words, what recording it established)
    ("dataset `{}`", ["orders-2026Q2", "orders-2026Q3", "users-2026Q3", "events-v4", "events-v5"],
     "its checksum matched the warehouse export"),
    ("toolchain `{}`", ["rustc-1.95", "rustc-1.96", "llvm-21", "llvm-22"],
     "built from source; its hash matched the published one"),
    ("fixture `{}`", ["fx-17", "fx-18", "fx-21", "fx-22"], "recorded from the production database"),
    ("audit of `{}`", ["libfoo-3.2", "libfoo-3.3", "libbar-1.9", "libbaz-0.8"],
     "a security audit found no open issue in the library"),
    ("bench machine `{}`", ["bench-a", "bench-b", "bench-c"], "measured and pinned as the benchmark host"),
]
CHECK_NAMES = ["latency-p99", "throughput-1k", "parser-fuzz-24h", "schema-migration", "replay-orders", "memory-ceiling",
               "crash-recovery", "tls-handshake", "export-roundtrip", "cold-start", "index-rebuild", "auth-regression",
               "cache-coherence", "backup-restore", "billing-reconcile", "load-shedding", "upgrade-in-place",
               "clock-skew", "quota-enforcement", "search-relevance", "webhook-retry", "csv-import", "rate-limit-burst",
               "disk-full", "failover-drill", "timezone-dst", "unicode-names", "api-compat-v2"]
DECISION_TITLES = ["switch the parser to streaming", "enable the new cache", "drop support for schema v3",
                   "adopt libfoo 3.3", "raise the connection limit", "make index rebuild incremental",
                   "ship the export API", "accept TLS 1.3 only", "merge the billing service", "remove the legacy importer",
                   "enable crash-safe writes", "move backups to hourly", "default to the async client",
                   "rotate the signing key yearly", "turn on load shedding", "allow upgrades in place",
                   "retire the v1 API", "enforce quotas per tenant", "retry webhooks with backoff", "accept CSV imports",
                   "raise the burst rate limit", "fail over automatically", "store times in UTC",
                   "allow unicode user names", "move search to the new ranker", "compress archived logs",
                   "split the monolith's auth module", "pin the base image", "enable read replicas",
                   "drop the nightly full reindex", "sign release artifacts", "gate deploys on the canary",
                   "shorten the session timeout"]


# --- the history, as data ------------------------------------------------------------------------------------------

def draw_history(rng: random.Random, size: str) -> Dict[str, object]:
    """One candidate history of `size` (SIZES): everything a rendering states, nothing derived."""
    n_grounds, n_checks, n_decisions = SIZES[size]
    pool = [(pat.format(w), why) for pat, words, why in GROUND_KINDS for w in words]
    grounds = [{"id": f"G{i + 1}", "name": n, "text": why, "by": rng.choice(MEMBERS)}
               for i, (n, why) in enumerate(rng.sample(pool, n_grounds))]
    gids = [g["id"] for g in grounds]
    checks = [{"id": f"K{i + 1}", "name": n, "rests": sorted(rng.sample(gids, rng.choice((1, 2))), key=_num),
               "by": rng.choice(MEMBERS)} for i, n in enumerate(rng.sample(CHECK_NAMES, n_checks))]
    kids = [k["id"] for k in checks]
    decisions, approvals = [], []
    for i, title in enumerate(rng.sample(DECISION_TITLES, n_decisions)):
        did = f"D{i + 1:02d}"
        own = sorted(rng.sample(kids, rng.choice((1, 2))), key=_num)
        decisions.append({"id": did, "title": title, "rests": own, "by": rng.choice(MEMBERS)})
        for m in sorted(rng.sample(MEMBERS, rng.choice((2, 3)))):
            relied = set()
            for _ in range(rng.choice((1, 2))):
                relied.add(rng.choice(own) if rng.random() < 0.5 else rng.choice(kids))
            approvals.append({"decision": did, "by": m, "relies": sorted(relied, key=_num)})
    dependents = {g: sum(g in k["rests"] for k in checks) for g in gids}
    failed = rng.choice(sorted((g for g in gids if dependents[g] >= 2), key=_num) or gids)
    return {"size": size, "grounds": grounds, "checks": checks, "decisions": decisions, "approvals": approvals,
            "failed": failed}


def _num(label: str) -> int:
    return int(label[1:])


def closure_truth(h: Dict[str, object]) -> Dict[str, str]:
    """Which decisions are still in force after the failure, by the rules as PREREG.md states them, computed over the
    history's data with no VARS-1 code: what rests on the failed ground (through checks) falls; an approval counts
    while every check it relies on stands; a decision is in force while its checks stand and two approvals count."""
    fallen_checks = {k["id"] for k in h["checks"] if h["failed"] in k["rests"]}
    out = {}
    for d in h["decisions"]:
        if set(d["rests"]) & fallen_checks:
            out[d["id"]] = DROP
            continue
        counted = {a["by"] for a in h["approvals"] if a["decision"] == d["id"] and not set(a["relies"]) & fallen_checks}
        out[d["id"]] = RELY if len(counted) >= THRESHOLD else DROP
    return out


def kinds(h: Dict[str, object]) -> Dict[str, str]:
    """Each decision's case: `own` (one of its checks fell), `approvals` (its checks stand, too few approvals do),
    `margin` (in force with an approval lost), `untouched`."""
    fallen = {k["id"] for k in h["checks"] if h["failed"] in k["rests"]}
    out = {}
    for d in h["decisions"]:
        mine = [a for a in h["approvals"] if a["decision"] == d["id"]]
        lost = [a for a in mine if set(a["relies"]) & fallen]
        if set(d["rests"]) & fallen:
            out[d["id"]] = "own"
        elif len(mine) - len(lost) < THRESHOLD:
            out[d["id"]] = "approvals"
        else:
            out[d["id"]] = "margin" if lost else "untouched"
    return out


def accept(h: Dict[str, object]) -> bool:
    """The frozen constraints (PREREG.md, Histories): every case occurs, and both answers are common."""
    k = list(kinds(h).values())
    t = list(closure_truth(h).values())
    low, high, keep = BOUNDS[h["size"]]
    return all(c in k for c in ("own", "approvals", "margin")) and low <= t.count(DROP) <= high and t.count(RELY) >= keep


def history(seed: bytes, size: str) -> Dict[str, object]:
    rng = random.Random(seed)
    for _ in range(10_000):
        h = draw_history(rng, size)
        if accept(h):
            return h
    raise SystemExit("no history met the constraints")


# --- the history, as a VARS-1 chain --------------------------------------------------------------------------------

def _key(seed: bytes, member: str) -> bytes:
    return hashlib.sha256(seed + b"/" + member.encode()).digest()


def build_chain(h: Dict[str, object], seed: bytes, repo_dir: Path) -> Dict[str, object]:
    """The history admitted through the gate, one commit per event, each cell sealed by its maintainer, up to the
    failure: the notice that invalidates the ground is the caller's to admit, sealed by `reporter`."""
    subprocess.run(["git", "init", "-q", str(repo_dir)], check=True)
    for k, v in (("user.name", "g6"), ("user.email", "g6@pilot.local"), ("gc.auto", "0")):
        subprocess.run(["git", "-C", str(repo_dir), "config", k, v], check=True)
    repo = V.GitVarsRepo(repo_dir)
    sk = {m: _key(seed, m) for m in MEMBERS}
    pk = {m: V.ed25519_pubkey(s) for m, s in sk.items()}

    def put(atoms, raw):
        atoms[V.sha256(raw)] = raw
        return V.sha256(raw)
    hv = lambda atoms, ids: put(atoms, V.atom_hvec(sorted(ids)))
    pol = lambda atoms, thr: put(atoms, V.atom_pol1(thr, hv(atoms, list(pk.values()))))

    atoms = dict(V.STD_SCHEMA_ATOMS)
    admit = pol(atoms, 1)
    scope = V.Cell(h_schema=V.H_SCHEMA["scope"], h_slot_name=put(atoms, V.atom_utf8(f"{SCOPE}/SCOPE")),
                   h_payload=put(atoms, V.atom_utf8(SCOPE)), slots=(admit, admit, V.H_LENS_KERNEL))
    tip = repo.build_candidate_commit(SCOPE, atoms, [*V.STD_SCHEMAS.values(), scope],
                                      [V.Seal.sign(sk["ana"], scope.id, scope.id)], parent_commit=None)
    repo.admit_and_advance(SCOPE, tip, expected_old=None)
    s = scope.id
    ids: Dict[str, bytes] = {}
    by: Dict[bytes, str] = {}
    order: List[bytes] = []

    def commit(atoms, cells):
        nonlocal tip
        c = repo.build_candidate_commit(SCOPE, atoms, cells, [V.Seal.sign(sk[by[x.id]], x.id, s) for x in cells],
                                        parent_commit=tip)
        repo.admit_and_advance(SCOPE, c, expected_old=tip)
        tip = c
        order.extend(x.id for x in cells)

    def axiom(atoms, label, name, text, member, relies=()):
        c = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=put(atoms, V.atom_utf8(f"{SCOPE}/{name}")),
                   h_payload=put(atoms, V.atom_utf8(text)),
                   **({"h_relies": hv(atoms, [ids[r] for r in relies])} if relies else {}))
        ids[label], by[c.id] = c.id, member
        return c

    a: Dict[bytes, bytes] = {}
    commit(a, [axiom(a, g["id"], f"ground/{g['id']}", f"{g['name']}: {g['text']}", g["by"]) for g in h["grounds"]])
    a = {}
    commit(a, [axiom(a, k["id"], f"check/{k['id']}", f"`{k['name']}` passed", k["by"], k["rests"]) for k in h["checks"]])
    for d in h["decisions"]:
        a = {}
        dec = V.Cell(h_schema=V.H_SCHEMA["decision"], h_slot_name=put(a, V.atom_utf8(f"{SCOPE}/decision/{d['id']}")),
                     h_payload=put(a, V.atom_utf8(f"{d['id']}: {d['title']}")),
                     h_relies=hv(a, [ids[k] for k in d["rests"]]),
                     slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, pol(a, THRESHOLD)))
        ids[d["id"]], by[dec.id] = dec.id, d["by"]
        cells = [dec]
        for x in (x for x in h["approvals"] if x["decision"] == d["id"]):
            v = V.Cell(h_schema=V.H_SCHEMA["verdict"],
                       h_slot_name=put(a, V.atom_utf8(f"{SCOPE}/decision/{d['id']}/approved-by-{x['by']}")),
                       h_payload=dec.id, h_attests=hv(a, [dec.id]), h_relies=hv(a, [ids[k] for k in x["relies"]]),
                       slots=(V.H_EMPTY, V.H_ATTESTED, put(a, V.atom_utf8(x["by"]))))
            ids[f"{d['id']}/{x['by']}"], by[v.id] = v.id, x["by"]
            cells.append(v)
        commit(a, cells)
    lens = repo.lens(SCOPE)
    if not all(lens["settled"].get(ids[d["id"]]) for d in h["decisions"]):
        raise SystemExit("a decision is not in force before the failure")
    reporter = next(m for m in MEMBERS if m != next(g["by"] for g in h["grounds"] if g["id"] == h["failed"]))
    return {"repo": repo, "ids": ids, "by": by, "order": order, "lens": lens, "reporter": reporter}


def seeds(seed: str, count: int) -> List[Tuple[bytes, str]]:
    """The i-th history's seed and size: sizes alternate, S first."""
    return [(hashlib.sha256(f"g6/{seed}/{i}".encode()).digest(), "SL"[i % 2]) for i in range(count)]
