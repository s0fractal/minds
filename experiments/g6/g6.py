"""G6 pilot (PREREG.md): does a reader given a minds chain decide what it may still rely on after a ground fails with
fewer wrong reliances than a reader given the same evidence as pull requests and Markdown?

One history is a project kept by three maintainers: grounds, checks resting on grounds, decisions resting on checks,
and approvals, each relying on the checks its maintainer ran. A decision is in force with two approvals that stand.
Then one ground is found invalid. The history is built as a real VARS-1 chain (vars1.py, the v1 rules), and its
answer, which decisions are still in force, is computed twice: by the chain's own `what_if` and by a closure over
the history's data that shares no code with it. Generation refuses a history on which the two disagree.

Each history is rendered three ways from one set of facts: M (pull requests and Markdown), C (the chain's cells), and
W (the chain's cells and the `what_if` report). Every reader gets the same instructions, rules and question; only
the evidence differs.

    python experiments/g6/g6.py generate --seed SEED --count N --out DIR
    python experiments/g6/g6.py run --tasks DIR --out DIR [--models FILE] [--budget USD]
    python experiments/g6/g6.py score --tasks DIR --results DIR
"""
import argparse
import hashlib
import json
import os
import random
import re
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import vars1 as V  # noqa: E402

SCOPE = "proj"
MEMBERS = ("ana", "bo", "cy")
THRESHOLD = 2
SIZES = {"S": (7, 14, 12), "L": (10, 24, 30)}  # grounds, checks, decisions
BOUNDS = {"S": (3, 8, 3), "L": (5, 20, 5)}  # fewest and most decisions no longer in force; fewest still in force
ARMS = ("M", "C", "W")
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
    """The history admitted through the gate, one commit per event, each cell sealed by its maintainer; then the
    failure asked of `what_if` as a notice that invalidates the ground, sealed by the maintainer who reports it."""
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
    a = {}
    notice = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=put(a, V.atom_utf8(f"{SCOPE}/notice/{h['failed']}")),
                    h_payload=put(a, V.atom_utf8(f"{h['failed']} was found invalid")),
                    h_invalidates=hv(a, [ids[h["failed"]]]))
    report = repo.what_if(SCOPE, a, [notice], [V.Seal.sign(sk[reporter], notice.id, s)])
    return {"repo": repo, "ids": ids, "by": by, "order": order, "lens": lens, "notice": notice,
            "reporter": reporter, "report": report}


def whatif_truth(h: Dict[str, object], chain: Dict[str, object]) -> Dict[str, str]:
    """The chain's own answer: a decision is no longer in force when `what_if` lists it as lost."""
    lost = {x["name"] for x in chain["report"]["lost"]}
    return {d["id"]: DROP if f"{SCOPE}/decision/{d['id']}" in lost else RELY for d in h["decisions"]}


# --- three renderings of one set of facts --------------------------------------------------------------------------

RULES = """The project's rules:
- A ground is something recorded as established, such as a dataset's checksum or a toolchain's build.
- A check rests on one or more grounds. It stands only while every ground it rests on stands.
- A decision rests on one or more checks. Each maintainer may approve a decision; an approval relies on the checks
  that maintainer ran.
- An approval counts only while every check it relies on stands.
- A decision is in force while every check it rests on stands and approvals from at least two different maintainers
  count."""

QUESTION = """Before the notice at the end of the record, all {n} decisions {first} to {last} were in force. Then one
ground was found invalid.

Question: for each decision, may the project still rely on it being in force? Answer RELY or DO_NOT_RELY for each.

You may reason first. End your reply with one fenced JSON block (```json ... ```) holding one object that maps each
of {first} to {last} to "RELY" or "DO_NOT_RELY", and nothing else."""


def _ground(h, gid):
    return next(g for g in h["grounds"] if g["id"] == gid)


def _check(h, kid):
    return next(k for k in h["checks"] if k["id"] == kid)


def render_markdown(h: Dict[str, object]) -> str:
    """M: the repository as pull requests, CI records and Markdown files; every fact of the history, none derived."""
    ref = lambda kid: f"{kid} `{_check(h, kid)['name']}`"
    out = ["The project's repository: its Markdown files, CI history, pull requests and issues.", "",
           "### docs/GROUNDS.md", "", "| ground | recorded by | what was established |", "|---|---|---|"]
    out += [f"| {g['id']} {g['name']} | {g['by']} | {g['text']} |" for g in h["grounds"]]
    out += ["", "### docs/CHECKS.md (from the CI history)", "", "| check | run by | result | rests on grounds |",
            "|---|---|---|---|"]
    out += [f"| {ref(k['id'])} | {k['by']} | passed | {', '.join(k['rests'])} |" for k in h["checks"]]
    for i, d in enumerate(h["decisions"]):
        out += ["", f"### Pull request #{101 + i}: {d['id']} {d['title']} (merged)", "", f"Opened by {d['by']}.",
                f"Rests on checks: {', '.join(ref(k) for k in d['rests'])}.", "", "Reviews:"]
        out += [f"- {a['by']} approved: \"I ran {' and '.join(ref(k) for k in a['relies'])}; approving.\""
                for a in h["approvals"] if a["decision"] == d["id"]]
    g = _ground(h, h["failed"])
    out += ["", f"### Issue #{101 + len(h['decisions'])}: {g['id']} {g['name']} is invalid", "",
            f"Opened by {_reporter(h)}: \"{g['id']} was found invalid.\""]
    return "\n".join(out)


def _reporter(h):
    return next(m for m in MEMBERS if m != _ground(h, h["failed"])["by"])


def _short(cid: bytes) -> str:
    return cid.hex()[:12]


def _cells(h, chain) -> List[Dict[str, object]]:
    repo, ids = chain["repo"], chain["ids"]
    lens = chain["lens"]
    cells, atoms = lens["cells"], lens["atoms"]
    name = {v: k for k, v in ids.items()}
    rows = []
    for cid in chain["order"]:
        c = cells[cid]
        row = {"id": _short(cid), "schema": "axiom" if c.h_schema == V.H_SCHEMA["axiom"] else
               "decision" if c.h_schema == V.H_SCHEMA["decision"] else "verdict",
               "name": V.parse_utf8(atoms[c.h_slot_name])}
        if c.h_schema == V.H_SCHEMA["verdict"]:
            row["attests"] = [_short(x) for x in V.parse_hvec(atoms[c.h_attests])]
            row["verdict"] = "ATTESTED"
        else:
            row["payload"] = V.parse_utf8(atoms[c.h_payload])
        row["relies_on"] = [] if c.h_relies == V.H_EMPTY else [_short(x) for x in V.parse_hvec(atoms[c.h_relies])]
        if c.h_schema == V.H_SCHEMA["decision"]:
            row["evaluators"] = f"{THRESHOLD} of {', '.join(MEMBERS)}"
        row["sealed_by"] = chain["by"][cid]
        rows.append(row)
        assert cid in name
    n = chain["notice"]
    rows.append({"id": _short(n.id), "schema": "axiom", "name": f"{SCOPE}/notice/{h['failed']}",
                 "payload": f"{h['failed']} was found invalid", "invalidates": [_short(ids[h["failed"]])],
                 "relies_on": [], "sealed_by": chain["reporter"]})
    return rows


CHAIN_LEGEND = """The project's minds chain (refs/vars/heads/proj): every cell it holds, in the order admitted, each
sealed by the maintainer named. Cells refer to each other by id (the first 12 hex digits of the cell's hash). An axiom
is a ground or a check; `relies_on` lists the cells it rests on. A decision lists the checks it rests on in
`relies_on`; its evaluators are 2 of ana, bo, cy. A verdict is an approval: it `attests` the decision it approves and
`relies_on` the checks its maintainer ran. The last cell is the notice: it `invalidates` the ground found invalid."""

WHATIF_LEGEND = """minds' own reading of the notice (`minds_chain.py what-if`): the gate admitted the notice on a
candidate commit and the lens was computed before and after it. `lost` lists every cell whose status changes, with
its statuses before and after and what it needs that no longer stands; `held` lists the cells near the notice that
keep their status, with a decision's counted approvals before and after. Each row's `path` runs from the notice
through the cells it depends on."""


def render_chain(h: Dict[str, object], chain: Dict[str, object]) -> str:
    """C: the chain's cells, as a reader of the chain sees them."""
    return CHAIN_LEGEND + "\n\n" + "\n".join(json.dumps(r, sort_keys=False) for r in _cells(h, chain))


def render_whatif(h: Dict[str, object], chain: Dict[str, object]) -> str:
    """W: the chain's cells and what minds computes for the notice."""
    full = {v.hex(): _short(v) for v in chain["ids"].values()}
    full[chain["notice"].id.hex()] = _short(chain["notice"].id)
    sh = lambda x: [full.get(c, c[:12]) for c in x]

    def row(x, kind):
        r = {"id": full.get(x["cell"], x["cell"][:12]), "name": x["name"], "path": sh(x["path"])}
        if kind == "lost":
            r["before"], r["after"] = x["before"], x["after"]
            needs = dict(x.get("needs", {}))
            if "grounds" in needs:
                needs["grounds"] = sh(needs["grounds"])
            if "endorsements" in needs:
                needs["endorsements"] = {k: sh(v) if isinstance(v, list) else v
                                         for k, v in needs["endorsements"].items()}
            r["needs"] = needs
        elif "endorsements" in x:
            r["endorsements"] = x["endorsements"]
        return json.dumps(r)
    rep = chain["report"]
    return (render_chain(h, chain) + "\n\n" + WHATIF_LEGEND + "\n\nlost:\n"
            + "\n".join(row(x, "lost") for x in rep["lost"]) + "\n\nheld:\n"
            + "\n".join(row(x, "held") for x in rep["held"]))


def prompt(h: Dict[str, object], evidence: str) -> str:
    ds = [d["id"] for d in h["decisions"]]
    q = QUESTION.format(n=len(ds), first=ds[0], last=ds[-1])
    return ("You are reading the record of a software project kept by three maintainers: ana, bo and cy.\n\n"
            + RULES + "\n\n<record>\n" + evidence + "\n</record>\n\n" + q)


def task(seed: bytes, size: str, work: Path) -> Dict[str, object]:
    """One history: its facts, both answers (refusing unless they agree), its cases and the three prompts."""
    h = history(seed, size)
    with tempfile.TemporaryDirectory(dir=work) as d:
        chain = build_chain(h, seed, Path(d))
        a, b = closure_truth(h), whatif_truth(h, chain)
        if a != b:
            raise SystemExit(f"the chain and the closure disagree: {sorted(x for x in a if a[x] != b[x])}")
        prompts = {"M": prompt(h, render_markdown(h)), "C": prompt(h, render_chain(h, chain)),
                   "W": prompt(h, render_whatif(h, chain))}
        digest = chain["report"]["digest"]
    return {"seed": seed.hex(), "history": h, "truth": a, "kinds": kinds(h), "whatif_digest": digest,
            "prompts": prompts}


def seeds(seed: str, count: int) -> List[Tuple[bytes, str]]:
    """The i-th history's seed and size: sizes alternate, S first."""
    return [(hashlib.sha256(f"g6/{seed}/{i}".encode()).digest(), "SL"[i % 2]) for i in range(count)]


def generate(seed: str, count: int, out: Path) -> None:
    out.mkdir(parents=True, exist_ok=False)
    work = Path.home() / "Projects" / ".worktrees" / "g6-work"
    work.mkdir(parents=True, exist_ok=True)
    manifest = {}
    for i, (s, size) in enumerate(seeds(seed, count)):
        t = task(s, size, work)
        p = out / f"h{i:02d}.json"
        p.write_text(json.dumps(t, indent=1, sort_keys=True) + "\n")
        manifest[p.name] = hashlib.sha256(p.read_bytes()).hexdigest()
    (out / "MANIFEST.json").write_text(json.dumps({"seed": seed, "count": count, "files": manifest}, indent=1) + "\n")


# --- answers -------------------------------------------------------------------------------------------------------

FENCE = re.compile(r"```json[ \t]*\n(.*?)\n[ \t]*```", re.S)


def parse_answer(text: str, items: List[str]) -> Optional[Dict[str, str]]:
    """The reply's last fenced JSON block, if it maps exactly `items` to RELY or DO_NOT_RELY; else None (invalid)."""
    blocks = FENCE.findall(text or "")
    if not blocks:
        return None
    try:
        obj = json.loads(blocks[-1])
    except ValueError:
        return None
    if not isinstance(obj, dict) or set(obj) != set(items) or any(v not in (RELY, DROP) for v in obj.values()):
        return None
    return obj


# --- running readers -----------------------------------------------------------------------------------------------

API = "https://openrouter.ai/api/v1/chat/completions"


def call(model: str, text: str, key: str, max_tokens: int) -> Dict[str, object]:
    body = json.dumps({"model": model, "messages": [{"role": "user", "content": text}], "temperature": 0,
                       "max_tokens": max_tokens, "usage": {"include": True}}).encode()
    req = urllib.request.Request(API, data=body, headers={"Authorization": f"Bearer {key}",
                                                          "Content-Type": "application/json",
                                                          "X-Title": "minds G6 pilot"})
    with urllib.request.urlopen(req, timeout=600) as r:
        return json.loads(r.read())


def plan(tasks: Dict[str, Dict[str, object]], models: List[str], order_seed: str) -> List[Tuple[str, str, str]]:
    """Every (history, model, arm) once, in an order drawn from `order_seed`, so no arm runs in a block of its own."""
    calls = [(t, m, a) for t in sorted(tasks) for m in models for a in ARMS]
    random.Random(hashlib.sha256(f"g6/order/{order_seed}".encode()).digest()).shuffle(calls)
    return calls


def run(tasks_dir: Path, out: Path, models: List[str], budget: float, max_tokens: int,
        caller=call, key: Optional[str] = None) -> Dict[str, object]:
    """Ask each reader each prompt once. A recorded reply is never asked again, so an interrupted run resumes; an
    HTTP or network failure is retried twice, then recorded as no answer. Before each call the spend so far, as
    OpenRouter reports it, must leave a quarter of a dollar under `budget`, or the run stops."""
    key = key if key is not None else os.environ.get("OPENROUTER_API_KEY", "")
    if not key and caller is call:
        raise SystemExit("set OPENROUTER_API_KEY")
    tasks = {p.stem: json.loads(p.read_text()) for p in sorted(tasks_dir.glob("h*.json"))}
    raw = out / "raw"
    raw.mkdir(parents=True, exist_ok=True)
    ledger = out / "ledger.jsonl"
    spent = sum(json.loads(x).get("cost", 0.0) for x in ledger.read_text().splitlines()) if ledger.exists() else 0.0
    manifest = json.loads((tasks_dir / "MANIFEST.json").read_text())
    stopped = None
    for t, m, a in plan(tasks, models, manifest["seed"]):
        dest = raw / f"{t}.{m.replace('/', '_')}.{a}.json"
        if dest.exists():
            continue
        if spent > budget - 0.25:
            stopped = f"budget: {spent:.4f} of {budget} spent"
            break
        rec = {"task": t, "model": m, "arm": a, "attempts": []}
        for attempt in range(3):
            t0 = time.time()
            try:
                resp = caller(m, tasks[t]["prompts"][a], key, max_tokens)
                rec["attempts"].append({"ok": True, "seconds": round(time.time() - t0, 2)})
                rec["response"] = resp
                break
            except (urllib.error.URLError, TimeoutError, ValueError, OSError) as e:
                rec["attempts"].append({"ok": False, "error": f"{type(e).__name__}: {str(e)[:300]}"})
                time.sleep(5 * (attempt + 1))
        usage = (rec.get("response") or {}).get("usage") or {}
        cost = float(usage.get("cost") or 0.0)
        spent += cost
        dest.write_text(json.dumps(rec, indent=1) + "\n")
        with ledger.open("a") as f:
            f.write(json.dumps({"task": t, "model": m, "arm": a, "cost": cost,
                                "served": (rec.get("response") or {}).get("model")}) + "\n")
    status = {"spent": round(spent, 6), "budget": budget, "stopped": stopped,
              "recorded": len(list(raw.glob("*.json"))), "planned": len(tasks) * len(models) * len(ARMS)}
    (out / "STATUS.json").write_text(json.dumps(status, indent=1) + "\n")
    return status


# --- scoring -------------------------------------------------------------------------------------------------------

def reply_text(rec: Dict[str, object]) -> Optional[str]:
    try:
        return rec["response"]["choices"][0]["message"]["content"]
    except (KeyError, IndexError, TypeError):
        return None


def rates(answer: Optional[Dict[str, str]], truth: Dict[str, str]) -> Optional[Dict[str, float]]:
    """Wrong reliance: the share of decisions no longer in force that the reader would still rely on. Over-caution:
    the share of decisions still in force that it would drop. None for an invalid reply."""
    if answer is None:
        return None
    drop = [d for d, v in truth.items() if v == DROP]
    keep = [d for d, v in truth.items() if v == RELY]
    return {"wrong_reliance": sum(answer[d] == RELY for d in drop) / len(drop),
            "over_caution": sum(answer[d] == DROP for d in keep) / len(keep)}


def sign_test(diffs: List[float]) -> Dict[str, object]:
    """Exact two-sided sign test over the nonzero paired differences."""
    pos, neg = sum(d > 0 for d in diffs), sum(d < 0 for d in diffs)
    n = pos + neg
    if n == 0:
        return {"positive": 0, "negative": 0, "ties": len(diffs), "p": 1.0}
    from math import comb
    k = min(pos, neg)
    p = min(1.0, 2 * sum(comb(n, i) for i in range(k + 1)) / 2 ** n)
    return {"positive": pos, "negative": neg, "ties": len(diffs) - n, "p": p}


def contrast(cells: Dict[Tuple[str, str, str], Optional[Dict[str, float]]], arm: str, metric: str,
             invalid_as_worst: bool = False) -> Dict[str, object]:
    """Paired over (history, model): M's rate minus `arm`'s. A positive mean is fewer errors under `arm`. A pair with an
    invalid reply in either arm is left out, or with `invalid_as_worst` counts that reply as wrong on every item."""
    worst = {"wrong_reliance": 1.0, "over_caution": 1.0}
    diffs = []
    pairs = sorted({(t, m) for t, m, _ in cells})
    for t, m in pairs:
        x, y = cells.get((t, m, "M")), cells.get((t, m, arm))
        if invalid_as_worst:
            x, y = x or worst, y or worst
        if x is None or y is None:
            continue
        diffs.append(x[metric] - y[metric])
    mean = sum(diffs) / len(diffs) if diffs else None
    st = sign_test(diffs)
    verdict = "no difference detected"
    if mean is not None and st["p"] < 0.05:
        verdict = f"{arm} lowers it" if mean > 0 else f"{arm} raises it"
    return {"arm": arm, "metric": metric, "pairs": len(diffs), "mean_difference": mean, **st, "verdict": verdict}


def score(tasks_dir: Path, results: Path) -> Dict[str, object]:
    tasks = {p.stem: json.loads(p.read_text()) for p in sorted(tasks_dir.glob("h*.json"))}
    cells: Dict[Tuple[str, str, str], Optional[Dict[str, float]]] = {}
    by_kind: Dict[Tuple[str, str], List[int]] = {}
    invalid: Dict[str, int] = {a: 0 for a in ARMS}
    for p in sorted((results / "raw").glob("*.json")):
        rec = json.loads(p.read_text())
        t, m, a = rec["task"], rec["model"], rec["arm"]
        truth = tasks[t]["truth"]
        ans = parse_answer(reply_text(rec), sorted(truth))
        cells[(t, m, a)] = rates(ans, truth)
        if ans is None:
            invalid[a] += 1
            continue
        for d, k in tasks[t]["kinds"].items():
            by_kind.setdefault((a, k), []).append(int(ans[d] == truth[d]))
    per, per_size = {}, {}
    for (t, m, a), r in cells.items():
        if r is not None:
            per.setdefault(f"{m} {a}", []).append(r)
            per_size.setdefault(f"{tasks[t]['history']['size']} {a}", []).append(r)
    mean = lambda groups: {k: {met: sum(r[met] for r in v) / len(v) for met in ("wrong_reliance", "over_caution")}
                           | {"n": len(v)} for k, v in sorted(groups.items())}
    return {
        "primary": contrast(cells, "W", "wrong_reliance"),
        "secondary": [contrast(cells, "C", "wrong_reliance"), contrast(cells, "W", "over_caution"),
                      contrast(cells, "C", "over_caution")],
        "sensitivity": [contrast(cells, "W", "wrong_reliance", True), contrast(cells, "C", "wrong_reliance", True)],
        "invalid": invalid,
        "accuracy_by_case": {f"{a} {k}": round(sum(v) / len(v), 4) for (a, k), v in sorted(by_kind.items())},
        "per_model_arm": mean(per),
        "per_size_arm": mean(per_size),
    }


def main(argv: List[str]) -> int:
    ap = argparse.ArgumentParser(prog="g6")
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("generate")
    g.add_argument("--seed", required=True)
    g.add_argument("--count", type=int, required=True)
    g.add_argument("--out", type=Path, required=True)
    r = sub.add_parser("run")
    r.add_argument("--tasks", type=Path, required=True)
    r.add_argument("--out", type=Path, required=True)
    r.add_argument("--models", type=Path, default=Path(__file__).with_name("models.json"))
    r.add_argument("--budget", type=float, default=5.0)
    r.add_argument("--max-tokens", type=int, default=8000)
    s = sub.add_parser("score")
    s.add_argument("--tasks", type=Path, required=True)
    s.add_argument("--results", type=Path, required=True)
    a = ap.parse_args(argv)
    if a.cmd == "generate":
        generate(a.seed, a.count, a.out)
    elif a.cmd == "run":
        print(json.dumps(run(a.tasks, a.out, json.loads(a.models.read_text())["models"], a.budget, a.max_tokens),
                         indent=1))
    else:
        print(json.dumps(score(a.tasks, a.results), indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
