#!/usr/bin/env python3
"""minds governs itself with VARS-1: the chain `refs/vars/heads/minds` in this repository.

Each release of `main` is a `decision` cell stating what was released (commit, rules kernel) and which checks
passed, attested by the maintainer's verdict, together with a projection of the chain for clients without the
repository. The maintainer key lives in `.git/vars/maintainer.key` (never committed or pushed); the scope's roster
is that key until `join` adds others. With more than one key, every release needs a verdict and a projection seal
from every key on the roster: another member runs `verify-release`, which reruns the checks on the released commit
in its own worktree and records that member's verdict.

Run it with the interpreter that has requirements.txt installed (`.venv/bin/python tools/minds_chain.py ...`):
the checks run the test suites with that same interpreter.

    tools/minds_chain.py init                 # genesis of refs/vars/heads/minds (once)
    tools/minds_chain.py release              # with HEAD = main and a clean tree, run every check on main in a
                                              # fresh worktree, then record main
    tools/minds_chain.py join PUBKEY NAME     # rotate the roster to add a member's Ed25519 public key (hex)
    tools/minds_chain.py verify-release DECISION --key FILE --name NAME
                                              # as a member: rerun the checks at the release's commit, record a
                                              # verdict, and witness the projections that name your key
    tools/minds_chain.py show                 # releases and projections with their status
    tools/minds_chain.py status               # read only: is main released, who has not yet attested each
                                              # release or witnessed each projection, rules, claims debt
    tools/minds_chain.py profile COMMIT       # the release profile of COMMIT: every file an admission depends on
    tools/minds_chain.py bundle PROJECTION    # a projection bundle for `vars1.py verify-projection`
    tools/minds_chain.py attest DECISION      # an attestation bundle for `vars1.py verify-attestation`
    tools/minds_chain.py shadow RULES [--out FILE]
                                              # every historical tip under its epoch's rules and under RULES: the
                                              # manifest of every difference (commit, cell, bit, old, new)
    tools/minds_chain.py change-rules CLASS RULES --manifest FILE [--accept DIGEST]
                [--input FILE --budget N --refusal N]                       (hardening, tightening)
                [--counterexample-scope S --counterexample C --cell I --status B --right R]   (correction)
                                              # rotate to RULES with a rules-change decision (VARS-1-SPEC.md §4.3),
                                              # only if FILE is the shadow replay of the chain now
    tools/minds_chain.py evidence             # what each past rules change needs to replay (AMENDMENTS.md)
    tools/minds_chain.py replay-changes       # replay each past rules change with a fresh gate
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
import vars1 as V  # noqa: E402

SCOPE = "minds"
SIBLINGS = ("sigma-glyph", "primitives")
SIGMA_PIN = "c864d3ee01a2fe46c528bd6e9552438e64df5f6b"  # VARS-1-SPEC.md `c864d3e`: Book I as the spec depends on it
BOOK_I = ("impl/sigma_resume.py", "proofs")


def key_path(repo_dir: Path) -> Path:
    return Path(repo_dir) / ".git" / "vars" / "maintainer.key"


def load_or_create_key(repo_dir: Path) -> bytes:
    """The maintainer's Ed25519 seed, created on first use (mode 0600, inside .git, never tracked)."""
    p = key_path(repo_dir)
    if not p.exists():
        p.parent.mkdir(parents=True, exist_ok=True)
        fd = os.open(p, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, "w") as f:
            f.write(os.urandom(32).hex())
    return bytes.fromhex(p.read_text().strip())


def _put(atoms: Dict[bytes, bytes], raw: bytes) -> bytes:
    h = V.sha256(raw)
    atoms[h] = raw
    return h


def _policy(atoms: Dict[bytes, bytes], thr: int, keys: List[bytes]) -> bytes:
    return _put(atoms, V.atom_pol1(thr, _put(atoms, V.atom_hvec(sorted(set(keys))))))


def _maintainer_policy(atoms: Dict[bytes, bytes], sk: bytes) -> bytes:
    return _policy(atoms, 1, [V.ed25519_pubkey(sk)])


def init(repo_dir: Path, sk: bytes) -> str:
    """Genesis: one scope cell `minds/SCOPE` whose admission and acceptance policy is 1-of-{maintainer}."""
    repo = V.GitVarsRepo(repo_dir)
    if repo.ref_commit(SCOPE) is not None:
        raise V.VarsError("refs/vars/heads/minds already exists")
    atoms = dict(V.STD_SCHEMA_ATOMS)
    pol = _maintainer_policy(atoms, sk)
    scope = V.Cell(
        h_schema=V.H_SCHEMA["scope"],
        h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/SCOPE")),
        h_payload=_put(atoms, V.atom_utf8(SCOPE)),
        slots=(pol, pol, V.H_LENS_KERNEL),
    )
    c = repo.build_candidate_commit(SCOPE, atoms, [*V.STD_SCHEMAS.values(), scope],
                                    [V.Seal.sign(sk, scope.id, scope.id)], parent_commit=None)
    repo.admit_and_advance(SCOPE, c, expected_old=None)
    return c


def governing_scope(repo: V.GitVarsRepo) -> bytes:
    return repo._evaluate_commit_chain(SCOPE, repo.commit_chain(repo.ref_commit(SCOPE)))["active_scope_id"]


def governing_rules(repo: V.GitVarsRepo) -> bytes:
    """The rules the governing scope names. A membership rotation or a release keeps them; changing them is its own
    operation, a rotation with a rules-change decision (VARS-1-SPEC.md §4.3), never a side effect of either."""
    atoms, cells, _ = repo.read_cas_tree(repo.ref_commit(SCOPE))
    return cells[governing_scope(repo)].slots[2]


def roster(repo: V.GitVarsRepo) -> List[bytes]:
    """The keys of the governing scope's admission policy."""
    atoms, cells, _ = repo.read_cas_tree(repo.ref_commit(SCOPE))
    _, hv = V.parse_pol1(atoms[cells[governing_scope(repo)].slots[0]])
    return V.parse_hvec(atoms[hv], require_sorted=True)


def join(repo_dir: Path, sk: bytes, pubkey: bytes, name: str) -> str:
    """Rotate the scope so the roster is the current one plus `pubkey`. Any member may then admit cells (1-of-n);
    releases are settled only by all of them (see `release`)."""
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    s = governing_scope(repo)
    keys = roster(repo)
    if pubkey in keys:
        raise V.VarsError("already a member")
    if V.weak_public_key(pubkey):
        raise V.VarsError("weak public key")
    keys = sorted(keys + [pubkey])
    atoms: Dict[bytes, bytes] = {}
    pol = _policy(atoms, 1, keys)
    scope = V.Cell(
        h_schema=V.H_SCHEMA["scope"],
        h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/SCOPE")),
        h_payload=_put(atoms, V.atom_utf8(f"{SCOPE} roster of {len(keys)}: {name} joins")),
        h_supersedes=_put(atoms, V.atom_hvec([s])),
        h_loss=_put(atoms, V.atom_utf8(f"rotation: {name} joins")),
        slots=(pol, pol, governing_rules(repo)),
    )
    c = repo.build_candidate_commit(SCOPE, atoms, [scope], [V.Seal.sign(sk, scope.id, s)], parent_commit=tip)
    repo.admit_and_advance(SCOPE, c, expected_old=tip)
    return c


def _rules_read(repo: V.GitVarsRepo, scope: str, commit: str, rules: bytes) -> Tuple[str, object]:
    """`rules` over the chain up to `commit`: ("output", its reading) or ("refusal", "E<code>")."""
    try:
        return "output", repo.rules_output(scope, commit, rules)[1]
    except V.KernelRefusal as e:
        return "refusal", f"E{e.code}"


def _digest(doc: Dict[str, object]) -> str:
    return V.sha256(json.dumps(doc, sort_keys=True, separators=(",", ":")).encode()).hex()


def shadow(repo_dir: Path, new_rules: bytes, scope: str = SCOPE) -> Dict[str, object]:
    """Shadow replay before a rules change (VARS-1-SPEC.md §4.3): at every historical tip of the chain, the rules of
    that tip's epoch and `new_rules`, compared bit by bit. The manifest lists every difference as
    `{commit, cell, bit, old, new}`: a status bit (`accepted` ... `stale`), `authorized` (a cell's latch, or an edge's,
    whose `cell` is `<w>><v>:<kind>`), `governing` (the scope cell, `cell` "-") or `result` (output or a refusal,
    `cell` "-"). `digest` is SHA-256 over the canonical JSON of the rest."""
    repo = V.GitVarsRepo(repo_dir)
    chain = repo.commit_chain(repo.ref_commit(scope))
    epochs = V.commit_rules(scope, repo.chain_deltas(chain))
    rows: List[Dict[str, object]] = []
    for commit, old_rules in zip(chain, epochs):
        (ok, o), (nk, n) = _rules_read(repo, scope, commit, old_rules), _rules_read(repo, scope, commit, new_rules)
        if (ok, nk) != ("output", "output"):
            if (ok, o) != (nk, n):
                rows.append({"commit": commit, "cell": "-", "bit": "result",
                             "old": o if ok == "refusal" else "output", "new": n if nk == "refusal" else "output"})
            continue
        if o["scope"] != n["scope"]:
            rows.append({"commit": commit, "cell": "-", "bit": "governing", "old": o["scope"].hex(), "new": n["scope"].hex()})
        for cid in sorted(o["status"]):
            for b, name in enumerate(V.KERNEL_BITS):
                ob, nb = o["status"][cid] >> b & 1, n["status"].get(cid, 0) >> b & 1
                if ob != nb:
                    rows.append({"commit": commit, "cell": cid.hex(), "bit": name, "old": ob, "new": nb})
            if bool(o["auth"][cid]) != bool(n["auth"].get(cid, 0)):
                rows.append({"commit": commit, "cell": cid.hex(), "bit": "authorized", "old": o["auth"][cid],
                             "new": n["auth"].get(cid, 0)})
        for (w, v, kind) in sorted(o["edges"]):
            if bool(o["edges"][(w, v, kind)]) != bool(n["edges"].get((w, v, kind), 0)):
                rows.append({"commit": commit, "cell": f"{w.hex()}>{v.hex()}:{kind}", "bit": "authorized",
                             "old": o["edges"][(w, v, kind)], "new": n["edges"].get((w, v, kind), 0)})
    doc: Dict[str, object] = {"scope": scope, "tip": chain[-1], "tips": len(chain), "new_rules": new_rules.hex(),
                              "differences": rows}
    return {**doc, "digest": _digest(doc)}


def change_rules(repo_dir: Path, sk: bytes, kind: str, new_rules: bytes, manifest: Dict[str, object],
                 accept: Optional[str] = None, **fields: object) -> str:
    """Record a rotation of the scope to `new_rules` with a rules-change decision of class `kind` (§4.3), only after
    the shadow replay: `manifest` must be `shadow`'s replay of this chain now. A hardening or an equivalent change
    must leave every historical tip as it was; a correction or a tightening may change some, and is recorded only
    with `accept` equal to the manifest's digest. `fields`: for a correction `counterexample_scope`,
    `counterexample`, `cell`, `status`, `right`; for a hardening or a tightening `input` (bytes), `budget`,
    `refusal` (the code, negated). The gate then replays the decision's own computations."""
    if manifest != shadow(repo_dir, new_rules):
        raise V.VarsError("the shadow manifest is not this chain's replay under those rules now: run `shadow` again")
    if manifest["differences"]:
        if kind in ("hardening", "equivalent"):
            raise V.VarsError(f"{'an' if kind == 'equivalent' else 'a'} {kind} change must leave every historical tip "
                              f"as it was: the shadow manifest lists "
                              f"{len(manifest['differences'])} differences")
        if accept != manifest["digest"]:
            raise V.VarsError("the shadow manifest lists differences: record the change only with --accept <its digest>")
    repo = V.GitVarsRepo(repo_dir)
    tip = str(manifest["tip"])  # the chain the manifest replayed; the CAS below refuses if the ref has moved since
    if repo.ref_commit(SCOPE) != tip:
        raise V.VarsError("the chain moved after its shadow replay: run `shadow` again")
    base_id = repo._evaluate_commit_chain(SCOPE, repo.commit_chain(tip))["active_scope_id"]
    base = repo.read_cas_tree(tip)[1][base_id]
    atoms: Dict[bytes, bytes] = {new_rules: V.RULES_ATOMS[new_rules]}
    put = lambda raw: _put(atoms, raw)  # noqa: E731
    schema, schema_atoms = V.rules_change_schema(SCOPE, kind)
    atoms.update(schema_atoms)
    vals: Dict[str, bytes] = {"old_rules": base.slots[2], "new_rules": new_rules, "basis": put(V.atom_utf8(tip))}
    if kind == "correction":
        cx_scope, cx = str(fields["counterexample_scope"]), str(fields["counterexample"])
        ev = repo.rules_change_evidence(SCOPE, tip, base.slots[2], new_rules, cx_scope, cx)
        vals.update(reproduce=ev["reproduce"], counterexample_scope=put(V.atom_utf8(cx_scope)),
                    counterexample=put(V.atom_utf8(cx)), refutes=ev["refutes"], latches=ev["latches"],
                    **{k: put(V.atom_u64(int(fields[k]))) for k in ("cell", "status", "right")})
    else:
        vals["reproduce"] = repo.rules_change_basis(SCOPE, tip, base.slots[2], new_rules)["reproduce"]
        if kind != "equivalent":
            inp, budget = bytes(fields["input"]), int(fields["budget"])
            vals.update(input=put(V.atom_kin1(inp)), budget=put(V.atom_u64(budget)),
                        refusal=put(V.atom_u64(int(fields["refusal"]))),
                        refutes=repo.rules_change_refusal(base.slots[2], new_rules, inp, budget)["refutes"])
    names = [f.split(":")[0] for f in V.RULES_CHANGE_CLASSES[kind][1]]
    decision = V.Cell(schema.id, put(V.atom_utf8(f"{SCOPE}/rules-change/{tip}")),  # one name per basis: unique
                      put(V.atom_utf8(f"{SCOPE} moves to rules {new_rules.hex()} ({kind}); shadow manifest "
                                      f"{manifest['digest']}, {len(manifest['differences'])} differences")),
                      slots=tuple(vals[n] for n in names))
    scope = V.Cell(V.H_SCHEMA["scope"], put(V.atom_utf8(f"{SCOPE}/SCOPE")),
                   put(V.atom_utf8(f"{SCOPE} under rules {new_rules.hex()[:12]}")), h_supersedes=put(V.atom_hvec([base_id])),
                   h_loss=put(V.atom_utf8(f"rules change ({kind})")), slots=(base.slots[0], base.slots[1], new_rules))
    cells = [schema, decision, scope]
    c = repo.build_candidate_commit(SCOPE, atoms, cells, [V.Seal.sign(sk, x.id, base_id) for x in cells],
                                    parent_commit=tip)
    repo.admit_and_advance(SCOPE, c, expected_old=tip)
    return c


def evidence(repo_dir: Path, scope: str = SCOPE) -> Dict[str, object]:
    """The evidence manifest of every rules change on the chain (§4.3): for each decision, its rotation commit, class,
    rules, basis, and what its replay needs beyond the chain: a counterexample chain and every counterexample its own
    corrections name, transitively, each reachable from `refs/vars/evidence/<scope>/<decision>/<commit>`, or an input
    carried in the chain as a KIN1 atom. Every rules module it
    names is carried in the chain as an atom too (`in_chain`). `package` is SHA-256 over the canonical JSON of the
    items: what a fresh clone needs, by name, to replay each change (`replay_changes`)."""
    repo = V.GitVarsRepo(repo_dir)
    chain = repo.commit_chain(repo.ref_commit(scope))
    items: List[Dict[str, object]] = []
    atoms: Dict[bytes, bytes] = {}
    for commit, (d_atoms, d_cells, _) in zip(chain, repo.chain_deltas(chain)):
        atoms.update(d_atoms)
        for cid in sorted(d_cells):
            kind = V.rules_change_class(scope, d_cells[cid].h_schema)
            if kind is None:
                continue
            f = dict(zip((x.split(":")[0] for x in V.RULES_CHANGE_CLASSES[kind][1]), d_cells[cid].slots))
            item: Dict[str, object] = {"decision": cid.hex(), "commit": commit, "class": kind,
                                       "old_rules": f["old_rules"].hex(), "new_rules": f["new_rules"].hex(),
                                       "in_chain": sorted(h.hex() for h in (f["old_rules"], f["new_rules"]) if h in atoms),
                                       "basis": V.parse_utf8(atoms[f["basis"]])}
            if kind == "correction":
                cx = (V.parse_utf8(atoms[f["counterexample_scope"]]), V.parse_utf8(atoms[f["counterexample"]]))
                item["counterexample"] = {"scope": cx[0], "commit": cx[1]}
                try:
                    need = [cx] + repo.evidence_closure(*cx)
                except V.VarsError:
                    need = [cx]  # what this node lacks is reported by the replay; the manifest names what is known
                item["needs"] = [{"scope": sc, "commit": c, "ref": f"refs/vars/evidence/{scope}/{cid.hex()}/{c}"}
                                 for sc, c in need]
            elif kind != "equivalent":
                item["input"] = {"atom": f["input"].hex(), "bytes": len(atoms[f["input"]]) - 4}
            items.append(item)
    return {"scope": scope, "tip": chain[-1], "changes": items, "package": _digest({"changes": items})}


def replay_changes(repo_dir: Path, scope: str = SCOPE) -> List[Tuple[str, str]]:
    """Replay every rules change of the chain with a fresh gate: `(decision, REPLAYED | EVIDENCE MISSING: ... |
    REFUSED: ...)`. Missing evidence is not a refutation: fetch `refs/vars/evidence/*` and replay again."""
    out = []
    for item in evidence(repo_dir, scope)["changes"]:
        gate = V.GitVarsRepo(repo_dir)
        try:
            gate.check_chain(scope, item["commit"])
            out.append((item["decision"], "REPLAYED"))
        except V.EvidenceMissing as e:
            out.append((item["decision"], f"EVIDENCE MISSING: {e}"))
        except V.VarsError as e:
            out.append((item["decision"], f"REFUSED: {e}"))
    return out


# What a release identifies beyond its rules hash. H_LENS_KERNEL names the fold and Passes 1–2 only; the host decides
# canonical bytes, types, replay, bindings and rules-change admission (ASSURANCE.md, "Changing the rules"), so a fix
# there changes no rules hash. The profile names the bytes of every file the released commit tracks: a list of the
# files an admission depends on would be wider than anything that can check it, because profiled code can load any
# other file (a module beside it, a package, a ZIP on its path, a file it reads), so nothing narrower is sound. It is
# not the commit id: it is SHA-256 throughout (git's object ids are SHA-1 here) and leaves out the commit's metadata,
# so two commits with the same bytes have one profile. Not named: the interpreters (Python, node, Lean, cargo),
# which come from the host.
PROFILE_FORMAT = "minds-profile/1"
# The rules modules a commit carries (by file), and of those the one the offline verifier interprets, read from its own
# bytes (minds_verify.py `H_LENS_KERNEL`; it reports every other identity unsupported). Carrying a module is not the
# gate running it: which modules the gate runs, and for which epochs, is vars1.py's `RULES`, named here by its hash.
RULES_FILES = (("kernel/lens.wasm", "v1"), ("kernel/lens1b.wasm", "v1b"), ("kernel2/lens2.wasm", "v2"))


def profile_at(repo_dir: Path, sha: str) -> Dict[str, object]:
    """The release profile of commit `sha`, read from git's objects, not from a checkout: `files` (every tracked path
    -> SHA-256 of its bytes), `rules_carried`, `offline_reads` and `id`, SHA-256 over the canonical JSON of the rest.
    A commit with a symlink or a submodule has none: their bytes are not in the commit."""
    if not V.canonical_commit_id(Path(repo_dir), sha):  # a ref or a short id names no fixed set of files
        raise V.VarsError(f"{sha[:80]!r} is not a full commit id of {repo_dir}")
    listing = subprocess.run(["git", "-C", str(repo_dir), "ls-tree", "-r", "-z", "--full-tree", sha],
                             capture_output=True, check=True).stdout.decode()
    entries = []  # (path, object id), every entry of the tree with its mode: a symlink and a submodule appear too
    for entry in filter(None, listing.split("\0")):
        meta, _, path = entry.partition("\t")
        mode, _, oid = meta.split(" ")
        if mode not in ("100644", "100755"):
            raise V.VarsError(f"{path} at {sha[:12]} is not a regular file (mode {mode}): its bytes are not in the commit")
        entries.append((path, oid))
    batch = subprocess.run(["git", "-C", str(repo_dir), "cat-file", "--batch"], capture_output=True, check=True,
                           input="".join(f"{oid}\n" for _, oid in entries).encode()).stdout
    files: Dict[str, str] = {}
    blobs: Dict[str, bytes] = {}
    at = 0
    for path, oid in entries:
        header_end = batch.index(b"\n", at)
        size = int(batch[at:header_end].split(b" ")[2])
        raw = batch[header_end + 1: header_end + 1 + size]
        at = header_end + 1 + size + 1
        files[path], blobs[path] = V.sha256(raw).hex(), raw
    carried = {name: files[path] for path, name in RULES_FILES if path in files}
    m = re.search(rb'^H_LENS_KERNEL = bytes\.fromhex\("([0-9a-f]{64})"\)', blobs.get("verify/minds_verify.py", b""), re.M)
    offline = {name: h for name, h in carried.items() if m and h == m.group(1).decode()}
    if m and not offline:
        offline = {"other": m.group(1).decode()}  # a rules identity this commit does not carry
    doc: Dict[str, object] = {"format": PROFILE_FORMAT, "files": dict(sorted(files.items())), "rules_carried": carried,
                              "offline_reads": offline}
    return dict(doc, id=_digest(doc))


def release(repo_dir: Path, sk: bytes, main_sha: str, checks: List[str],
            siblings: Optional[Dict[str, str]] = None, profile: Optional[str] = None) -> Tuple[str, Dict[str, bytes]]:
    """Record a release of `main_sha`: a decision stating it and the checks, the maintainer's ATTESTED verdict on it,
    and a projection of the chain as it stood before this commit. The decision's evaluator policy and the
    projection's witness policy are every key on the roster: the release is settled when each member has attested
    it, and the projection when each has witnessed it."""
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    if tip is None:
        raise V.VarsError("run `init` first")
    s = governing_scope(repo)
    atoms: Dict[bytes, bytes] = {}
    keys = roster(repo)
    everyone = _policy(atoms, len(keys), keys)
    pins = "".join(f" {k}@{siblings[k]}" for k in SIBLINGS) if siblings else ""
    if profile is not None and not re.fullmatch(r"[0-9a-f]{64}", profile):
        raise V.VarsError("a release profile is a SHA-256 in lowercase hex")
    if any(";" in c or c.startswith("profile@") for c in checks):
        raise V.VarsError("a check line may not contain ';' nor start with 'profile@': they mark the statement's parts")
    # The profile goes last, after the checks: a reader of the earlier format matches only the prefix up to the
    # first ';', so it still reads main, rules and pins from a statement that names a profile.
    statement = (f"minds release main@{main_sha} rules@{governing_rules(repo).hex()}{pins}; checks: "
                 + "; ".join(checks) + (f"; profile@{profile}" if profile else ""))
    tag = main_sha[:12]
    decision = V.Cell(
        h_schema=V.H_SCHEMA["decision"],
        h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/release/{tag}")),
        h_payload=_put(atoms, V.atom_utf8(statement)),
        slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, everyone),
    )
    verdict = V.Cell(
        h_schema=V.H_SCHEMA["verdict"],
        h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/release/{tag}/attested")),
        h_payload=decision.id,
        h_attests=_put(atoms, V.atom_hvec([decision.id])),
        slots=(V.H_EMPTY, V.H_ATTESTED, _put(atoms, V.atom_utf8("minds-maintainer"))),
    )
    h_in, h_state = repo.projection_digests(SCOPE, tip)
    tip_rules = V.chain_rules(SCOPE, repo.chain_deltas(repo.commit_chain(tip)))  # the rules of the tip's epoch
    projection = V.Cell(
        h_schema=V.H_SCHEMA["projection"],
        h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/projection/{tip[:12]}")),
        h_payload=V.H_EMPTY,
        slots=(_put(atoms, V.atom_utf8(tip)), tip_rules, h_in, h_state, everyone),
    )
    cells = [decision, verdict, projection]
    c = repo.build_candidate_commit(SCOPE, atoms, cells, [V.Seal.sign(sk, x.id, s) for x in cells], parent_commit=tip)
    repo.admit_and_advance(SCOPE, c, expected_old=tip)
    return c, {"decision": decision.id, "verdict": verdict.id, "projection": projection.id}


def show(repo_dir: Path) -> List[Dict[str, object]]:
    repo = V.GitVarsRepo(repo_dir)
    lens = repo.lens(SCOPE)
    cells, atoms = lens["cells"], lens["atoms"]
    out = []
    for cid, c in cells.items():
        kind = {V.H_SCHEMA["decision"]: "release", V.H_SCHEMA["projection"]: "projection"}.get(c.h_schema)
        if kind is None:
            continue
        row = {"kind": kind, "id": cid.hex(), "name": V.parse_utf8(atoms[c.h_slot_name]),
               "settled": lens["settled"][cid]}
        if kind == "release":
            row["statement"] = V.parse_utf8(atoms[c.h_payload])
        out.append(row)
    return sorted(out, key=lambda r: r["name"])


RULES_NAMES = {V.H_LENS_KERNEL: "v1", V.H_LENS_KERNEL_V1B: "v1b", V.H_LENS_KERNEL_V2: "v2"}


def status(repo_dir: Path, main: str = "main") -> Dict[str, object]:
    """Where the release process stands, read only: whether `main` is released, and for each release whether it is
    Settled and, as Pass 3 reads it, which evaluators' endorsements count, which have a live INVALID on it, and which
    have not yet answered; which projections await a witness; the governing rules; the rules changes on the chain;
    and the claims debt at `main`. Nothing is signed or written. Merged is not Settled."""
    git = lambda *a: subprocess.run(["git", "-C", str(repo_dir), *a], capture_output=True, text=True)
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    if tip is None:
        raise V.VarsError("no chain: run `init` first")
    atoms, cells, seals = repo.read_cas_tree(tip)
    lens = repo.lens(SCOPE)
    settled = lens["settled"]
    keys = roster(repo)
    sealers: Dict[bytes, set] = {}
    for x in seals.values():
        sealers.setdefault(x.h_target, set()).add(x.actor_pubkey)
    main_sha = git("rev-parse", "--verify", f"{main}^{{commit}}").stdout.strip() or None
    releases, projections = [], []
    for cid, c in sorted(cells.items(), key=lambda kv: V.parse_utf8(atoms[kv[1].h_slot_name])):
        name = V.parse_utf8(atoms[c.h_slot_name])
        if c.h_schema == V.H_SCHEMA["projection"] and not settled.get(cid):
            _, hv = V.parse_pol1(atoms[c.slots[4]])
            missing = [k for k in V.parse_hvec(atoms[hv], require_sorted=True) if k not in sealers.get(cid, set())]
            projections.append({"name": name, "id": cid.hex(), "unwitnessed_by": [k.hex() for k in missing]})
        if c.h_schema != V.H_SCHEMA["decision"] or not name.startswith(f"{SCOPE}/release/"):
            continue
        sha, rules, profile, _ = parse_release_profile(V.parse_utf8(atoms[c.h_payload]))
        row: Dict[str, object] = {"name": name, "id": cid.hex(), "commit": sha, "profile": profile,
                                  "settled": bool(settled.get(cid))}
        if cid not in lens["evaluators"]:  # not live, so Pass 3 does not evaluate it and no one is awaited
            row.update(threshold=None, evaluators=None, attested_by=[], invalid_by=[], awaiting=[])
        else:  # Pass 3's own reading: its evaluation policy (the release's, or the scope's for an early release
            # naming none) and the endorsements it counts; an evaluator with a live INVALID has answered
            thr, evaluators = lens["evaluators"][cid]
            counted, invalid = lens["endorsers"][cid], lens["invalidators"][cid]
            row.update(threshold=thr, evaluators=sorted(k.hex() for k in evaluators),
                       attested_by=sorted(k.hex() for k in counted),
                       invalid_by=sorted(k.hex() for k in invalid),
                       awaiting=[] if row["settled"] else sorted(k.hex() for k in evaluators - counted - invalid))
        releases.append(row)
    released = {r["commit"] for r in releases}
    last = None
    if main_sha:  # the newest released commit on main's history, and how many commits main has beyond it
        for line in git("rev-list", main_sha).stdout.split():
            if line in released:
                last = line
                break
    behind = None
    if main_sha and last:
        behind = int(git("rev-list", "--count", f"{last}..{main_sha}").stdout.strip() or 0)
    claims = git("show", f"{main_sha}:claims.json").stdout if main_sha else ""
    debt: Dict[str, int] = {}
    if claims:
        for x in json.loads(claims)["claims"]:
            debt[x["status"]] = debt.get(x["status"], 0) + 1
    rules = governing_rules(repo)
    return {
        "chain": tip, "main": main_sha, "main_released": main_sha in released, "last_released": last,
        "commits_since_release": behind,
        "rules": {"id": rules.hex(), "name": RULES_NAMES.get(rules, "unknown")},
        "roster": sorted(k.hex() for k in keys),
        "releases": releases,
        "unsettled": [r["name"] for r in releases if not r["settled"]],
        "unwitnessed_projections": projections,
        "rules_changes": len(evidence(repo_dir)["changes"]),
        "claims_at_main": dict(sorted(debt.items())),
    }


def covering_projection(repo: V.GitVarsRepo, decision_id: bytes) -> Optional[bytes]:
    """The latest projection whose tip already holds `decision_id` (so its statuses cover it), preferring one that is
    witnessed (Settled), if any."""
    chain = repo.commit_chain(repo.ref_commit(SCOPE))
    atoms, cells, _ = repo.read_cas_tree(chain[-1])
    settled = repo.lens(SCOPE)["settled"]
    best: Optional[Tuple[bool, int, bytes]] = None
    for cid, c in cells.items():
        if c.h_schema != V.H_SCHEMA["projection"]:
            continue
        tip = V.parse_utf8(atoms[c.slots[0]])
        if tip in chain and decision_id in repo.read_cas_tree(tip)[1]:
            key = (bool(settled.get(cid)), chain.index(tip), cid)
            if best is None or key > best:
                best = key
    return None if best is None else best[2]


# Every rules module a commit may carry: the path whose presence says it carries it, the crate directory, cargo's
# extra arguments, the wasm cargo builds, and the identity it must hash to. Built one after another: the v1b build
# overwrites the v1 wasm in kernel/target, after it was hashed.
KERNELS = (("kernel", "kernel", (), "vars_lens.wasm", V.H_LENS_KERNEL, "H_LENS_KERNEL"),
           ("kernel2", "kernel2", (), "vars_lens2.wasm", V.H_LENS_KERNEL_V2, "H_LENS_KERNEL_V2"),
           ("kernel/lens1b.wasm", "kernel", ("--features", "commit-bound"), "vars_lens.wasm", V.H_LENS_KERNEL_V1B,
            "H_LENS_KERNEL_V1B"))


def _run(cmd: List[str], cwd: Path) -> bool:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True).returncode == 0


def kernel_checks(root: Path, rules: bytes, run=_run) -> List[Tuple[str, bool]]:
    """Rebuild every rules module `root` carries (kernel/, kernel2/ and kernel/lens1b.wasm where present); each must
    hash to its pinned identity, and the rules the release names must be one of those rebuilt here."""
    results: List[Tuple[str, bool]] = []
    rebuilt = set()
    for marker, d, extra, wasm_name, pinned, label in KERNELS:
        if not (root / marker).exists():
            continue
        built = run(["cargo", "build", "--release", "--target", "wasm32-unknown-unknown", *extra], root / d)
        wasm = root / d / "target" / "wasm32-unknown-unknown" / "release" / wasm_name
        ok = built and wasm.exists() and V.sha256(wasm.read_bytes()) == pinned
        results.append((f"{marker} rebuild hashes to {label}" if extra else f"{d} rebuild hashes to {label}", ok))
        if ok:
            rebuilt.add(pinned)
    results.append(("the released rules are rebuilt here", rules in rebuilt))
    return results


def run_checks(root: Path, rules: bytes = V.H_LENS_KERNEL) -> Tuple[List[str], bool]:
    """Every check a release requires, as `name OK|FAILED` lines; the release is refused unless all pass. Every
    rules module built from `root` must hash to its identity, and `rules` must be one of them."""
    run = _run

    # The Lean executables first: properties I9, I10 and I12 run them, so in a fresh checkout they must exist
    results: List[Tuple[str, bool]] = []
    for target in ("", "vars1exec", "vars1fold", "vars1cycle", "Vars1Sigma"):
        results.append((f"lake build {target}".strip(), run(["lake", "build", *([target] if target else [])], root / "proofs")))
    results += [
        ("test_vars1", run([sys.executable, "-m", "unittest", "test_vars1"], root)),
        ("test_vars1_props", run([sys.executable, "test_vars1_props.py"], root)),
    ]
    results += kernel_checks(root, rules)
    return [f"{n} {'OK' if ok else 'FAILED'}" for n, ok in results], all(ok for _, ok in results)


def release_target(repo_dir: Path) -> Tuple[str, Optional[str]]:
    """The commit a release would record — `main` — and why it may not be recorded now, if so: the checks run in this
    checkout, so its HEAD must be main's commit and its tree clean."""
    def git(*a: str) -> str:
        return subprocess.run(["git", "-C", str(repo_dir), *a], capture_output=True, text=True, check=True).stdout.strip()

    main_sha = git("rev-parse", "--verify", "main^{commit}")
    if git("rev-parse", "--verify", "HEAD^{commit}") != main_sha:
        return main_sha, "HEAD is not main: the checks would run on another commit"
    if git("status", "--porcelain", "--untracked-files=all"):
        return main_sha, "the working tree is not clean"
    return main_sha, None


def parse_release(statement: str) -> Tuple[str, bytes, Optional[Dict[str, str]]]:
    """The commit, rules hash and (for releases that pin them) sibling commits a release statement names."""
    sha, rules, _, pins = parse_release_profile(statement)
    return sha, rules, pins


def parse_release_profile(statement: str) -> Tuple[str, bytes, Optional[str], Optional[Dict[str, str]]]:
    """The commit, rules hash, release profile id (for releases that name one) and sibling pins (for releases that
    pin them) a release statement names."""
    sib = "".join(rf"(?: {k}@([0-9a-f]{{40}}))" for k in SIBLINGS)
    m = re.match(rf"^minds release main@([0-9a-f]{{40}}) rules@([0-9a-f]{{64}})(?:{sib})?;", statement)
    if m is None:
        raise V.VarsError("not a release statement")
    pins = dict(zip(SIBLINGS, m.groups()[2:])) if m.group(3) else None
    tail = re.search(r"; profile@([0-9a-f]{64})$", statement)
    if tail is None and "; profile@" in statement:  # a marker that is not a profile is not "no profile"
        raise V.VarsError("a release statement with a malformed profile")
    return m.group(1), bytes.fromhex(m.group(2)), tail.group(1) if tail else None, pins


def checks_at(repo_dir: Path, sha: str, rules: bytes, siblings: Optional[Dict[str, str]] = None) -> Tuple[List[str], bool]:
    """Run every check on commit `sha` in a fresh worktree under `.git/vars/verify/`. A commit now carries
    its dependencies (sigma-glyph from PyPI by requirements.txt, run by this interpreter; vendored Lean sources and
    vectors), so nothing sits beside the worktree. An older release that pinned sibling commits (`siblings`) gets
    each extracted at that commit beside it (read from the sibling repository with `git archive`), and Book I is
    compared with the spec's pin. The worktree and any extracted siblings are removed afterwards."""
    git = lambda *a: subprocess.run(["git", "-C", str(repo_dir), *a], capture_output=True, text=True, check=True)
    # every commit checked out or compared is named by its canonical id in its own repository, never by a ref
    if not V.canonical_commit_id(repo_dir, sha):
        raise V.VarsError(f"release commit {sha[:80]!r} is not a full commit id of {repo_dir}")
    parent = Path(repo_dir).resolve().parent
    for sib, pin in (siblings or {}).items():
        if not V.canonical_commit_id(parent / sib, pin):
            raise V.VarsError(f"{sib} pin {pin[:80]!r} is not a full commit id of its repository")
    if siblings is not None and not V.canonical_commit_id(parent / "sigma-glyph", SIGMA_PIN):
        raise V.VarsError(f"the spec's Book I pin {SIGMA_PIN} is not a commit of the sigma-glyph checkout")
    git("merge-base", "--is-ancestor", sha, "main")
    base = Path(repo_dir) / ".git" / "vars" / "verify" / sha[:12]
    base.mkdir(parents=True, exist_ok=True)
    pre: List[Tuple[str, bool]] = []
    for sib in SIBLINGS:
        dst = base / sib
        if dst.is_symlink() or dst.is_file():
            dst.unlink()
        elif dst.exists():
            shutil.rmtree(dst)
        if siblings is None:
            continue
        dst.mkdir()
        arc = subprocess.run(["git", "-C", str(parent / sib), "archive", siblings[sib]], capture_output=True, check=True)
        subprocess.run(["tar", "-x", "-C", str(dst)], input=arc.stdout, check=True)
    if siblings is not None:
        same = subprocess.run(["git", "-C", str(parent / "sigma-glyph"), "diff", "--quiet", SIGMA_PIN,
                               siblings["sigma-glyph"], "--", *BOOK_I]).returncode == 0
        pre.append((f"sigma-glyph Book I equals the spec's pin {SIGMA_PIN}", same))
    wt = base / "minds"
    if wt.exists():
        git("worktree", "remove", "--force", str(wt))
    git("worktree", "add", "-q", "--detach", str(wt), sha)
    try:
        lines, ok = run_checks(wt, rules)
    finally:
        git("worktree", "remove", "--force", str(wt))
        for sib in SIBLINGS:
            dst = base / sib
            if dst.exists() and not dst.is_symlink():
                shutil.rmtree(dst)
    return [f"{n} {'OK' if g else 'FAILED'}" for n, g in pre] + lines, ok and all(g for _, g in pre)


def verify_release(repo_dir: Path, sk: bytes, decision_id: bytes, name: str,
                   checks=checks_at) -> Tuple[str, bool, List[str]]:
    """As a roster member: run `checks` on the release's commit, record this member's verdict on the decision
    (ATTESTED if every check passed, else INVALID), and witness every projection that names this member's key and
    whose digests this host recomputes. Returns the new commit, the outcome and the check lines.

    `name` is the member's verifier id, the same on every run: an INVALID after the member's own ATTESTED
    contradicts it in Pass 3 and so withdraws it. Each outcome is recorded at most once per member and release;
    an INVALID cannot be taken back by a later ATTESTED."""
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    atoms, cells, seals = repo.read_cas_tree(tip)
    pk = V.ed25519_pubkey(sk)
    if pk not in roster(repo):
        raise V.VarsError("this key is not on the roster; a member must `join` it first")
    d = cells.get(decision_id)
    if d is None or d.h_schema != V.H_SCHEMA["decision"]:
        raise V.VarsError("not a decision of this chain")
    sha, rules, profile, pins = parse_release_profile(V.parse_utf8(atoms[d.h_payload]))
    lines, ok = checks(repo_dir, sha, rules, siblings=pins) if pins else checks(repo_dir, sha, rules)
    if profile is not None:  # the files the release names are the files at its commit, recomputed here
        try:
            same = profile_at(repo_dir, sha)["id"] == profile
        except V.VarsError:
            same = False
        lines = lines + [f"release profile {profile[:12]} is the commit's {'OK' if same else 'FAILED'}"]
        ok = ok and same
    s = governing_scope(repo)
    new: Dict[bytes, bytes] = {}
    verdict = V.Cell(
        h_schema=V.H_SCHEMA["verdict"],
        h_slot_name=_put(new, V.atom_utf8(f"{V.parse_utf8(atoms[d.h_slot_name])}/{name}/"
                                           f"{'attested' if ok else 'invalid'}")),
        h_payload=decision_id,
        h_attests=_put(new, V.atom_hvec([decision_id])),
        slots=(V.H_EMPTY, V.H_ATTESTED if ok else V.H_VERDICT_INVALID, _put(new, V.atom_utf8(name))),
    )
    if verdict.id in cells:
        raise V.VarsError("this member already recorded this verdict")
    sealed_by_me = {x.h_target for x in seals.values() if x.actor_pubkey == pk}
    witness = []
    for cid, c in sorted(cells.items()):
        if c.h_schema != V.H_SCHEMA["projection"] or cid in sealed_by_me:
            continue
        _, hv = V.parse_pol1(atoms[c.slots[4]])
        if pk not in V.parse_hvec(atoms[hv], require_sorted=True):
            continue
        if repo.projection_digests(SCOPE, V.parse_utf8(atoms[c.slots[0]])) != (c.slots[2], c.slots[3]):
            raise V.VarsError(f"projection {cid.hex()[:12]} does not match this host's recomputation")
        witness.append(cid)
    c = repo.build_candidate_commit(SCOPE, new, [verdict],
                                    [V.Seal.sign(sk, x, s) for x in [verdict.id, *witness]], parent_commit=tip)
    repo.admit_and_advance(SCOPE, c, expected_old=tip)
    return c, ok, lines


def _main(argv: List[str]) -> int:
    cmd = argv[0] if argv else ""
    repo_dir = ROOT
    if cmd == "init":
        print(init(repo_dir, load_or_create_key(repo_dir)))
        print("maintainer key:", V.ed25519_pubkey(load_or_create_key(repo_dir)).hex())
        return 0
    if cmd == "release":
        main_sha, why = release_target(repo_dir)
        if why:
            print(f"refused: {why}", file=sys.stderr)
            return 1
        checks, ok = checks_at(repo_dir, main_sha, governing_rules(V.GitVarsRepo(repo_dir)))  # fresh worktree
        print("\n".join(checks))
        if not ok:
            print("refused: a check failed", file=sys.stderr)
            return 1
        if release_target(repo_dir) != (main_sha, None):
            print("refused: main, HEAD or the tree changed while the checks ran", file=sys.stderr)
            return 1
        commit, ids = release(repo_dir, load_or_create_key(repo_dir), main_sha, checks,
                              profile=profile_at(repo_dir, main_sha)["id"])
        print(json.dumps({"commit": commit, **{k: v.hex() for k, v in ids.items()}}, indent=2))
        return 0
    if cmd == "join" and len(argv) == 3:
        print(join(repo_dir, load_or_create_key(repo_dir), bytes.fromhex(argv[1]), argv[2]))
        return 0
    if cmd == "verify-release" and len(argv) == 6 and argv[2] == "--key" and argv[4] == "--name":
        sk = bytes.fromhex(Path(argv[3]).read_text().strip())
        commit, ok, lines = verify_release(repo_dir, sk, bytes.fromhex(argv[1]), argv[5])
        print("\n".join(lines))
        print(json.dumps({"commit": commit, "verdict": "ATTESTED" if ok else "INVALID"}))
        return 0 if ok else 1
    if cmd == "shadow" and len(argv) in (2, 4) and argv[2:3] in ([], ["--out"]):
        doc = json.dumps(shadow(repo_dir, bytes.fromhex(argv[1])), indent=2)
        if len(argv) == 4:
            Path(argv[3]).write_text(doc + "\n")
        print(doc)
        return 0
    if cmd == "change-rules" and len(argv) >= 5 and argv[3] == "--manifest":
        kind, new_rules = argv[1], bytes.fromhex(argv[2])
        opts = dict(zip(argv[5::2], argv[6::2]))
        fields: Dict[str, object] = {}
        if kind == "correction":
            fields = {k: opts[f"--{k.replace('_', '-')}"] for k in
                      ("counterexample_scope", "counterexample", "cell", "status", "right")}
        elif kind in ("hardening", "tightening"):
            fields = {"input": Path(opts["--input"]).read_bytes(), "budget": opts["--budget"], "refusal": opts["--refusal"]}
        manifest = json.loads(Path(argv[4]).read_text())
        print(change_rules(repo_dir, load_or_create_key(repo_dir), kind, new_rules, manifest, opts.get("--accept"),
                           **fields))
        return 0
    if cmd == "evidence":
        print(json.dumps(evidence(repo_dir), indent=2))
        return 0
    if cmd == "replay-changes":
        rows = replay_changes(repo_dir)
        print("\n".join(f"{d} {r}" for d, r in rows))
        return 0 if all(r == "REPLAYED" for _, r in rows) else 1
    if cmd == "show":
        print(json.dumps(show(repo_dir), indent=2))
        return 0
    if cmd == "status":
        print(json.dumps(status(repo_dir), indent=2))
        return 0
    if cmd == "profile" and len(argv) == 2:
        print(json.dumps(profile_at(repo_dir, argv[1]), indent=2))
        return 0
    if cmd == "bundle" and len(argv) == 2:
        print(json.dumps(V.export_projection(V.GitVarsRepo(repo_dir), SCOPE, bytes.fromhex(argv[1])), indent=2))
        return 0
    if cmd == "attest" and len(argv) == 2:
        repo = V.GitVarsRepo(repo_dir)
        did = bytes.fromhex(argv[1])
        print(json.dumps(V.export_attestation(repo, SCOPE, did, covering_projection(repo, did)), indent=2))
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(_main(sys.argv[1:]))
