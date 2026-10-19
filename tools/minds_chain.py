#!/usr/bin/env python3
"""minds governs itself with VARS-1: the chain `refs/vars/heads/minds` in this repository.

Each release of `main` is a `decision` cell stating what was released (commit, rules kernel) and which checks
passed, attested by the maintainer's verdict, together with a projection of the chain for clients without the
repository. The maintainer key lives in `.git/vars/maintainer.key` (never committed or pushed); the scope's roster
is that key until `join` adds others. With more than one key, every release needs a verdict and a projection seal
from every key on the roster: another member runs `verify-release`, which reruns the checks on the released commit
in its own worktree and records that member's verdict.

    tools/minds_chain.py init                 # genesis of refs/vars/heads/minds (once)
    tools/minds_chain.py release              # with HEAD = main and a clean tree, run every check on main in a
                                              # fresh worktree, then record main
    tools/minds_chain.py join PUBKEY NAME     # rotate the roster to add a member's Ed25519 public key (hex)
    tools/minds_chain.py verify-release DECISION --key FILE --name NAME
                                              # as a member: rerun the checks at the release's commit, record a
                                              # verdict, and witness the projections that name your key
    tools/minds_chain.py show                 # releases and projections with their status
    tools/minds_chain.py bundle PROJECTION    # a projection bundle for `vars1.py verify-projection`
    tools/minds_chain.py attest DECISION      # an attestation bundle for `vars1.py verify-attestation`
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
import vars1 as V  # noqa: E402

SCOPE = "minds"


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
        slots=(pol, pol, V.H_LENS_KERNEL),
    )
    c = repo.build_candidate_commit(SCOPE, atoms, [scope], [V.Seal.sign(sk, scope.id, s)], parent_commit=tip)
    repo.admit_and_advance(SCOPE, c, expected_old=tip)
    return c


def release(repo_dir: Path, sk: bytes, main_sha: str, checks: List[str]) -> Tuple[str, Dict[str, bytes]]:
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
    statement = f"minds release main@{main_sha} rules@{V.H_LENS_KERNEL.hex()}; checks: " + "; ".join(checks)
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
    projection = V.Cell(
        h_schema=V.H_SCHEMA["projection"],
        h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/projection/{tip[:12]}")),
        h_payload=V.H_EMPTY,
        slots=(_put(atoms, V.atom_utf8(tip)), V.H_LENS_KERNEL, h_in, h_state, everyone),
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


def run_checks(root: Path, rules: bytes = V.H_LENS_KERNEL) -> Tuple[List[str], bool]:
    """Every check a release requires, as `name OK|FAILED` lines; the release is refused unless all pass. The kernel
    built from `root` must hash to `rules`."""
    def run(cmd: List[str], cwd: Path) -> bool:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True).returncode == 0

    # The Lean executables first: properties I9 and I10 run them, so in a fresh checkout they must exist
    results: List[Tuple[str, bool]] = []
    for target in ("", "vars1exec", "vars1fold", "Vars1Sigma"):
        results.append((f"lake build {target}".strip(), run(["lake", "build", *([target] if target else [])], root / "proofs")))
    results += [
        ("test_vars1", run([sys.executable, "-m", "unittest", "test_vars1"], root)),
        ("test_vars1_props", run([sys.executable, "test_vars1_props.py"], root)),
    ]
    built = run(["cargo", "build", "--release", "--target", "wasm32-unknown-unknown"], root / "kernel")
    wasm = root / "kernel" / "target" / "wasm32-unknown-unknown" / "release" / "vars_lens.wasm"
    results.append(("kernel rebuild hashes to H_LENS_KERNEL",
                    built and wasm.exists() and V.sha256(wasm.read_bytes()) == rules))
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


def parse_release(statement: str) -> Tuple[str, bytes]:
    """The commit and rules hash a release statement names."""
    m = re.match(r"^minds release main@([0-9a-f]{40}) rules@([0-9a-f]{64});", statement)
    if m is None:
        raise V.VarsError("not a release statement")
    return m.group(1), bytes.fromhex(m.group(2))


def checks_at(repo_dir: Path, sha: str, rules: bytes) -> Tuple[List[str], bool]:
    """Run every check on commit `sha` in a fresh worktree under `.git/vars/verify/`, beside links to the sibling
    checkouts the code expects; the worktree is removed afterwards."""
    git = lambda *a: subprocess.run(["git", "-C", str(repo_dir), *a], capture_output=True, text=True, check=True)
    git("merge-base", "--is-ancestor", sha, "main")
    base = Path(repo_dir) / ".git" / "vars" / "verify" / sha[:12]
    base.mkdir(parents=True, exist_ok=True)
    for sib in ("sigma-glyph", "primitives"):
        link = base / sib
        if not link.exists():
            link.symlink_to(Path(repo_dir).resolve().parent / sib)
    wt = base / "minds"
    if wt.exists():
        git("worktree", "remove", "--force", str(wt))
    git("worktree", "add", "-q", "--detach", str(wt), sha)
    try:
        return run_checks(wt, rules)
    finally:
        git("worktree", "remove", "--force", str(wt))


def verify_release(repo_dir: Path, sk: bytes, decision_id: bytes, name: str,
                   checks=checks_at) -> Tuple[str, bool, List[str]]:
    """As a roster member: run `checks` on the release's commit, record this member's verdict on the decision
    (ATTESTED if every check passed, else INVALID), and witness every projection that names this member's key and
    whose digests this host recomputes. Returns the new commit, the outcome and the check lines."""
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    atoms, cells, seals = repo.read_cas_tree(tip)
    pk = V.ed25519_pubkey(sk)
    if pk not in roster(repo):
        raise V.VarsError("this key is not on the roster; a member must `join` it first")
    d = cells.get(decision_id)
    if d is None or d.h_schema != V.H_SCHEMA["decision"]:
        raise V.VarsError("not a decision of this chain")
    sha, rules = parse_release(V.parse_utf8(atoms[d.h_payload]))
    lines, ok = checks(repo_dir, sha, rules)
    s = governing_scope(repo)
    new: Dict[bytes, bytes] = {}
    verdict = V.Cell(
        h_schema=V.H_SCHEMA["verdict"],
        h_slot_name=_put(new, V.atom_utf8(f"{V.parse_utf8(atoms[d.h_slot_name])}/{name}")),
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
        checks, ok = checks_at(repo_dir, main_sha, V.H_LENS_KERNEL)  # a fresh worktree: nothing left from earlier builds
        print("\n".join(checks))
        if not ok:
            print("refused: a check failed", file=sys.stderr)
            return 1
        if release_target(repo_dir) != (main_sha, None):
            print("refused: main, HEAD or the working tree changed while the checks ran", file=sys.stderr)
            return 1
        commit, ids = release(repo_dir, load_or_create_key(repo_dir), main_sha, checks)
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
    if cmd == "show":
        print(json.dumps(show(repo_dir), indent=2))
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
