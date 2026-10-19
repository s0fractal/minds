#!/usr/bin/env python3
"""minds governs itself with VARS-1: the chain `refs/vars/heads/minds` in this repository.

Each release of `main` is a `decision` cell stating what was released (commit, rules kernel) and which checks
passed, attested by the maintainer's verdict, together with a projection of the chain for clients without the
repository. The maintainer key lives in `.git/vars/maintainer.key` (never committed or pushed); the scope's roster
is that key until a rotation adds others.

    tools/minds_chain.py init                 # genesis of refs/vars/heads/minds (once)
    tools/minds_chain.py release              # run every check, then record main@HEAD as a release
    tools/minds_chain.py show                 # releases and projections with their status
    tools/minds_chain.py bundle PROJECTION    # a projection bundle for `vars1.py verify-projection`
    tools/minds_chain.py attest DECISION      # an attestation bundle for `vars1.py verify-attestation`
"""
from __future__ import annotations

import json
import os
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


def _maintainer_policy(atoms: Dict[bytes, bytes], sk: bytes) -> bytes:
    return _put(atoms, V.atom_pol1(1, _put(atoms, V.atom_hvec([V.ed25519_pubkey(sk)]))))


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


def release(repo_dir: Path, sk: bytes, main_sha: str, checks: List[str]) -> Tuple[str, Dict[str, bytes]]:
    """Record a release of `main_sha`: a decision stating it and the checks, the maintainer's ATTESTED verdict on it,
    and a projection of the chain as it stood before this commit, witnessed by the maintainer."""
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    if tip is None:
        raise V.VarsError("run `init` first")
    s = governing_scope(repo)
    atoms: Dict[bytes, bytes] = {}
    statement = f"minds release main@{main_sha} rules@{V.H_LENS_KERNEL.hex()}; checks: " + "; ".join(checks)
    tag = main_sha[:12]
    decision = V.Cell(
        h_schema=V.H_SCHEMA["decision"],
        h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/release/{tag}")),
        h_payload=_put(atoms, V.atom_utf8(statement)),
        slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY),
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
        slots=(_put(atoms, V.atom_utf8(tip)), V.H_LENS_KERNEL, h_in, h_state, _maintainer_policy(atoms, sk)),
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
    """The latest projection whose tip already holds `decision_id` (so its statuses cover it), if any."""
    chain = repo.commit_chain(repo.ref_commit(SCOPE))
    _, cells, _ = repo.read_cas_tree(chain[-1])
    atoms = repo.read_cas_tree(chain[-1])[0]
    best: Optional[Tuple[int, bytes]] = None
    for cid, c in cells.items():
        if c.h_schema != V.H_SCHEMA["projection"]:
            continue
        tip = V.parse_utf8(atoms[c.slots[0]])
        if tip in chain and decision_id in repo.read_cas_tree(tip)[1]:
            pos = chain.index(tip)
            if best is None or pos > best[0]:
                best = (pos, cid)
    return None if best is None else best[1]


def run_checks(root: Path) -> Tuple[List[str], bool]:
    """Every check a release requires, as `name OK|FAILED` lines; the release is refused unless all pass."""
    def run(cmd: List[str], cwd: Path) -> bool:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True).returncode == 0

    results: List[Tuple[str, bool]] = [
        ("test_vars1", run([sys.executable, "-m", "unittest", "test_vars1"], root)),
        ("test_vars1_props", run([sys.executable, "test_vars1_props.py"], root)),
    ]
    for target in ("", "vars1exec", "vars1fold", "Vars1Sigma"):
        results.append((f"lake build {target}".strip(), run(["lake", "build", *([target] if target else [])], root / "proofs")))
    built = run(["cargo", "build", "--release", "--target", "wasm32-unknown-unknown"], root / "kernel")
    wasm = root / "kernel" / "target" / "wasm32-unknown-unknown" / "release" / "vars_lens.wasm"
    results.append(("kernel rebuild hashes to H_LENS_KERNEL",
                    built and wasm.exists() and V.sha256(wasm.read_bytes()) == V.H_LENS_KERNEL))
    return [f"{n} {'OK' if ok else 'FAILED'}" for n, ok in results], all(ok for _, ok in results)


def _main(argv: List[str]) -> int:
    cmd = argv[0] if argv else ""
    repo_dir = ROOT
    if cmd == "init":
        print(init(repo_dir, load_or_create_key(repo_dir)))
        print("maintainer key:", V.ed25519_pubkey(load_or_create_key(repo_dir)).hex())
        return 0
    if cmd == "release":
        main_sha = subprocess.run(["git", "-C", str(repo_dir), "rev-parse", "main"], capture_output=True,
                                  text=True, check=True).stdout.strip()
        dirty = subprocess.run(["git", "-C", str(repo_dir), "status", "--porcelain"], capture_output=True,
                               text=True).stdout.strip()
        if dirty:
            print("refused: the working tree is not clean", file=sys.stderr)
            return 1
        checks, ok = run_checks(repo_dir)
        print("\n".join(checks))
        if not ok:
            print("refused: a check failed", file=sys.stderr)
            return 1
        commit, ids = release(repo_dir, load_or_create_key(repo_dir), main_sha, checks)
        print(json.dumps({"commit": commit, **{k: v.hex() for k, v in ids.items()}}, indent=2))
        return 0
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
