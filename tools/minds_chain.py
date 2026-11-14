#!/usr/bin/env python3
"""minds governs itself with VARS-1: the chain `refs/vars/heads/minds` in this repository.

Each release of `main` is a `decision` cell stating what was released (commit, rules kernel) and which checks
passed, attested by the maintainer's verdict, together with a projection of the chain for clients without the
repository. The maintainer key lives in `.git/vars/maintainer.key` (never committed or pushed); the scope's roster
is that key until `join` adds others. With more than one key, every release needs verdicts and projection seals
from a majority of the roster (`majority`): another member runs `verify-release`, which reruns the checks on the
released commit in a fresh checkout and records that member's verdict. A reader who wants every member's veto pins
every key when it verifies.

Run it with the interpreter that has requirements.txt installed (`.venv/bin/python tools/minds_chain.py ...`):
the checks run the test suites with that same interpreter, or, for a release whose commit pins other requirements,
with one that has the commit's own installed (`interpreter_for`).

    tools/minds_chain.py init                 # genesis of refs/vars/heads/minds (once)
    tools/minds_chain.py release              # with HEAD = main and a clean tree, run every check on main in a
                                              # fresh checkout, then record main
    tools/minds_chain.py join PUBKEY NAME [--key FILE]...
                                              # rotate the roster to add a member's Ed25519 public key (hex), under
                                              # the thresholds it has, sealed by each FILE or the maintainer key.
                                              # Raise `threshold` first when the key is someone else's (see `join`)
    tools/minds_chain.py threshold N [--key FILE]...
                                              # rotate to the same roster and rules under admission and acceptance
                                              # N-of-n, sealed by each FILE or the maintainer key
    tools/minds_chain.py threshold N [--key FILE]... --propose
                                              # the same rotation, sealed the same way but not admitted: it is kept at
                                              # refs/vars/proposals/minds/<its scope cell> for a cosigner (`cosign`)
    tools/minds_chain.py cosign --key FILE    # as the witness: seal and admit each proposed raise of the threshold, up
                                              # to a majority of the roster, that this key first saw COSIGN_WINDOW ago,
                                              # that another member sealed and that nobody vetoed (a ref
                                              # refs/vars/veto/minds/<cell>); it judges form and time, not merit
    tools/minds_chain.py cosign-ref --key FILE  # the ref this key keeps its signed cosign ledger in (for the push)
    tools/minds_chain.py verify-release DECISION --key FILE --name NAME
                                              # as a member: rerun the checks the release claims at its commit, record
                                              # a verdict, and witness the projections that name your key; exit 3 and
                                              # nothing recorded when they cannot be rerun as they ran (UNREPRODUCIBLE)
    tools/minds_chain.py witnessed-ref --key FILE  # the ref this key remembers its sealed tips in (for the workflow's push)
    tools/minds_chain.py witness --key FILE --name NAME
                                              # as a member: verify-release every release awaiting your key
                                              # (the GitHub Actions witness, .github/workflows/witness.yml)
    tools/minds_chain.py show                # releases and projections with their status
    tools/minds_chain.py status               # read only: is main released, who has not yet attested each
                                              # release or witnessed each projection, rules, claims debt
    tools/minds_chain.py profile COMMIT       # the release profile of COMMIT: every file an admission depends on
    tools/minds_chain.py what-if CELL... [--key FILE | --assume PUBKEY] [--restore]
                                              # what would follow if CELL... (a release's check, say) were
                                              # invalidated: checked by the gate, sealed by FILE or the maintainer
                                              # key (never created), no ref moves, nothing filed on the chain;
                                              # --assume: no key at all, the seals of roster key PUBKEY supposed
                                              # (zero signatures, `mode: assumed` in the report);
                                              # --restore: the signer's own replacement checks and verdicts too
    tools/minds_chain.py power CELL           # read only: which coalitions of roster keys can change the status of
                                              # CELL by commits of their own (`GitVarsRepo.power`)
    tools/minds_chain.py why CELL [--json]   # read only: CELL's status (a name, 8+ hex of its id, or 7+ hex of a
                                              # released commit) and why, in words: whose keys count and whom it waits
                                              # for, what kills it, and, when it is not Grounded, the path down
                                              # `relies` to the first cell that does not hold
    tools/minds_chain.py next [--actor KEY] [--json]
                                              # read only: which single act of one roster key (an ACCEPT or INVALID
                                              # verdict, a seal on a projection or a verdict) would change a status,
                                              # the most cells first, what waits for an answer, and the margin of the
                                              # Settled decisions; KEY is a verifier id or 8+ hex of a key
    tools/minds_chain.py next --check [--every]
                                              # hold `next` to the gate, act by act (`--every`: every seal of every key)
    tools/minds_chain.py lag REPO SCOPE       # read only: which cells of SCOPE in REPO that this chain holds stand on one
                                              # side and not the other, why, and what this scope can do (`vars1.lag`)
    tools/minds_chain.py bundle PROJECTION    # a projection bundle for `vars1.py verify-projection`
    tools/minds_chain.py attest DECISION      # an attestation bundle for `vars1.py verify-attestation`
    tools/minds_chain.py shadow RULES [--out FILE]
                                              # every historical tip under its epoch's rules and under RULES: the
                                              # manifest of every difference (commit, cell, bit, old, new)
    tools/minds_chain.py change-rules CLASS RULES --manifest FILE [--accept DIGEST] [--key FILE]...
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
import time
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple, Union

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
import vars1 as V  # noqa: E402

SCOPE = "minds"
SIBLINGS = ("sigma-glyph", "primitives")
# Book I as the spec pinned it while releases pinned sibling checkouts (VARS-1-SPEC.md `c864d3e`, 2026-10-19): such a
# release is checked against it. Releases since carry requirements.txt, and the spec has moved on (sigma-glyph 1.0.1).
SIGMA_PIN = "c864d3ee01a2fe46c528bd6e9552438e64df5f6b"
BOOK_I = ("impl/sigma_resume.py", "proofs")
# The last commit whose checks read the sibling checkouts beside it, nothing pinning them: its child a512f8b carried the
# first requirements.txt and removed them. Its ancestors are a closed set, history: no commit made since is one of them.
# Every commit of main without a requirements.txt is one, and none of them has one (403 commits, 2026-11-14).
UNPINNED_UNTIL = "f161db7c50d5dd1b8a9dfdf7e52fb8913249f6d5"


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


def majority(n: int) -> int:
    """The threshold of a release's evaluator policy and of its projection's witness policy, for a roster of `n` keys:
    the least `q` with `n < 2q`. Two sets of `q` distinct keys of one roster share at least `2q - n` of them
    (`quorum_overlap`, proofs/Vars1/History.lean), so at this `q` any two conflicting Settled results name a key that
    sealed both, and at `q - 1` that bound is 0 (`majority_overlap`, `majority_least`). Unanimity would let one absent
    member hold every release back; a reader who wants it pins every key (§4.4)."""
    return n // 2 + 1


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


def thresholds(repo: V.GitVarsRepo) -> Tuple[int, int]:
    """The thresholds of the governing scope's admission and acceptance policies."""
    atoms, cells, _ = repo.read_cas_tree(repo.ref_commit(SCOPE))
    scope = cells[governing_scope(repo)]
    return V.parse_pol1(atoms[scope.slots[0]])[0], V.parse_pol1(atoms[scope.slots[1]])[0]


def _rotation(repo: V.GitVarsRepo, keys: List[bytes], admission: int, acceptance: int,
              say: str) -> Tuple[Dict[bytes, bytes], V.Cell, bytes]:
    """The scope cell of a rotation of the governing scope to `keys` under these thresholds, keeping its rules: its atoms,
    the cell and the scope it supersedes (the context its seals sign). `_rotate` files it; `cosign` rebuilds it from a
    proposal to see that the proposal is this and nothing else."""
    s = governing_scope(repo)
    atoms: Dict[bytes, bytes] = {}
    adm = _policy(atoms, admission, keys)
    acc = _policy(atoms, acceptance, keys)
    scope = V.Cell(
        h_schema=V.H_SCHEMA["scope"],
        h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/SCOPE")),
        h_payload=_put(atoms, V.atom_utf8(f"{SCOPE} roster of {len(keys)}: {say}")),
        h_supersedes=_put(atoms, V.atom_hvec([s])),
        h_loss=_put(atoms, V.atom_utf8(f"rotation: {say}")),
        slots=(adm, acc, governing_rules(repo)),
    )
    return atoms, scope, s


def _rotate(repo_dir: Path, sks: Sequence[bytes], keys: List[bytes], admission: int, acceptance: int, say: str,
            propose: bool = False) -> str:
    """A rotation of the governing scope to `keys` under these thresholds, sealed by each of `sks`, keeping its rules. It
    names no projection, so it adds nothing to a key's memory, but no key that remembers a history seals on a fork of it.
    With `propose` the commit is not admitted: it is kept at `proposal_ref` of its scope cell for a cosigner."""
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    for sk in sks:
        refuse_a_fork(repo_dir, V.ed25519_pubkey(sk), tip)
    atoms, scope, s = _rotation(repo, keys, admission, acceptance, say)
    c = repo.build_candidate_commit(SCOPE, atoms, [scope], [V.Seal.sign(sk, scope.id, s) for sk in sks], parent_commit=tip)
    if propose:
        subprocess.run(["git", "-C", str(repo_dir), "update-ref", proposal_ref(scope.id), c], check=True)
        return c
    repo.admit_and_advance(SCOPE, c, expected_old=tip)
    return c


def _join_act(repo: V.GitVarsRepo, pubkey: bytes, name: str) -> Tuple[List[bytes], int, int, str]:
    """What `join` rotates to: the roster plus `pubkey`, under the thresholds it has."""
    keys = roster(repo)
    if pubkey in keys:
        raise V.VarsError("already a member")
    if V.weak_public_key(pubkey):
        raise V.VarsError("weak public key")
    admission, acceptance = thresholds(repo)
    return sorted(keys + [pubkey]), admission, acceptance, f"{name} joins"


def _threshold_act(repo: V.GitVarsRepo, threshold: int) -> Tuple[List[bytes], int, int, str]:
    """What `threshold` rotates to: the same roster under admission and acceptance `threshold`."""
    keys = roster(repo)
    if not 1 <= threshold <= len(keys):
        raise V.VarsError(f"a threshold of {threshold} for a roster of {len(keys)}")
    if thresholds(repo) == (threshold, threshold):
        raise V.VarsError("the scope has this threshold already")
    return keys, threshold, threshold, f"admission and acceptance {threshold} of {len(keys)}"


def join(repo_dir: Path, sks: Union[bytes, Sequence[bytes]], pubkey: bytes, name: str) -> str:
    """Rotate the scope so the roster is the current one plus `pubkey`, under the thresholds it has. Every key of `sks`
    seals it, so a roster whose admission threshold is above 1 needs that many here. Any member may admit cells whatever
    the threshold; releases are settled only by all of them (see `release`).

    Before the first key of someone outside joins, raise the admission threshold to 2 or more (`threshold`): at 1 each key
    alone is the quorum, so the newcomer alone could invalidate any verdict or rotate the others out (spec §4.2). While
    every key is ours this stays at 1 on purpose, since raising it costs three early releases their Settled until a second
    key attests them (`status` says `one_key_is_the_quorum`)."""
    return _rotate(repo_dir, [sks] if isinstance(sks, bytes) else sks, *_join_act(V.GitVarsRepo(repo_dir), pubkey, name))


def set_threshold(repo_dir: Path, sks: Union[bytes, Sequence[bytes]], threshold: int, propose: bool = False) -> str:
    """Rotate the scope to the same roster and rules under this admission and acceptance threshold (spec §4.2). It removes no
    key and changes no rules, so it takes effect at once (§4.1 latches 4a, 4b); it needs the quorum of the policy it leaves.
    One key still admits a cell at any threshold (§3 check 3). An evaluator policy that falls back to the admission policy
    moves with it (§4.2 Pass 3): `what-if` says what that takes from a chain before anyone files this."""
    return _rotate(repo_dir, [sks] if isinstance(sks, bytes) else sks, *_threshold_act(V.GitVarsRepo(repo_dir), threshold),
                   propose=propose)


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


def change_rules(repo_dir: Path, sks: Union[bytes, Sequence[bytes]], kind: str, new_rules: bytes, manifest: Dict[str, object],
                 accept: Optional[str] = None, **fields: object) -> str:
    """Record a rotation of the scope to `new_rules` with a rules-change decision of class `kind` (§4.3), only after
    the shadow replay: `manifest` must be `shadow`'s replay of this chain now. A hardening or an equivalent change
    must leave every historical tip as it was; a correction or a tightening may change some, and is recorded only
    with `accept` equal to the manifest's digest. `fields`: for a correction `counterexample_scope`,
    `counterexample`, `cell`, `status`, `right`; for a hardening or a tightening `input` (bytes), `budget`,
    `refusal` (the code, negated). Every key of `sks` seals it, so an admission threshold above 1 needs that many here.
    The gate then replays the decision's own computations."""
    sks = [sks] if isinstance(sks, bytes) else sks
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
    for sk in sks:
        refuse_a_fork(repo_dir, V.ed25519_pubkey(sk), tip)
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
    c = repo.build_candidate_commit(SCOPE, atoms, cells, [V.Seal.sign(sk, x.id, base_id) for x in cells for sk in sks],
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
# The rules modules a commit carries (by file), and of those the ones the offline verifier interprets, read from its
# own bytes: the rows of minds_verify.py's `KNOWN_RULES_TABLE`, or, in a verifier of one rules identity before it, its
# `H_LENS_KERNEL` line (it reports every other identity unsupported), read as before, so an earlier release keeps its
# profile. Carrying a module is not the gate running it: which modules the gate runs, and for which epochs, is
# vars1.py's `RULES`, named here by its hash. A retired module keeps its row: the profile is a function of the commit,
# and the commits that carried `kernel/lens1c.wasm` (releases of PRs #16–#18) are profiled with it.
RULES_FILES = (("kernel/lens.wasm", "v1"), ("kernel/lens1b.wasm", "v1b"), ("kernel/lens1c.wasm", "v1c"),
               ("kernel2/lens2.wasm", "v2"))


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
    verifier = blobs.get("verify/minds_verify.py", b"")
    table = re.search(rb'^KNOWN_RULES_TABLE = """\n((?:[0-9a-f]{64} v[12] H_LENS_KERNEL\w*\n)+)"""\n', verifier, re.M)
    if table:
        known = {row.split(b" ")[0].decode() for row in table.group(1).splitlines()}
        offline = {name: h for name, h in carried.items() if h in known}
    else:
        m = re.search(rb'^H_LENS_KERNEL = bytes\.fromhex\("([0-9a-f]{64})"\)', verifier, re.M)
        offline = {name: h for name, h in carried.items() if m and h == m.group(1).decode()}
        if m and not offline:
            offline = {"other": m.group(1).decode()}  # a rules identity this commit does not carry
    doc: Dict[str, object] = {"format": PROFILE_FORMAT, "files": dict(sorted(files.items())), "rules_carried": carried,
                              "offline_reads": offline}
    return dict(doc, id=_digest(doc))


def check_cells(atoms: Dict[bytes, bytes], prefix: str, checks: List[str], sha: str,
                profile: Optional[str] = None) -> List["V.Cell"]:
    """One axiom per check line, named `<prefix>/check/<nn>`: what was run, its result, at which commit (and
    profile). The author's seal on it is that author's claim that the check passed there."""
    at = f" at main@{sha}" + (f" profile@{profile}" if profile else "")
    return [V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=_put(atoms, V.atom_utf8(f"{prefix}/check/{i:02d}")),
                   h_payload=_put(atoms, V.atom_utf8(line + at)))
            for i, line in enumerate(checks)]


def release(repo_dir: Path, sk: bytes, main_sha: str, checks: List[str],
            siblings: Optional[Dict[str, str]] = None, profile: Optional[str] = None) -> Tuple[str, Dict[str, bytes]]:
    """Record a release of `main_sha`: a decision stating it and the checks, the maintainer's ATTESTED verdict on it,
    and a projection of the chain as it stood before this commit. The decision's evaluator policy and the
    projection's witness policy are a `majority` of the roster: the release is settled when a majority of members has
    attested it, and the projection when a majority has witnessed it. Once settled, it waits for no one; a member who
    has not answered may still `verify-release` it, for readers who pin its key."""
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    if tip is None:
        raise V.VarsError("run `init` first")
    s = governing_scope(repo)
    atoms: Dict[bytes, bytes] = {}
    keys = roster(repo)
    quorum = _policy(atoms, majority(len(keys)), keys)
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
    # Each check is a cell the decision relies on, so a check later shown wrong takes the release with it (Pass 2),
    # and `what-if` can say so before anyone files it
    grounds = check_cells(atoms, f"{SCOPE}/release/{tag}", checks, main_sha, profile)
    decision = V.Cell(
        h_schema=V.H_SCHEMA["decision"],
        h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/release/{tag}")),
        h_payload=_put(atoms, V.atom_utf8(statement)),
        h_relies=_put(atoms, V.atom_hvec([g.id for g in grounds])),
        slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, quorum),
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
        slots=(_put(atoms, V.atom_utf8(tip)), tip_rules, h_in, h_state, quorum),
    )
    cells = [*grounds, decision, verdict, projection]
    c = repo.build_candidate_commit(SCOPE, atoms, cells, [V.Seal.sign(sk, x.id, s) for x in cells], parent_commit=tip)
    admit_sealing(repo_dir, repo, V.ed25519_pubkey(sk), tip, c, [tip])
    return c, {"decision": decision.id, "verdict": verdict.id, "projection": projection.id}


WHY_BITS = ("accepted", "effective", "invalidated", "retired", "superseded", "active", "stale", "settled", "grounded")
EVALUATED = ("contract", "decision", "question")


def key_names(cells: Dict[bytes, V.Cell], atoms: Dict[bytes, bytes], seals) -> Dict[bytes, str]:
    """Each key's name: the verifier id it gives most often on the verdicts it seals (the NAME of `verify-release`)."""
    seen: Dict[bytes, Dict[str, int]] = {}
    for x in seals.values():
        c = cells.get(x.h_target)
        if c is not None and c.h_schema == V.H_SCHEMA["verdict"] and c.slots[2] != V.H_EMPTY:
            n = V.parse_utf8(atoms[c.slots[2]])
            seen.setdefault(x.actor_pubkey, {}).setdefault(n, 0)
            seen[x.actor_pubkey][n] += 1
    return {k: max(sorted(v), key=v.get) for k, v in seen.items()}


def explain(repo_dir: Path, ref: str) -> Dict[str, object]:
    """Read only: the status of the cell named `ref` (its slot name, 8 or more hex digits of its id, or 7 or more of a
    commit whose release it is) at the chain's tip, and why, from the lens's own tables: the kill edges into it, the
    keys that count and those it waits for, and, when it is not live or not Grounded, each step down to the first cell
    that does not hold. A kill edge's sources are listed with their Effective bit; which of them latched is the
    lens's, and is not said."""
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    if tip is None:
        raise V.VarsError("no chain: run `init` first")
    lens = repo.lens(SCOPE)
    cells, atoms = lens["cells"], lens["atoms"]
    _, _, seals = repo.read_cas_tree(tip)
    names = key_names(cells, atoms, seals)
    schema = {h: n for n, h in V.H_SCHEMA.items()}
    slot = lambda x: V.parse_utf8(atoms[cells[x].h_slot_name])  # noqa: E731
    hv = lambda h: [] if h == V.H_EMPTY else V.parse_hvec(atoms[h], require_sorted=True)  # noqa: E731
    who = lambda ks: [f"{names.get(k, '?')} {k.hex()[:8]}" for k in sorted(ks)]  # noqa: E731
    found = [x for x in cells if slot(x) == ref]
    h = ref.lower()
    if not found and re.fullmatch(r"[0-9a-f]{7,64}", h):
        # 8 or more hex digits of a cell's id, or 7 or more of a released commit: the release whose statement names it
        released = lambda x: (cells[x].h_schema == V.H_SCHEMA["decision"]  # noqa: E731
                              and slot(x).startswith(f"{SCOPE}/release/")
                              and parse_release_profile(V.parse_utf8(atoms[cells[x].h_payload]))[0].startswith(h))
        found = [x for x in cells if (len(h) >= 8 and x.hex().startswith(h)) or released(x)]
    if len(found) != 1:
        some = ", ".join(sorted(slot(x) for x in found)[:6]) + (", ..." if len(found) > 6 else "")
        raise V.VarsError(f"{len(found)} cells answer to {ref!r}" + (f" ({some})" if found else "")
                          + ": name one by its slot name (`show` lists the releases and projections), 8 or more hex"
                          " digits of its id, or 7 or more of a released commit")
    bit = lambda b, x: bool(lens[b].get(x))  # noqa: E731
    live = lambda x: bit("active", x) and not bit("stale", x)  # noqa: E731

    def step(x: bytes) -> Tuple[Dict[str, object], Optional[bytes]]:
        c = cells[x]
        kind = schema.get(c.h_schema, "custom")
        row: Dict[str, object] = {"cell": x.hex(), "name": slot(x), "schema": kind,
                                  "status": {b: bit(b, x) for b in WHY_BITS}, "because": []}
        say = row["because"].append
        if not bit("active", x):
            for b, field in (("invalidated", "h_invalidates"), ("retired", "h_retires"), ("superseded", "h_supersedes")):
                if bit(b, x):
                    src = [f"{slot(y)} ({'effective' if bit('effective', y) else 'not effective'})"
                           for y in sorted(cells) if x in hv(getattr(cells[y], field))]
                    say(f"{b}: an edge into it from {', '.join(src) or 'no cell of this store'}")
            if not bit("accepted", x):
                say("not accepted")
            return row, None
        if bit("stale", x):
            bad = [r for r in hv(c.h_relies) if not live(r)]
            if bad:
                say(f"stale: it relies on {slot(bad[0])}, which is not live")
                return row, bad[0]
            say("stale")
            return row, None
        if kind in EVALUATED and x in lens["evaluators"]:
            thr, evs = lens["evaluators"][x]
            counted, invalid = lens["endorsers"][x], lens["invalidators"][x]
            row["keys"] = {"threshold": thr, "of": len(evs), "counted": who(counted), "invalid": who(invalid),
                           "waiting": who(set(evs) - set(counted) - set(invalid))}
            say(f"{'Settled' if bit('settled', x) else 'Provisional'}: {len(counted)} of threshold {thr} "
                f"({len(evs)} keys) counted: {', '.join(who(counted)) or 'none'}")
            if row["keys"]["waiting"]:  # a Settled cell waits for no one; the keys that did not answer are still named
                say(f"{'not answered' if bit('settled', x) else 'waiting for'}: {', '.join(row['keys']['waiting'])}")
            if invalid:
                say(f"INVALID from: {', '.join(who(invalid))}")
        if kind == "projection":
            thr, hk = V.parse_pol1(atoms[c.slots[4]])
            keys = set(hv(hk))
            sealed = {s.actor_pubkey for s in seals.values() if s.h_target == x} & keys
            row["keys"] = {"threshold": thr, "of": len(keys), "counted": who(sealed), "invalid": [],
                           "waiting": who(keys - sealed)}
            say(f"{'witnessed' if bit('settled', x) else 'not witnessed'}: {len(sealed)} of threshold {thr} "
                f"({len(keys)} keys) sealed: {', '.join(who(sealed)) or 'none'}")
            if keys - sealed:
                say(f"{'not sealed' if bit('settled', x) else 'waiting for'}: {', '.join(who(keys - sealed))}")
        if bit("settled", x) and not bit("grounded", x):
            down = [r for r in hv(c.h_relies) if not bit("grounded", r)]
            if down:
                say(f"not Grounded: it relies on {slot(down[0])}, which is not Grounded")
                return row, down[0]
            wit = [w for w in sorted(set(lens["counted_witnesses"].get(x, {}).values())) if not bit("grounded", w)]
            if wit:
                say(f"not Grounded: too few keys count through Grounded witnesses; {slot(wit[0])} is not Grounded")
                return row, wit[0]
            say("not Grounded")
        return row, None

    path, x, seen = [], found[0], set()
    while x is not None and x not in seen:
        seen.add(x)
        row, x = step(x)
        path.append(row)
    return {"tip": tip, "path": path}


def explain_text(doc: Dict[str, object]) -> str:
    """`explain` (`why` on the command line) as lines a person reads: one block per cell of the path, its status and its reasons."""
    out = []
    for i, row in enumerate(doc["path"]):
        st = row["status"]
        state = ("live" if st["active"] and not st["stale"] else "not live") + \
            (", Settled" if st["settled"] else "") + (", Grounded" if st["grounded"] else ", not Grounded")
        out.append(f"{'  ' * i}{row['name']} ({row['schema']}): {state}")
        out += [f"{'  ' * i}  {b}" for b in row["because"]]
    return "\n".join(out)


NEXT_KINDS = ("attest", "withdraw", "witness", "cosign", "seal", "other")
NEXT_BITS = ("accepted", "invalidated", "effective", "retired", "superseded", "active", "stale", "settled", "grounded")
HYPOTHESIS = V.sha256(b"minds.next.hypothesis")  # the id `next` gives the one new cell of an act, in memory


class NextTip:
    """What `next` reads at the tip: the lens and the seals, the roster, the admission policy, and which edges have
    latched. Every act is read against these, in memory, or through the gate (`act_hypothesis`)."""

    def __init__(self, repo_dir: Path) -> None:
        self.repo_dir = repo_dir
        self.repo = V.GitVarsRepo(repo_dir)
        self.tip = self.repo.ref_commit(SCOPE)
        if self.tip is None:
            raise V.VarsError("no chain: run `init` first")
        self.lens = L = self.repo.lens(SCOPE)
        self.cells, self.atoms = L["cells"], L["atoms"]
        _, _, seals = self.repo.read_cas_tree(self.tip)
        self.names = key_names(self.cells, self.atoms, seals)
        self.scope = L["scope"]
        self.adm = self.pol(self.cells[self.scope].slots[0])
        self.keys = sorted(self.adm[1])
        self.latched = self.repo._evaluate_commit_chain(SCOPE, self.repo.commit_chain(self.tip))["latched_edge_auth"]

    def pol(self, h: bytes) -> Tuple[int, set]:
        thr, hv = V.parse_pol1(self.atoms[h])
        return thr, set(V.parse_hvec(self.atoms[hv], require_sorted=True))

    def hv(self, h: bytes) -> List[bytes]:
        return [] if h == V.H_EMPTY else V.parse_hvec(self.atoms[h], require_sorted=True)

    def name(self, x: bytes) -> str:
        return V.parse_utf8(self.atoms[self.cells[x].h_slot_name])

    def who(self, k: bytes) -> str:
        return f"{self.names.get(k, '?')} {k.hex()[:8]}"

    def live(self, x: bytes) -> bool:
        return bool(self.lens["active"].get(x)) and not self.lens["stale"].get(x)

    def wend(self, x: bytes) -> set:
        """The keys behind a local cell: every seal on it counts, late co-signatures too."""
        return self.lens["cumulative_endorsers"].get(x, set())

    def judged(self, d: bytes) -> bool:
        """A contract or decision without a computation: one an ACCEPT or an INVALID verdict alone can judge."""
        c = self.cells[d]
        return c.h_schema in (V.H_SCHEMA["contract"], V.H_SCHEMA["decision"]) and c.slots[1] == V.H_EMPTY

    def gate_only(self, x: bytes) -> bool:
        """A seal on `x` can move Pass 1 (an edge of `x` not yet latched, a scope or a schema not yet authorized), which
        `next` does not read in memory: such an act is read through the gate."""
        c = self.cells[x]
        edges = [(x, v, kind) for kind, h in (("invalidates", c.h_invalidates), ("retires", c.h_retires),
                                               ("supersedes", c.h_supersedes)) for v in self.hv(h)]
        return (any(e not in self.latched for e in edges)
                or (c.h_schema in (V.H_META_SCHEMA, V.H_SCHEMA["scope"]) and not self.lens["settled"].get(x)))

    def menu(self, every: bool = False) -> List[Dict[str, object]]:
        """The acts `next` reads: each one seal of one roster key. On a new verdict it files: `attest`, an ACCEPT under
        a verifier id of its own, on a contract or decision whose policy names it and that does not count it yet;
        `withdraw`, an INVALID under a verifier id it counts through. On a local cell already on the chain: `witness` a
        projection whose witness policy names it, `cosign` a verdict or an answer that counts for a cell whose policy
        names it, or an INVALID verdict on one, and `seal` a cell `gate_only` names. With `every`, also each other
        seal it has not made, on any cell of the chain, local or not (`other`), and an ACCEPT by a key no policy names:
        `next` reads those as changing nothing, which `check` holds to the gate."""
        L, cells = self.lens, self.cells
        acts: List[Dict[str, object]] = []
        local = lambda x: self.name(x).startswith(f"{SCOPE}/")  # noqa: E731
        for d in sorted((d for d in L["evaluators"] if local(d) and self.judged(d)), key=self.name):
            pks, counted = L["evaluators"][d][1], L["endorsers"][d]
            for k in self.keys:
                if every or (k in pks and k not in counted):
                    acts.append({"act": "attest", "key": k, "cell": d})
                for vid in sorted({cells[w].slots[2] for w, ks in L["counted_witnesses"][d].items() if k in ks}):
                    acts.append({"act": "withdraw", "key": k, "cell": d, "vid": vid})
        for x in sorted((x for x in cells if every or local(x)), key=self.name):
            for k in self.keys:
                if k in self.wend(x):
                    continue
                kind = self.seal_kind(x, k)
                if kind != "other" or every:
                    acts.append({"act": kind, "key": k, "cell": x})
        return acts

    def seal_kind(self, x: bytes, k: bytes) -> str:
        L, c = self.lens, self.cells[x]
        if self.gate_only(x):
            return "seal"
        if c.h_schema == V.H_SCHEMA["projection"]:
            return "witness" if k in self.pol(c.slots[4])[1] else "other"
        if any(x in ws and k in L["evaluators"][d][1] for d, ws in L["counted_witnesses"].items()):
            return "cosign"
        if (c.h_schema == V.H_SCHEMA["verdict"] and c.slots[1] == V.H_VERDICT_INVALID and self.live(x)
                and any(self.withdraws(x, d, w) and k in ws[w] for d, ws in L["counted_witnesses"].items() for w in ws)):
            return "cosign"
        return "other"

    def withdraws(self, b: bytes, d: bytes, w: bytes) -> bool:
        """Does an INVALID verdict `b` (live) withdraw its keys' endorsements of `d` through the witness `w`? Under the
        same verifier id, on `d` itself or on the checkpoint or cycle witness `w` names (§4.2 Pass 3, `Withdrawn`)."""
        cb, cw = self.cells[b], self.cells[w]
        return (self.cells[d].h_schema in (V.H_SCHEMA["contract"], V.H_SCHEMA["decision"])
                and cb.slots[2] == cw.slots[2]
                and (cb.h_payload == d or (cw.slots[0] != V.H_EMPTY and cb.slots[0] == cw.slots[0])))

    def withdrawn(self, d: bytes, w: bytes, k: bytes) -> bool:
        return any(cb.h_schema == V.H_SCHEMA["verdict"] and cb.slots[1] == V.H_VERDICT_INVALID and self.live(b)
                   and k in self.wend(b) and self.withdraws(b, d, w) for b, cb in self.cells.items())

    def predict(self, act: Dict[str, object]) -> Dict[str, object]:
        """What the act leaves, read in memory: Pass 3's tables changed by that one seal, Settled of the cells whose
        tables changed, and Grounded recomputed by the lens's own fixed point (`vars1.grounded_lfp`). A new local cell
        needs one seal by a key of the admission policy, at any threshold (§3 check 3). `refused`, or the status changes of the
        chain's cells (`proofs/Vars1/Pivot.lean`: an endorsement only adds Grounded cells, a withdrawal only takes)."""
        L, cells = self.lens, self.cells
        kind, k, x = act["act"], act["key"], act["cell"]
        if kind == "seal":
            raise ValueError("a seal `gate_only` names is read through the gate")
        settled, cw, order = dict(L["settled"]), dict(L["counted_witnesses"]), list(L["kernel_order"])
        relies = lambda c: [] if c == HYPOTHESIS else self.hv(cells[c].h_relies)  # noqa: E731
        touched: set = set()
        if kind in ("attest", "withdraw"):
            if k not in self.adm[1]:
                return {"refused": True}
            order.append(HYPOTHESIS)
            settled[HYPOTHESIS] = True  # a verdict that stands is Settled; it relies on nothing, so it is Grounded
            if kind == "attest" and k in L["evaluators"][x][1]:
                cw[x] = {**cw[x], HYPOTHESIS: {k}}
                touched.add(x)
            if kind == "withdraw":  # its INVALID verdict names no witness: it reaches `x` by its payload alone
                cw[x] = {w: (ks - {k} if cells[w].slots[2] == act["vid"] else ks) for w, ks in cw[x].items()}
                touched.add(x)
        elif kind == "witness":
            thr, pks = self.pol(cells[x].slots[4])
            settled[x] = self.live(x) and len((self.wend(x) | {k}) & pks) >= thr
        elif kind == "cosign":
            for d, ws in L["counted_witnesses"].items():
                pks = L["evaluators"][d][1]
                if x in ws and k in pks and (cells[d].h_schema == V.H_SCHEMA["question"] or not self.withdrawn(d, x, k)):
                    cw[d] = {**cw[d], x: cw[d][x] | {k}}
                    touched.add(d)
                if cells[x].h_schema == V.H_SCHEMA["verdict"] and cells[x].slots[1] == V.H_VERDICT_INVALID:
                    hit = [w for w in ws if self.withdraws(x, d, w)]
                    if hit:
                        cw[d] = {w: (ks - {k} if w in hit else ks) for w, ks in cw[d].items()}
                        touched.add(d)
        for d in touched:
            settled[d] = self.live(d) and len(set().union(*cw[d].values())) >= L["evaluators"][d][0]
        grounded = V.grounded_lfp(order, settled, relies, cw, L["evaluators"])
        flips = {x: {b: (bool(L[b].get(x)), bool(new.get(x))) for b, new in (("settled", settled), ("grounded", grounded))
                     if bool(L[b].get(x)) != bool(new.get(x))} for x in cells}
        return {"refused": False, "flips": {x: f for x, f in flips.items() if f}}

    def act_hypothesis(self, act: Dict[str, object]) -> Tuple[Dict[bytes, bytes], List[V.Cell], List[V.Seal]]:
        """The act as the gate reads it: its new verdict, if any, and its one seal, supposed (a zero signature)."""
        kind, k, x = act["act"], act["key"], act["cell"]
        atoms: Dict[bytes, bytes] = {}
        if kind not in ("attest", "withdraw"):
            return atoms, [], [V.Seal(h_target=x, h_scope_ctx=self.scope, actor_pubkey=k, signature=V.ZERO_SIGNATURE)]
        if kind == "attest":  # a verifier id of its own, which no INVALID verdict on the chain names
            used = {c.slots[2] for c in self.cells.values() if c.h_schema == V.H_SCHEMA["verdict"]}
            n = 0
            while V.sha256(V.atom_utf8(f"next/{k.hex()[:16]}/{n}")) in used:
                n += 1
            vid, outcome = _put(atoms, V.atom_utf8(f"next/{k.hex()[:16]}/{n}")), V.H_ATTESTED
        else:
            vid, outcome = act["vid"], V.H_VERDICT_INVALID
            atoms[vid] = self.atoms[vid]
        w = V.Cell(h_schema=V.H_SCHEMA["verdict"],
                   h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/next/{kind}/{x.hex()[:12]}/{k.hex()[:8]}")),
                   h_payload=x, h_attests=_put(atoms, V.atom_hvec([x])), slots=(V.H_EMPTY, outcome, vid))
        return atoms, [w], [V.Seal(h_target=w.id, h_scope_ctx=self.scope, actor_pubkey=k, signature=V.ZERO_SIGNATURE)]

    def through_gate(self, act: Dict[str, object]) -> Dict[str, object]:
        """The act through the gate (`GitVarsRepo.what_if`, its seal supposed): `refused`, or every status change of
        the chain's cells, all bits."""
        atoms, new, seals = self.act_hypothesis(act)
        try:
            rep = self.repo.what_if(SCOPE, atoms, new, seals, assume=True, statuses=True)
        except V.VarsError:
            return {"refused": True}
        flips = {}
        for h, row in rep.get("statuses", {}).items():
            b, a = row["before"], row["after"]
            flips[bytes.fromhex(h)] = {bit: (b[bit], a[bit]) for bit in b if b[bit] != a[bit]}
        return {"refused": False, "flips": flips}


def next_acts(repo_dir: Path, actor: Optional[str] = None) -> Dict[str, object]:
    """Read only: which single act of one roster key would change a status now, and which cells wait (`next`). Each
    act of the menu (`NextTip.menu`) is read in memory (`NextTip.predict`) or, for a seal that can move Pass 1, through
    the gate; the acts that change something are listed, the most cells first, gains before losses. `actor` (a key's
    name, or 8 or more hex digits of it) keeps that key's acts only."""
    t = NextTip(repo_dir)
    keys = t.keys
    if actor is not None:
        keys = [k for k in t.keys if t.names.get(k) == actor
                or (re.fullmatch(r"[0-9a-f]{8,64}", actor.lower()) and k.hex().startswith(actor.lower()))]
        if len(keys) != 1:  # a verifier id is free text: two keys can give the same one
            raise V.VarsError(f"{len(keys)} roster keys answer to {actor!r}"
                              + (f" ({', '.join(t.who(k) for k in keys)})" if keys else "")
                              + ": name one by its verifier id or 8 or more hex digits of it")
    menu = [a for a in t.menu() if a["key"] in keys]
    rows = []
    for act in menu:
        got = t.through_gate(act) if act["act"] == "seal" else t.predict(act)
        if got["refused"] or not got["flips"]:
            continue
        flips = [{"cell": x.hex(), "name": t.name(x), "bit": b, "before": ba[0], "after": ba[1]}
                 for x, f in sorted(got["flips"].items(), key=lambda kv: t.name(kv[0])) for b, ba in sorted(f.items())]
        row = {"act": act["act"], "key": act["key"].hex(), "who": t.who(act["key"]), "cell": act["cell"].hex(),
               "name": t.name(act["cell"]), "radius": len(got["flips"]),
               "gains": sum(1 for f in flips if f["after"]), "losses": sum(1 for f in flips if not f["after"]),
               "flips": flips}
        if "vid" in act:
            row["verifier"] = V.parse_utf8(t.atoms[act["vid"]])
        rows.append(row)
    rows.sort(key=lambda r: (-r["radius"], -r["gains"], NEXT_KINDS.index(r["act"]), r["name"], r["key"]))
    L = t.lens
    waiting = []
    for x in sorted(t.cells, key=t.name):
        if not t.live(x) or L["settled"].get(x):
            continue
        if x in L["evaluators"]:
            thr, pks = L["evaluators"][x]
            have = L["endorsers"][x]
        elif t.cells[x].h_schema == V.H_SCHEMA["projection"]:
            thr, pks = t.pol(t.cells[x].slots[4])
            have = t.wend(x) & pks
        else:
            continue
        waiting.append({"cell": x.hex(), "name": t.name(x), "threshold": thr,
                        "counted": [t.who(k) for k in sorted(have)], "waiting_for": [t.who(k) for k in sorted(pks - have)]})
    margins = {}
    for d in L["evaluators"]:
        if L["settled"].get(d) and t.judged(d):
            m = len(L["endorsers"][d]) - L["evaluators"][d][0]
            margins[m] = margins.get(m, 0) + 1
    return {"tip": t.tip, "keys": [t.who(k) for k in keys], "considered": len(menu), "waiting": waiting,
            "margins": {str(m): n for m, n in sorted(margins.items())}, "acts": rows}


def next_text(doc: Dict[str, object], top: int = 12) -> str:
    """`next` as lines a person reads: what waits, then each act that changes more than one cell, the most first, then
    the acts that change one cell each, counted by key and kind, then how much margin the Settled decisions keep."""
    w = doc["waiting"]
    out = [f"chain {doc['tip'][:12]}: " + (f"{len(w)} cells wait for an answer" if w else "nothing waits for an answer")]
    for x in w:
        out.append(f"  {x['name']}: {len(x['counted'])} of {x['threshold']}, waiting for {', '.join(x['waiting_for'])}")
    acts = doc["acts"]
    out.append(f"{len(acts)} of the {doc['considered']} acts of one key ({', '.join(doc['keys'])}) change a status")
    big = [r for r in acts if r["radius"] > 1]
    word = lambda f: f"{f['name']} {'gains' if f['after'] else 'loses'} {f['bit']}"  # noqa: E731
    for r in big[:top]:
        more = f", and {len(r['flips']) - 4} more" if len(r["flips"]) > 4 else ""
        via = f" under {r['verifier']}" if "verifier" in r else ""
        out.append(f"  {r['act']} by {r['who']} on {r['name']}{via}: {r['radius']} cells: "
                   + ", ".join(word(f) for f in r["flips"][:4]) + more)
    if len(big) > top:
        out.append(f"  ... and {len(big) - top} more that change more than one cell")
    groups: Dict[Tuple[str, str, str], List[str]] = {}
    for r in acts:
        if r["radius"] == 1:
            bits = " and ".join(sorted({f["bit"] for f in r["flips"]}, key=NEXT_BITS.index))
            way = "gives" if r["gains"] else "takes"
            groups.setdefault((r["act"], r["who"], f"{way} {bits}"), []).append(r["flips"][0]["name"])
    for (act, who, what), names in sorted(groups.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        shown = ", ".join(names[:3]) + (f", ... ({len(names)})" if len(names) > 3 else "")
        out.append(f"  {act} by {who}: {len(names)} act(s), each {what} of one cell: {shown}")
    if doc["margins"]:
        out.append("Settled contracts and decisions by margin (keys counted beyond the threshold): " +
                   ", ".join(f"{m}: {n}" for m, n in doc["margins"].items())
                   + "; at margin 0, one withdrawal by any key it counts unsettles it")
    return "\n".join(out)


def next_check(repo_dir: Path, every: bool = False) -> Dict[str, object]:
    """Hold `next` to the gate: every act of its menu (with `every`, every seal of every roster key on every local cell
    it has not sealed, and an ACCEPT by every key on every contract or decision) through `GitVarsRepo.what_if`, its
    seal supposed, against `next`'s reading. They agree when both refuse, or both admit and change the same bits of the
    same cells; the gate's bits are all of them, so a Pass 1 or Pass 2 change `next` does not read is a difference."""
    t = NextTip(repo_dir)
    menu = t.menu(every)
    differ, gate_read = [], 0
    for act in menu:
        gate = t.through_gate(act)
        if act["act"] == "seal":
            gate_read += 1
            continue
        mine = t.predict(act)
        if mine != gate:
            differ.append({"act": act["act"], "key": act["key"].hex(), "cell": act["cell"].hex(), "name": t.name(act["cell"]),
                           "next": _flips_json(mine), "gate": _flips_json(gate)})
    return {"tip": t.tip, "acts": len(menu), "read_by_the_gate": gate_read, "differ": differ}


def _flips_json(got: Dict[str, object]) -> object:
    if got["refused"]:
        return "refused"
    return {x.hex(): {b: list(ba) for b, ba in f.items()} for x, f in got["flips"].items()}


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


def unanswered(lens: Dict[str, object], cid: bytes) -> set:
    """The evaluators a release still waits for, as Pass 3 reads it: none once it is settled or no longer live;
    else its evaluators less those whose endorsement Pass 3 counts and those with a live INVALID on it (an INVALID
    is an answer)."""
    if lens["settled"].get(cid) or cid not in lens["evaluators"]:
        return set()
    return lens["evaluators"][cid][1] - lens["endorsers"][cid] - lens["invalidators"][cid]


def awaiting(repo_dir: Path, pk: bytes) -> List[bytes]:
    """The releases of the chain that wait for the verdict of `pk`, in the order the lens holds them."""
    repo = V.GitVarsRepo(repo_dir)
    lens = repo.lens(SCOPE)
    cells, atoms = lens["cells"], lens["atoms"]
    return [cid for cid, c in cells.items()
            if c.h_schema == V.H_SCHEMA["decision"] and V.parse_utf8(atoms[c.h_slot_name]).startswith(f"{SCOPE}/release/")
            and pk in unanswered(lens, cid)]


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
                       awaiting=sorted(k.hex() for k in unanswered(lens, cid)))
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
        # with an admission threshold of 1 and more than one key, each key alone is the quorum (spec §4.2)
        "admission": {"threshold": thresholds(repo)[0], "keys": len(keys),
                      "one_key_is_the_quorum": thresholds(repo)[0] == 1 and len(keys) > 1},
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


# Where a commit pins its rules identities: verify/minds_verify.py's KNOWN_RULES_TABLE (one row per line: id, encoding,
# name) from 2026-10-28 (7720290) on, and before that lines `H_LENS_KERNEL… = bytes.fromhex("…")` in vars1.py.
PIN_FILES = ("verify/minds_verify.py", "vars1.py")
PIN_TABLE = re.compile(r'^KNOWN_RULES_TABLE = """\n((?:[0-9a-f]{64} v[12] H_LENS_KERNEL\w*\n)+)"""\n', re.M)
PIN_LINE = re.compile(r'^(H_LENS_KERNEL(?:_V2|_V1B)?) = bytes\.fromhex\("([0-9a-f]{64})"\)$', re.M)


def commit_pins(root: Path) -> Dict[str, bytes]:
    """The rules identities a checkout's own sources pin, by constant name, from the first file of PIN_FILES that
    pins each (its table, else its pin lines). An older commit pins its own kernel: while v2 was being built, kernel2/
    and its pin moved together (7e1368bc at 63ceffd, 0276c165 at dddd3ae, 1ca798b5 from be482c9 on), and a release is
    checked against its own commit's pins."""
    out: Dict[str, bytes] = {}
    for name in PIN_FILES:
        f = root / name
        if not f.is_file():
            continue
        text = f.read_text(encoding="utf-8")
        table = PIN_TABLE.search(text)
        rows = ([(r.split(" ")[2], r.split(" ")[0]) for r in table.group(1).splitlines()] if table
                else [(m.group(1), m.group(2)) for m in PIN_LINE.finditer(text)])
        for label, h in rows:
            out.setdefault(label, bytes.fromhex(h))
    return out


def _run(cmd: List[str], cwd: Path, env: Optional[Dict[str, str]] = None) -> bool:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True,
                          env=None if env is None else {**os.environ, **env}).returncode == 0


# A test run requires what CI's check job requires: a skip for want of the chain or of a Lean executable would read as
# a pass. A commit whose tests predate these variables ignores them.
REQUIRE = {"MINDS_REQUIRE_CHAIN": "1", "MINDS_REQUIRE_LEAN": "1"}


def kernel_checks(root: Path, rules: bytes, run=_run) -> List[Tuple[str, bool]]:
    """Rebuild every rules module `root` carries (kernel/, kernel2/ and kernel/lens1b.wasm where present); each must
    hash to the identity `root`'s own sources pin (`commit_pins`; this verifier's pin where they pin none), and the
    rules the release names must be one of those rebuilt here. That last check is the one about the release: a module
    that rebuilds to its commit's pin and is not the released rules settles nothing."""
    results: List[Tuple[str, bool]] = []
    rebuilt = set()
    pins = commit_pins(root)
    for marker, d, extra, wasm_name, pinned, label in KERNELS:
        if not (root / marker).exists():
            continue
        want = pins.get(label, pinned)
        built = run(["cargo", "build", "--release", "--target", "wasm32-unknown-unknown", *extra], root / d)
        wasm = root / d / "target" / "wasm32-unknown-unknown" / "release" / wasm_name
        ok = built and wasm.exists() and V.sha256(wasm.read_bytes()) == want
        results.append((f"{marker} rebuild hashes to {label}" if extra else f"{d} rebuild hashes to {label}", ok))
        if ok:
            rebuilt.add(want)
    results.append(("the released rules are rebuilt here", rules in rebuilt))
    return results


def witness_checks(root: Path, run=_run, python: str = sys.executable) -> List[Tuple[str, bool]]:
    """The witness checkers of experiments/witness/README.md, where the commit carries them: `vars1witness` built
    where its proofs name it (from PR #50 on), then the witness suite (from PR #46 on) with the Lean checker and the
    chain required, as CI's check job runs it. Its test 13 holds every decision the lens settles on
    refs/vars/heads/minds as the checkout's refs hold it; under `verify-release`, the chain the release was recorded
    on. A commit from before them has none of these checks, so verifying an older release does not fail on them."""
    results: List[Tuple[str, bool]] = []
    if (root / "proofs" / "Vars1WitnessMain.lean").exists():
        results.append(("lake build vars1witness", run(["lake", "build", "vars1witness"], root / "proofs")))
    if (root / "experiments" / "witness" / "test_witness.py").exists():
        results.append(("experiments/witness", run([python, "experiments/witness/test_witness.py"], root, REQUIRE)))
    return results


def run_checks(root: Path, rules: bytes = V.H_LENS_KERNEL, python: str = sys.executable) -> Tuple[List[str], bool]:
    """Every check a release requires, as `name OK|FAILED` lines; the release is refused unless all pass. Every
    rules module built from `root` must hash to its identity, and `rules` must be one of them. The test suites run
    under `python`, which must have `root`'s requirements installed."""
    run = _run

    # The Lean executables first: properties I9, I10 and I12 run them, so in a fresh checkout they must exist
    results: List[Tuple[str, bool]] = []
    for target in ("", "vars1exec", "vars1fold", "vars1cycle", "Vars1Sigma"):
        results.append((f"lake build {target}".strip(), run(["lake", "build", *([target] if target else [])], root / "proofs")))
    results += [
        ("test_vars1", run([python, "-m", "unittest", "test_vars1"], root, REQUIRE)),
        ("test_vars1_props", run([python, "test_vars1_props.py"], root, REQUIRE)),
    ]
    results += witness_checks(root, run, python)
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


def claimed_checks(statement: str) -> List[str]:
    """The checks a release statement says passed, in its order: what a member who verifies it reruns and answers for."""
    m = re.search(r"; checks: (.*?)(?:; profile@[0-9a-f]{64})?\Z", statement)
    items = m.group(1).split("; ") if m and m.group(1) else []
    if not items:
        raise V.VarsError("a release statement that names no checks")
    for x in items:
        if not x.endswith(" OK"):
            raise V.VarsError(f"a release statement whose check {x!r} did not pass")
    return [x[:-len(" OK")] for x in items]


class Unreproducible(V.VarsError):
    """A release whose checks cannot be rerun as it ran them: a member records nothing, neither ATTESTED nor INVALID. Its
    message names what is missing."""


def unpinned_reads(repo_dir: Path, sha: str, pins: Optional[Dict[str, str]]) -> List[str]:
    """What the checks of a release of `sha` read that nothing pins: each sibling checkout (SIBLINGS) a file of the commit
    names by its path (`../sigma-glyph/`, `"sigma-glyph"`), when the commit is `UNPINNED_UNTIL` or one of its ancestors
    and the statement names no sibling commits. Releases of 2026-10-19 before a512f8b are such: they read
    `../sigma-glyph` as it happened to be. Empty when nothing is unpinned, so a check that fails there is a failure
    (INVALID). The set is history, not text: a commit outside it is answered by its checks whatever its files name, so
    a comment or a file nothing reads cannot turn a failing check into no verdict (Codex, finding 3da1bc22 on #96), and
    a commit made since whose checks still read a sibling fails them where nothing sits beside the checkout. Within it a
    name in a comment would count as well; the five releases' commits each read both siblings in code (proofs/
    lakefile.toml's `srcDir`, test_vars1.py's paths). Empty in a repository that does not hold `UNPINNED_UNTIL` or
    `sha`, which has no such commit."""
    if pins is not None:
        return []
    git = ["git", "-C", str(repo_dir)]
    if subprocess.run([*git, "merge-base", "--is-ancestor", sha, UNPINNED_UNTIL], capture_output=True).returncode != 0:
        return []
    reads = []
    for sib in SIBLINGS:
        g = subprocess.run([*git, "grep", "-n", "-E", rf'(\.\./|"){sib}(/|")', sha, "--", "*.py", "*.toml", "*.lean"],
                           capture_output=True, text=True)
        if g.returncode == 0 and g.stdout:
            _, path, line, _ = g.stdout.splitlines()[0].split(":", 3)
            reads.append(f"{sib} (read by {path}:{line})")
    return reads


def recorded_at(repo: V.GitVarsRepo, cid: bytes) -> str:
    """The commit of the chain that admitted cell `cid`: the chain as it stood when that cell was recorded."""
    chain = repo.commit_chain(repo.ref_commit(SCOPE))
    for commit, (_, cells, _) in zip(chain, repo.chain_deltas(chain)):
        if cid in cells:
            return commit
    raise V.VarsError("not a cell of this chain")


def interpreter_for(repo_dir: Path, requirements: Optional[bytes]) -> str:
    """The Python a commit's checks run under. This one, where the commit pins no requirements (its Book I came from
    the sibling checkouts beside it, put first on its path) or the bytes this checkout pins (and `vars1`, imported
    above, has checked the installed modules against its own pins). Otherwise one with exactly the commit's
    requirements installed (`pip install --require-hashes`, so only the files the commit names by hash), made once
    per requirements file under `.git/vars/envs/`: a release recorded on sigma-glyph 0.8.0 is checked on 0.8.0 by a
    verifier that runs 1.0.1, rather than refused by its own commit's check of the Book I bytes. One that cannot be
    made is an error, not a failed check: no verdict is recorded, since the release was not checked."""
    if requirements is None or requirements == (ROOT / "requirements.txt").read_bytes():
        return sys.executable
    env = Path(repo_dir) / ".git" / "vars" / "envs" / V.sha256(requirements).hex()
    if not (env / "ready").exists():
        if env.exists():
            shutil.rmtree(env)
        env.mkdir(parents=True)
        (env / "requirements.txt").write_bytes(requirements)
        made = (_run([sys.executable, "-m", "venv", str(env)], env)
                and _run([str(env / "bin" / "python"), "-m", "pip", "install", "--quiet", "--require-hashes", "-r",
                          "requirements.txt"], env))
        if not made:
            raise V.VarsError(f"cannot install the commit's requirements.txt (in {env}): the release is not checked")
        (env / "ready").write_bytes(b"")
    return str(env / "bin" / "python")


def checks_at(repo_dir: Path, sha: str, rules: bytes, siblings: Optional[Dict[str, str]] = None,
              chain: Optional[str] = None) -> Tuple[List[str], bool]:
    """Run every check on commit `sha` in a fresh checkout under `.git/vars/verify/`: a clone sharing this
    repository's objects, not a worktree, so that its refs are its own. They are this repository's `refs/vars/*`,
    except that `refs/vars/heads/minds` is `chain` when one is given: `verify-release` passes the chain as it stood
    when the release was recorded, so a member who joined or left since does not change what the checks read (test
    25 compares README's keys with the roster). A commit now carries its dependencies (sigma-glyph from PyPI by
    requirements.txt, run under `interpreter_for` that file; vendored Lean sources and vectors), so nothing sits
    beside the checkout. An older release that pinned sibling commits (`siblings`) gets each extracted at that commit
    beside it (read from the sibling repository with `git archive`), and Book I is compared with `SIGMA_PIN`. The
    checkout and any extracted siblings are removed afterwards."""
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
    # the checks run under the commit's own requirements, read from the commit; none before 2026-10-19 (a512f8b)
    req = f"{sha}:requirements.txt"
    pinned = subprocess.run(["git", "-C", str(repo_dir), "cat-file", "-e", req], capture_output=True).returncode == 0
    python = interpreter_for(repo_dir, subprocess.run(["git", "-C", str(repo_dir), "show", req], capture_output=True,
                                                      check=True).stdout if pinned else None)
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
        shutil.rmtree(wt)
    src = str(Path(repo_dir).resolve())
    git("clone", "-q", "--shared", "--no-checkout", "--no-tags", src, str(wt))
    try:
        sub = lambda *a: subprocess.run(["git", "-C", str(wt), *a], capture_output=True, text=True, check=True)
        sub("fetch", "-q", "--no-tags", src, "+refs/vars/*:refs/vars/*")
        if chain is not None:
            sub("update-ref", f"refs/vars/heads/{SCOPE}", chain)
        sub("checkout", "-q", "--detach", sha)
        lines, ok = run_checks(wt, rules, python=python)
    finally:
        shutil.rmtree(wt, ignore_errors=True)
        for sib in SIBLINGS:
            dst = base / sib
            if dst.exists() and not dst.is_symlink():
                shutil.rmtree(dst)
    return [f"{n} {'OK' if g else 'FAILED'}" for n, g in pre] + lines, ok and all(g for _, g in pre)


def witnessed_ref(pk: bytes) -> str:
    """The newest tip that projections this key sealed name: what it remembers of the one history (§4.4). A ref beside the
    chain's, so the commit stays reachable and a witness with no disk of its own keeps it where it keeps the chain."""
    return f"refs/vars/witnessed/{SCOPE}/{pk.hex()}"


def witnessed_tip(repo_dir: Path, pk: bytes) -> Optional[str]:
    out = subprocess.run(["git", "-C", str(repo_dir), "rev-parse", "--verify", "--quiet", witnessed_ref(pk)],
                         capture_output=True, text=True)
    return out.stdout.strip() if out.returncode == 0 else None


def remember_witnessed(repo_dir: Path, repo: "V.GitVarsRepo", pk: bytes, tip: str, named: Iterable[str]) -> None:
    """Remember the newest of the tips `named`, all on the chain up to `tip`. The memory only moves on: a tip it holds that
    is newer stays, since a commit the chain lost may have named more."""
    order = {c: i for i, c in enumerate(repo.commit_chain(tip))}
    newest = max(named, key=lambda t: order[t], default=None)
    last = witnessed_tip(repo_dir, pk)
    if newest is not None and (last is None or order[newest] > order.get(last, -1)):
        subprocess.run(["git", "-C", str(repo_dir), "update-ref", witnessed_ref(pk), newest], check=True)


def refuse_a_fork(repo_dir: Path, pk: bytes, tip: str) -> None:
    """A witness vouches for one history (§4.4), so it signs no projection on a chain that does not descend from the tips
    of the projections it signed before. Its ref is all it has: a clone that never fetched it is not protected by this."""
    last = witnessed_tip(repo_dir, pk)
    if last is None:
        return
    if subprocess.run(["git", "-C", str(repo_dir), "merge-base", "--is-ancestor", last, tip],
                      capture_output=True).returncode != 0:
        raise V.VarsError(f"this key sealed a projection of {last[:12]}, and this chain's tip {tip[:12]} does not descend "
                          "from it: sealing here would sign a fork")


def admit_sealing(repo_dir: Path, repo: "V.GitVarsRepo", pk: bytes, tip: str, commit: str, named: List[str]) -> None:
    """The one path of a commit whose seals include projections: refuse a fork, admit it, and remember the newest tip
    those projections name. Not the new commit, which a lost push race never publishes: what the key has said of the
    history is the tips it named, and the published chain can move on from them without this commit and be no fork."""
    refuse_a_fork(repo_dir, pk, tip)
    repo.admit_and_advance(SCOPE, commit, expected_old=tip)
    remember_witnessed(repo_dir, repo, pk, tip, named)


def verify_release(repo_dir: Path, sk: bytes, decision_id: bytes, name: str,
                   checks=checks_at) -> Tuple[str, bool, List[str]]:
    """As a roster member: run `checks` on the release's commit, record this member's verdict on the decision
    (ATTESTED if every check the statement claims passed again, else INVALID), and witness every projection that names
    this member's key and whose digests this host recomputes. Returns the new commit, the outcome and the claimed checks'
    lines. A check the statement does not claim is not part of the answer (a commit from before it has none to pass).

    A release whose checks cannot be rerun as they ran is answered by neither: `Unreproducible` is raised and nothing is
    recorded. That is a release whose checks read a sibling checkout nothing pins (`unpinned_reads`), decided before any
    check runs; one that claims a check this verifier does not run at its commit; or one whose commit fails a check
    this verifier runs there and the statement does not claim (an omission must not earn a seal). A claimed check that
    runs and fails, or a profile that is not the commit's, is INVALID, never unreproducible; an unclaimed check that
    passes is no part of the answer.

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
    statement = V.parse_utf8(atoms[d.h_payload])
    sha, rules, profile, pins = parse_release_profile(statement)
    claimed = claimed_checks(statement)
    unpinned = unpinned_reads(repo_dir, sha, pins)
    if unpinned:
        raise Unreproducible(f"not reproducible: the checks of main@{sha[:12]} read {', '.join(unpinned)}, which its "
                             "statement does not pin: the commit is from before the first requirements.txt (a512f8b)")
    then = recorded_at(repo, decision_id)  # the checks read the chain the release was recorded on
    # the lines carry the outcome (checks_at's flag is every line's and every pre-check line's), so the flag is not read
    ran, _ = (checks(repo_dir, sha, rules, siblings=pins, chain=then) if pins
              else checks(repo_dir, sha, rules, chain=then))
    got = {line.rsplit(" ", 1)[0]: line.rsplit(" ", 1)[-1] == "OK" for line in ran}
    lines = [f"{n} {'OK' if got[n] else 'FAILED'}" for n in claimed if n in got]
    ok = all(got[n] for n in claimed if n in got)
    if profile is not None:  # the files the release names are the files at its commit, recomputed here
        try:
            same = profile_at(repo_dir, sha)["id"] == profile
        except V.VarsError:
            same = False
        lines = lines + [f"release profile {profile[:12]} is the commit's {'OK' if same else 'FAILED'}"]
        ok = ok and same
    if ok:  # a claim that failed is INVALID whatever else holds; short of that, what cannot be settled is no verdict
        missing = [n for n in claimed if n not in got]
        if missing:
            raise Unreproducible(f"not reproducible: the statement claims {missing}, which this verifier does not run "
                                 f"at main@{sha[:12]}")
        unclaimed = [n for n, passed in got.items() if not passed]
        if unclaimed:
            raise Unreproducible(f"not reproducible: this verifier runs {unclaimed} at main@{sha[:12]}, which fail there, "
                                 "and the statement does not claim them: leaving a check out cannot be told from a "
                                 "commit that did not have it, so it earns no verdict")
    s = governing_scope(repo)
    new: Dict[bytes, bytes] = {}
    base = f"{V.parse_utf8(atoms[d.h_slot_name])}/{name}/{'attested' if ok else 'invalid'}"
    grounds = check_cells(new, base, lines, sha, profile)  # this member's own checks: its verdict rests on them
    verdict = V.Cell(
        h_schema=V.H_SCHEMA["verdict"],
        h_slot_name=_put(new, V.atom_utf8(base)),
        h_payload=decision_id,
        h_attests=_put(new, V.atom_hvec([decision_id])),
        h_relies=_put(new, V.atom_hvec([g.id for g in grounds])),
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
    c = repo.build_candidate_commit(SCOPE, new, [*grounds, verdict],
                                    [V.Seal.sign(sk, x, s) for x in [*(g.id for g in grounds), verdict.id, *witness]],
                                    parent_commit=tip)
    admit_sealing(repo_dir, repo, pk, tip, c, [V.parse_utf8(atoms[cells[x].slots[0]]) for x in witness])
    return c, ok, lines


def witness(repo_dir: Path, sk: bytes, name: str, checks=checks_at) -> List[Dict[str, Optional[str]]]:
    """As a member on a host of its own (the GitHub Actions witness, `.github/workflows/witness.yml`, whose key is
    made on its runner and never leaves GitHub): `verify-release` every release that waits for this key's verdict,
    one after another. A key not on the roster, or one every release has its answer from, has nothing to do.
    A release this key answered before (a verdict it sealed whose attests name the release) and that still waits
    for it in Pass 3 has lost that answer since: withdrawn (superseded by NOT_ASSESSED), or stale. Answering it
    again is the member's own act, and `verify-release` could only remake the verdict the chain has: it is left to
    the member, as ANSWERED_BEFORE, and the others are verified (Codex, finding 83a5c151 on PR #36). A verdict that
    attests nothing is no answer (finding 37972d20). Returns each decision, its outcome and the chain commit that
    records it (none for ANSWERED_BEFORE)."""
    pk = V.ed25519_pubkey(sk)
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    refuse_a_fork(repo_dir, pk, tip)  # before anything else: a rewritten chain is refused even with nothing to answer
    atoms, cells, seals = repo.read_cas_tree(tip)
    # what the chain itself shows this key sealed, so a key that has answered before starts with its memory
    sealed = {V.parse_utf8(atoms[cells[x.h_target].slots[0]]) for x in seals.values()
              if x.actor_pubkey == pk and x.h_target in cells and cells[x.h_target].h_schema == V.H_SCHEMA["projection"]}
    remember_witnessed(repo_dir, repo, pk, tip, sealed)
    mine = [cells[x.h_target] for x in seals.values()
            if x.actor_pubkey == pk and x.h_target in cells and cells[x.h_target].h_schema == V.H_SCHEMA["verdict"]]
    answered = {d for v in mine if v.h_attests != V.H_EMPTY for d in V.parse_hvec(atoms[v.h_attests])}
    out: List[Dict[str, Optional[str]]] = []
    for d in awaiting(repo_dir, pk):
        if d in answered:
            out.append({"decision": d.hex(), "verdict": "ANSWERED_BEFORE", "commit": None})
            continue
        try:
            commit, ok, _ = verify_release(repo_dir, sk, d, name, checks=checks)
        except Unreproducible as e:  # recorded by no one: the release keeps waiting for this key, and says why
            out.append({"decision": d.hex(), "verdict": "UNREPRODUCIBLE", "commit": None, "why": str(e)})
            continue
        out.append({"decision": d.hex(), "verdict": "ATTESTED" if ok else "INVALID", "commit": commit})
    return out


# The cosigner. At an admission threshold of 2 a rotation of the scope needs a second member's seal (§3 check 3). The
# GitHub Actions witness gives it to a raise of the threshold another member proposed, judging form and time, not merit:
# - form: the proposal is exactly a `threshold` of the governing scope now, rebuilt here as that command builds it, to a
#   threshold above the one it has and no higher than a majority of the roster, and another member sealed it;
# - time: this key first saw it COSIGN_WINDOW ago;
# - no veto: nobody has put a ref at refs/vars/veto/minds/<its cell>, and this key never saw one there.
# It seals only what tightens. A second seal on a join or on a lower threshold would let one member pass the threshold
# alone: join a second key of its own, or lower it to 1, then act with no one (the analysis session, review of PR #95).
# Those take the members' own seals, and so does a rules change, which is bound to the tip its shadow replay read.
PROPOSALS = f"refs/vars/proposals/{SCOPE}/"
VETOES = f"refs/vars/veto/{SCOPE}/"
# Seconds from this key's first sight of a proposal. A raise is never urgent and can neither weaken the chain nor, up
# to a majority, stop it; the window is the time to see a mistaken one and veto it, and a day is enough for that.
COSIGN_WINDOW = 24 * 3600
LEDGER_FORMAT = "minds.cosign-ledger@1"
_HEX64 = re.compile(r"[0-9a-f]{64}")
_MALFORMED = (V.VarsError, subprocess.CalledProcessError, KeyError, IndexError, TypeError, ValueError, UnicodeDecodeError)


def proposal_ref(cell_id: bytes) -> str:
    return PROPOSALS + cell_id.hex()


def cosign_ref(pk: bytes) -> str:
    """The ref the cosigner `pk` keeps its ledger in, beside the chain (`read_ledger`)."""
    return f"refs/vars/cosign/{SCOPE}/{pk.hex()}"


def _refs(repo_dir: Path, prefix: str) -> Dict[str, str]:
    """The refs under `prefix`: their names after it, and what each points at."""
    out = subprocess.run(["git", "-C", str(repo_dir), "for-each-ref", "--format=%(refname) %(objectname)", prefix],
                         capture_output=True, text=True, check=True).stdout
    return {ref[len(prefix):]: oid for ref, oid in (line.split(" ") for line in out.splitlines())}


def _signed(doc: Dict[str, object]) -> bytes:
    """The bytes a ledger's signature signs: every member of the document but the signature, as canonical JSON."""
    return LEDGER_FORMAT.encode() + b"\x00" + json.dumps(doc, sort_keys=True, separators=(",", ":")).encode()


def read_ledger(repo_dir: Path, pk: bytes) -> Dict[str, Dict[str, object]]:
    """What the cosigner `pk` remembers: `{cell: {"seen": unix seconds of its first sight, "vetoed": bool}}`, in the message
    of the commit at `cosign_ref`, signed by `pk`. Whoever can push can move that ref, so the ledger counts only under this
    key's own signature, and one that does not verify is refused rather than read as empty. A missing ledger is empty:
    every window starts again, which delays a rotation and never hastens one."""
    out = subprocess.run(["git", "-C", str(repo_dir), "rev-parse", "--verify", "--quiet", cosign_ref(pk)],
                         capture_output=True, text=True)
    if out.returncode != 0:
        return {}
    raw = subprocess.run(["git", "-C", str(repo_dir), "cat-file", "commit", out.stdout.strip()], capture_output=True,
                         check=True).stdout
    try:
        doc = json.loads(raw.split(b"\n\n", 1)[1])
        if V.ed25519_verify(pk, _signed({k: v for k, v in doc.items() if k != "signature"}), bytes.fromhex(doc["signature"])):
            return doc["proposals"]
    except (ValueError, KeyError, IndexError, TypeError, AttributeError):
        pass
    raise V.VarsError(f"the cosign ledger at {cosign_ref(pk)} is not signed by this key: refusing to cosign")


def write_ledger(repo_dir: Path, sk: bytes, proposals: Dict[str, Dict[str, object]]) -> str:
    """Sign `proposals` and move `cosign_ref` to a commit holding them, the previous ledger its parent."""
    pk = V.ed25519_pubkey(sk)
    doc: Dict[str, object] = {"format": LEDGER_FORMAT, "key": pk.hex(), "proposals": proposals}
    doc["signature"] = V.ed25519_sign(sk, _signed(doc)).hex()
    git = ["git", "-C", str(repo_dir)]
    tree = subprocess.run([*git, "mktree"], input="", capture_output=True, text=True, check=True).stdout.strip()
    last = subprocess.run([*git, "rev-parse", "--verify", "--quiet", cosign_ref(pk)], capture_output=True, text=True)
    cmd = [*git, "commit-tree", tree, "-m", json.dumps(doc, sort_keys=True, separators=(",", ":"))]
    if last.returncode == 0:
        cmd += ["-p", last.stdout.strip()]
    commit = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout.strip()
    subprocess.run([*git, "update-ref", cosign_ref(pk), commit], check=True)
    return commit


def proposed_act(repo: V.GitVarsRepo, commit: str, cell_id: bytes) -> Tuple[Dict[bytes, bytes], V.Cell, bytes, List[V.Seal]]:
    """The proposal at `commit`, if it is what a cosigner may seal: `(atoms, cell, the scope it supersedes, its seals on the
    cell)`. It must be a `threshold` of the roster as it is, to a threshold above the one the scope has and no higher than
    `majority` of the roster, and the cell rebuilt here from the governing scope now, as `threshold` checks and builds it,
    must be the proposed cell to the byte. Anything else is refused, and so is a proposal from before a rotation: it
    supersedes a scope that no longer governs."""
    atoms, cells, seals = repo.read_cas_tree(commit)
    cell = cells.get(cell_id)
    if cell is None or cell.h_schema != V.H_SCHEMA["scope"]:
        raise V.VarsError("the proposal holds no scope cell of its name")
    keys = roster(repo)
    t, hv = V.parse_pol1(atoms[cell.slots[0]])
    if V.parse_hvec(atoms[hv], require_sorted=True) != keys:
        raise V.VarsError("cosign seals only a raise of the threshold: a join or any change of the roster takes the "
                          "members' own seals")
    k, a, c, say = _threshold_act(repo, t)
    if t <= max(thresholds(repo)):
        raise V.VarsError(f"cosign seals only a raise of the threshold: {t} does not raise it, and lowering it takes the "
                          "members' own seals")
    if t > majority(len(keys)):
        raise V.VarsError(f"cosign raises the threshold to a majority of the roster at most, {majority(len(keys))} of "
                          f"{len(keys)}: above it one member who stops answering stops every rotation")
    built_atoms, built, s = _rotation(repo, k, a, c, say)
    if built.id != cell_id:
        raise V.VarsError("the proposal is not the raise it reads as, built from the governing scope now")
    return built_atoms, built, s, [x for x in seals.values() if x.h_target == cell_id and x.h_scope_ctx == s]


def cosign(repo_dir: Path, sk: bytes, now: Optional[int] = None) -> List[Dict[str, object]]:
    """As a member on a host of its own (the GitHub Actions witness): give the second seal to each proposal that has waited
    its window, and admit it. Each proposal at refs/vars/proposals/minds/<cell> is, by name order:
    - VETOED: a ref refs/vars/veto/minds/<cell> is there, or this key saw one there once (the ledger remembers it);
    - ON_CHAIN: its cell is on the chain already;
    - REFUSED: not exactly a raise of the threshold of the governing scope now, up to a majority (`proposed_act`), no
      other member's seal on it, or refused by the gate;
    - WAITING: this key first saw it less than COSIGN_WINDOW ago;
    - COSIGNED: sealed by this key with the other members' seals, admitted by the gate, and the chain moved.
    The first sight of each proposal is recorded in this key's signed ledger (`read_ledger`); a proposal whose ref is gone
    (withdrawn) leaves it, unless it was vetoed. No key that remembers a history seals on a fork of it."""
    now = int(time.time()) if now is None else now
    pk = V.ed25519_pubkey(sk)
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    refuse_a_fork(repo_dir, pk, tip)
    if pk not in roster(repo):
        raise V.VarsError("this key is not on the roster; a member must `join` it first")
    ledger = read_ledger(repo_dir, pk)
    proposed, vetoed = _refs(repo_dir, PROPOSALS), set(_refs(repo_dir, VETOES))
    book = {h: dict(e) for h, e in ledger.items() if e["vetoed"] or h in proposed}
    out: List[Dict[str, object]] = []
    for name, commit in sorted(proposed.items()):
        if not _HEX64.fullmatch(name):
            out.append({"proposal": name, "outcome": "REFUSED", "why": "not named by a scope cell id"})
            continue
        entry = book.setdefault(name, {"seen": now, "vetoed": False})
        entry["vetoed"] = entry["vetoed"] or name in vetoed
        row: Dict[str, object] = {"proposal": name, "seen": entry["seen"]}
        if entry["vetoed"]:
            out.append({**row, "outcome": "VETOED"})
            continue
        cid = bytes.fromhex(name)
        if cid in repo.read_cas_tree(tip)[1]:
            del book[name]
            out.append({**row, "outcome": "ON_CHAIN"})
            continue
        try:
            atoms, cell, s, seals = proposed_act(repo, commit, cid)
            members = roster(repo)
            others = [x for x in seals if x.actor_pubkey in members and x.actor_pubkey != pk]  # read: signatures hold
            if not others:
                raise V.VarsError("no other member sealed it: a cosign is a second seal")
        except _MALFORMED as e:
            out.append({**row, "outcome": "REFUSED", "why": str(e)})
            continue
        if now < entry["seen"] + COSIGN_WINDOW:
            out.append({**row, "outcome": "WAITING", "until": entry["seen"] + COSIGN_WINDOW})
            continue
        c = repo.build_candidate_commit(SCOPE, atoms, [cell], [*others, V.Seal.sign(sk, cid, s)], parent_commit=tip)
        try:
            repo.admit_and_advance(SCOPE, c, expected_old=tip)
        except V.VarsError as e:
            out.append({**row, "outcome": "REFUSED", "why": f"the gate: {e}"})
            continue
        tip = c
        del book[name]
        out.append({**row, "outcome": "COSIGNED", "commit": c})
    if book != ledger:
        write_ledger(repo_dir, sk, book)
    return out


def what_if_args(repo_dir: Path, args: List[str]) -> Tuple[List[bytes], Optional[bytes], Optional[bytes]]:
    """`what-if CELL... [--key FILE | --assume PUBKEY] [--restore]`: the cells, the seed that seals the hypothesis
    (FILE, a member's own key, else the maintainer key if it exists) and, with `--assume`, no seed but the public
    key whose seals are supposed. Nothing is created: a missing key is a refusal. `--restore` is read by the
    caller."""
    args = [x for x in args if x != "--restore"]
    if "--assume" in args:
        i = args.index("--assume")
        if "--key" in args:
            raise V.VarsError("--assume and --key exclude each other: an assumed hypothesis is sealed by no key")
        if i + 1 >= len(args) or not re.fullmatch(r"[0-9a-f]{64}\Z", args[i + 1]):
            raise V.VarsError("--assume needs a public key (64 lowercase hex digits)")
        pk, args = bytes.fromhex(args[i + 1]), args[:i] + args[i + 2:]
        return _cell_args(args), None, pk
    if "--key" in args:
        i = args.index("--key")
        if i + 1 >= len(args):
            raise V.VarsError("--key needs a file")
        key, args = Path(args[i + 1]), args[:i] + args[i + 2:]
    else:
        key = key_path(repo_dir)
    if not key.is_file():
        raise V.VarsError(f"no key at {key}: pass --key FILE (a member's own seed) or --assume PUBKEY")
    return _cell_args(args), bytes.fromhex(key.read_text().strip()), None


def _cell_args(args: List[str]) -> List[bytes]:
    if not args:
        raise V.VarsError("what-if needs at least one cell id")
    cells = []
    for a in args:
        if not re.fullmatch(r"[0-9a-f]{64}\Z", a):
            raise V.VarsError(f"{a[:80]!r} is not a cell id (64 lowercase hex digits)")
        cells.append(bytes.fromhex(a))
    return cells


def what_if(repo_dir: Path, sk: Optional[bytes], cells: List[bytes], name: str = "", restore: bool = False,
            assume: Optional[bytes] = None) -> Dict[str, object]:
    """What would follow if `cells` were invalidated now: a hypothesis cell invalidating them, sealed by `sk` (a key
    on the roster), run through `GitVarsRepo.what_if`: checked by the gate, no ref moved, nothing filed on the chain.
    The candidate commit's objects stay in the object store, unreachable, until git's gc removes them.

    With `restore`, the signer also supposes it re-ran each of its own checks that the hypothesis invalidates: for
    every verdict sealed by `sk` that relies on one, a replacement check (`<check>/again`) and a replacement verdict
    (`<verdict>/again`) relying on its other grounds and the replacement, both sealed by `sk`. Only the signer's own
    verdicts are replaced; that nobody's standing is restored with another's key is Pass 3's, which counts the key
    that seals a verdict, not its name.

    With `assume` (a public key) in place of `sk`, nothing is signed: every seal names `assume` and carries a zero
    signature, and `GitVarsRepo.what_if` checks the hypothesis as if that key had sealed it (`mode: assumed`)."""
    repo = V.GitVarsRepo(repo_dir)
    tip = repo.ref_commit(SCOPE)
    t_atoms, t_cells, t_seals = repo.read_cas_tree(tip)
    atoms: Dict[bytes, bytes] = {}
    label = name or "-".join(c.hex()[:12] for c in cells)
    hyp = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=_put(atoms, V.atom_utf8(f"{SCOPE}/what-if/{label}")),
                 h_payload=_put(atoms, V.atom_utf8("suppose these fail")),
                 h_invalidates=_put(atoms, V.atom_hvec(sorted(cells))))
    new = [hyp]
    if restore:
        pk = assume if assume is not None else V.ed25519_pubkey(sk)
        mine = {x.h_target for x in t_seals.values() if x.actor_pubkey == pk}
        relies = lambda c: [] if c.h_relies == V.H_EMPTY else V.parse_hvec(t_atoms[c.h_relies], require_sorted=True)
        for vid, v in sorted(t_cells.items()):
            if v.h_schema != V.H_SCHEMA["verdict"] or vid not in mine or not set(relies(v)) & set(cells):
                continue
            grounds = []
            for g in relies(v):
                if g not in cells:
                    grounds.append(g)
                    continue
                again = V.Cell(h_schema=V.H_SCHEMA["axiom"],
                               h_slot_name=_put(atoms, V.atom_utf8(V.parse_utf8(t_atoms[t_cells[g].h_slot_name]) + "/again")),
                               h_payload=_put(atoms, V.atom_utf8(V.parse_utf8(t_atoms[t_cells[g].h_payload]) + " (run again)")))
                new.append(again)
                grounds.append(again.id)
            new.append(V.Cell(h_schema=V.H_SCHEMA["verdict"],
                              h_slot_name=_put(atoms, V.atom_utf8(V.parse_utf8(t_atoms[v.h_slot_name]) + "/again")),
                              h_payload=v.h_payload, h_attests=v.h_attests,
                              h_relies=_put(atoms, V.atom_hvec(sorted(grounds))), slots=v.slots))
    for c in new:  # the atoms the replacements reuse from the chain travel with them
        for h in (c.h_payload, c.h_attests, *c.slots):
            if h in t_atoms:
                atoms.setdefault(h, t_atoms[h])
    s = governing_scope(repo)
    if assume is not None:
        return repo.what_if(SCOPE, atoms, new, [V.Seal(h_target=c.id, h_scope_ctx=s, actor_pubkey=assume,
                                                       signature=V.ZERO_SIGNATURE) for c in new], assume=True)
    return repo.what_if(SCOPE, atoms, new, [V.Seal.sign(sk, c.id, s) for c in new])


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
        checks, ok = checks_at(repo_dir, main_sha, governing_rules(V.GitVarsRepo(repo_dir)))  # fresh checkout
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
    if cmd in ("join", "threshold") and len(argv) >= 2:
        propose = cmd == "threshold" and argv[-1] == "--propose"
        argv = argv[:-1] if propose else argv
        rest = argv[3:] if cmd == "join" else argv[2:]
        files = rest[1::2]
        if rest[0::2] != ["--key"] * len(files) or len(rest) % 2 or (cmd == "join" and len(argv) < 3):
            raise SystemExit(__doc__)
        sks = [bytes.fromhex(Path(f).read_text().strip()) for f in files] or [load_or_create_key(repo_dir)]
        print(join(repo_dir, sks, bytes.fromhex(argv[1]), argv[2]) if cmd == "join"
              else set_threshold(repo_dir, sks, int(argv[1]), propose=propose))
        return 0
    if cmd == "cosign" and len(argv) == 3 and argv[1] == "--key":
        print(json.dumps(cosign(repo_dir, bytes.fromhex(Path(argv[2]).read_text().strip())), indent=2))
        return 0
    if cmd == "cosign-ref" and len(argv) == 3 and argv[1] == "--key":
        print(cosign_ref(V.ed25519_pubkey(bytes.fromhex(Path(argv[2]).read_text().strip()))))
        return 0
    if cmd == "verify-release" and len(argv) == 6 and argv[2] == "--key" and argv[4] == "--name":
        sk = bytes.fromhex(Path(argv[3]).read_text().strip())
        try:
            commit, ok, lines = verify_release(repo_dir, sk, bytes.fromhex(argv[1]), argv[5])
        except Unreproducible as e:
            print(json.dumps({"commit": None, "verdict": "UNREPRODUCIBLE", "why": str(e)}))
            return 3
        print("\n".join(lines))
        print(json.dumps({"commit": commit, "verdict": "ATTESTED" if ok else "INVALID"}))
        return 0 if ok else 1
    if cmd == "witness" and len(argv) == 5 and argv[1] == "--key" and argv[3] == "--name":
        done = witness(repo_dir, bytes.fromhex(Path(argv[2]).read_text().strip()), argv[4])
        print(json.dumps(done, indent=2))
        # ANSWERED_BEFORE is the member's to answer; UNREPRODUCIBLE is no failure of the release, and waits as it is
        return 1 if any(x["verdict"] == "INVALID" for x in done) else 0
    if cmd == "shadow" and len(argv) in (2, 4) and argv[2:3] in ([], ["--out"]):
        doc = json.dumps(shadow(repo_dir, bytes.fromhex(argv[1])), indent=2)
        if len(argv) == 4:
            Path(argv[3]).write_text(doc + "\n")
        print(doc)
        return 0
    if cmd == "change-rules" and len(argv) >= 5 and argv[3] == "--manifest":
        kind, new_rules = argv[1], bytes.fromhex(argv[2])
        pairs = list(zip(argv[5::2], argv[6::2]))
        opts = dict(pairs)
        files = [v for k, v in pairs if k == "--key"]
        sks = [bytes.fromhex(Path(f).read_text().strip()) for f in files] or [load_or_create_key(repo_dir)]
        fields: Dict[str, object] = {}
        if kind == "correction":
            fields = {k: opts[f"--{k.replace('_', '-')}"] for k in
                      ("counterexample_scope", "counterexample", "cell", "status", "right")}
        elif kind in ("hardening", "tightening"):
            fields = {"input": Path(opts["--input"]).read_bytes(), "budget": opts["--budget"], "refusal": opts["--refusal"]}
        manifest = json.loads(Path(argv[4]).read_text())
        print(change_rules(repo_dir, sks, kind, new_rules, manifest, opts.get("--accept"), **fields))
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
    if cmd == "what-if" and len(argv) >= 2:
        cells, sk, pk = what_if_args(repo_dir, argv[1:])
        print(json.dumps(what_if(repo_dir, sk, cells, restore="--restore" in argv, assume=pk), indent=2))
        return 0
    if cmd == "power" and len(argv) == 2:
        repo = V.GitVarsRepo(repo_dir)
        print(json.dumps(repo.power(SCOPE, bytes.fromhex(argv[1])), indent=2))
        return 0
    if cmd == "next":
        flags, actor, rest = set(), None, list(argv[1:])
        while rest and (rest[0] in ("--json", "--check", "--every") or (rest[0] == "--actor" and len(rest) > 1
                                                                          and actor is None)):
            if rest[0] == "--actor":
                actor, rest = rest[1], rest[2:]
            else:
                flags.add(rest.pop(0))
        if not rest:
            if "--check" in flags:
                doc = next_check(repo_dir, every="--every" in flags)
                print(json.dumps(doc, indent=2))
                return 1 if doc["differ"] else 0
            doc = next_acts(repo_dir, actor)
            print(json.dumps(doc, indent=2) if "--json" in flags else next_text(doc))
            return 0
    if cmd == "why" and len(argv) in (2, 3) and argv[2:] in ([], ["--json"]):
        doc = explain(repo_dir, argv[1])
        print(json.dumps(doc, indent=2) if argv[2:] else explain_text(doc))
        return 0
    if cmd == "lag" and len(argv) == 3:
        print(json.dumps(V.lag(V.GitVarsRepo(repo_dir), SCOPE, V.GitVarsRepo(Path(argv[1])), argv[2]), indent=2))
        return 0
    if cmd == "witnessed-ref" and len(argv) == 3 and argv[1] == "--key":
        print(witnessed_ref(V.ed25519_pubkey(bytes.fromhex(Path(argv[2]).read_text().strip()))))
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
    try:
        sys.exit(_main(sys.argv[1:]))
    except V.VarsError as e:  # a refusal, said in one line; the exit code stays the 1 of an uncaught exception
        print(f"minds_chain: {e}", file=sys.stderr)
        sys.exit(1)
