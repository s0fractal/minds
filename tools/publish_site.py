#!/usr/bin/env python3
"""The release check site: the page, the JavaScript verifier, the rules modules and the live chain's bundles.

    .venv/bin/python tools/publish_site.py OUT      # write the site into OUT (a checkout of the `site` branch)

What it writes, at stable paths:
- `index.json` (`minds.published-bundles@1`): the chain's tip, the published projection and release, the roster with
  each key's name, the rules modules, the verifier, each file with its SHA-256;
- `bundles/projection-<id>.json`: the newest witnessed projection, with its input and output (`minds_chain.py bundle`);
- `bundles/attestation-<decision>.json`: the newest release whose attestation at that projection is accepted under
  the bundle's own policy (`minds_chain.py attest`, at that projection), checked here with minds_verify.py;
- `rules/<id>.wasm`: every rules module the verifier interprets, named by its SHA-256 (the page runs one with
  `--kernel`, and the verifier uses it only when its hash is the projection's rules);
- `index.html`, `page.mjs`, `style.css` (site/), and `minds_verify.mjs` (verify/), as of this checkout's commit.

Older bundle files in OUT stay: a reader who kept a link keeps the bytes. The index is the publisher's word, not a
trust anchor: the page asks the reader to pin keys, and the verifier counts only those. Nothing here signs or pushes.
"""
from __future__ import annotations

import datetime
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import vars1 as V  # noqa: E402
import minds_chain as MC  # noqa: E402

SCOPE = MC.SCOPE
RULES_FILES = {V.H_LENS_KERNEL: ROOT / "kernel" / "lens.wasm", V.H_LENS_KERNEL_V1B: ROOT / "kernel" / "lens1b.wasm",
               V.H_LENS_KERNEL_V2: ROOT / "kernel2" / "lens2.wasm"}


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _write(out: Path, rel: str, data: bytes) -> dict:
    (out / rel).parent.mkdir(parents=True, exist_ok=True)
    (out / rel).write_bytes(data)
    return {"file": rel, "sha256": _sha(data)}


def publish(out: Path) -> dict:
    repo = V.GitVarsRepo(ROOT)
    chain = repo.commit_chain(repo.ref_commit(SCOPE))
    lens = repo.lens(SCOPE)
    cells, atoms = lens["cells"], lens["atoms"]
    projections = []
    for cid, c in cells.items():
        if c.h_schema == V.H_SCHEMA["projection"] and lens["settled"].get(cid):
            tip = V.parse_utf8(atoms[c.slots[0]])
            if tip in chain:
                projections.append((chain.index(tip), cid, tip))
    if not projections:
        raise SystemExit("no witnessed projection on the chain")
    _, pid, ptip = max(projections)
    proj = V.export_projection(repo, SCOPE, pid)
    ki = V.parse_kernel_input(bytes.fromhex(proj["input"]), V.verify_projection(proj)["explain"]["rules"]["encoding"])
    # newest first, by the commit each was born at: the input's cell order is not the order of birth
    decisions = sorted(((c["birth"], c["id"]) for c in ki["cells"] if c["schema"] == V.H_SCHEMA["decision"]
                        and V.parse_utf8(atoms[cells[c["id"]].h_slot_name]).startswith(f"{SCOPE}/release/")),
                       reverse=True)
    chosen = None
    for _, did in decisions:
        att = json.loads(json.dumps(V.export_attestation(repo, SCOPE, did, pid)))
        r = V.verify_attestation(att)
        if r["accepted"]:
            chosen = (did, att, r)
            break
    if chosen is None:
        raise SystemExit(f"no release is accepted under its own policy at projection {pid.hex()}")
    did, att, r = chosen
    tip_atoms, tip_cells, tip_seals = repo.read_cas_tree(chain[-1])
    names = MC.key_names(tip_cells, tip_atoms, tip_seals)
    roster = [{"name": names.get(k, "unnamed"), "key": k.hex()} for k in MC.roster(repo)]
    index = {
        "format": "minds.published-bundles@1",
        "about": "The latest release of s0fractal/minds and the projection that covers it, as published by "
                 "tools/publish_site.py. The names and the roster are the publisher's word: pin the keys you trust.",
        "chain": "refs/vars/heads/minds",
        "chain_tip": chain[-1],
        "published": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "projection": {"id": pid.hex(), "tip": ptip, "witnesses": V.verify_projection(proj)["witnesses"],
                       **_write(out, f"bundles/projection-{pid.hex()}.json", (json.dumps(proj, indent=1) + "\n").encode())},
        "attestation": {"decision": did.hex(), "statement": r["statement"], "endorsers": r["endorsers_at_tip"],
                        **_write(out, f"bundles/attestation-{did.hex()}.json", (json.dumps(att, indent=1) + "\n").encode())},
        "roster": roster,
        "rules": [{"id": h.hex(), **_write(out, f"rules/{h.hex()}.wasm", p.read_bytes())} for h, p in RULES_FILES.items()],
        "verifier": {"main": subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True,
                                            check=True).stdout.strip(),
                     **_write(out, "minds_verify.mjs", (ROOT / "verify" / "minds_verify.mjs").read_bytes())},
    }
    for h, entry in zip(RULES_FILES, index["rules"]):
        if entry["sha256"] != h.hex():
            raise SystemExit(f"{entry['file']} does not hash to its rules identity")
    for name in ("index.html", "page.mjs", "style.css"):
        shutil.copy(ROOT / "site" / name, out / name)
    (out / ".nojekyll").write_bytes(b"")
    (out / "index.json").write_text(json.dumps(index, indent=1) + "\n")
    return index


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    out = Path(sys.argv[1])
    out.mkdir(parents=True, exist_ok=True)
    idx = publish(out)
    print(json.dumps({k: idx[k] for k in ("chain_tip", "projection", "attestation")}, indent=1))
