#!/usr/bin/env python3
"""The specification as a projection of what holds it (claims.json).

Every block of VARS-1-SPEC.md §0–§5 (a paragraph, a list item, a table, a code block) must contain the exact quote
of a claim or of an informative passage; every quote must still be in the spec, or, for a claim with
`"source": "ASSURANCE.md"` (what this repository's tools establish beyond the spec, such as the release checks), in
the claim cell of exactly one claim-table row of assurance.json whose evidence cell begins with the claim's status, and
ASSURANCE.md must be exactly the rendering of assurance.json; every witness must exist; a claim
that is tested or differential names at least one mutant that `tools/run_mutants.py` kills (or, for the witness
spike's checker, `experiments/witness/test_witness.py --mutants`); every mutant named exists, and finds its line
exactly once. Debt is listed, never failed: `assumed` (nothing here checks it) and `unburned` (a witness exists, but no
mutant has shown that it bites). An unburned claim says why in `reason`, rendered into ASSURANCE.md's debt table; no other
claim carries one. Exit 1 on any violation.

    python3 tools/check_claims.py            # check
    python3 tools/check_claims.py --table    # print claim -> status -> witnesses -> mutants
    python3 tools/check_claims.py --write-assurance  # render ASSURANCE.md from assurance.json
    python3 tools/check_claims.py --spec FILE --claims FILE [--assurance FILE] [--assurance-data FILE]
                                             # check other files (tests burn the checker so)
"""
from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STATUSES = {"proved", "bounded", "differential", "tested", "unburned", "assumed"}
DEBT = {"unburned", "assumed"}
WITNESS = "experiments/witness"


def norm(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def render_spec(doc: dict) -> str:
    """VARS-1-SPEC.md is a projection of spec.json: its parts' texts, each a run of whole lines, joined by newlines."""
    return "\n".join(part["text"] for part in doc["parts"])


def spec_problems(doc: dict, carriers: dict) -> list[str]:
    """What spec.json gets wrong: a part of an unknown kind; a heading that is not one heading line; a gap that is not
    one blank line; a block of §0–§5 (the section counted from the `## N.` headings, never read from the part) that
    carries nothing, or carries something whose quote is not in its own text. `carriers` maps each claim id and
    `informative:N` to its normalized quote."""
    errs: list[str] = []
    section = None
    for i, part in enumerate(doc["parts"]):
        kind, text = part.get("kind"), part.get("text", "")
        if kind == "heading":
            if "\n" in text or not re.match(r"^#{1,6} \S", text):
                errs.append(f"spec.json part {i}: a heading is one heading line: {text[:60]!r}")
            m = re.match(r"^## (\d+)\.", text)
            if m:
                section = int(m.group(1))
            elif text.startswith("## "):
                section = None  # a section without a number is outside §0–§5 by name, so it must say why: none here
            continue
        if kind == "gap":
            if text.strip():
                errs.append(f"spec.json part {i}: a gap is a blank line: {text[:60]!r}")
            continue
        if kind != "block":
            errs.append(f"spec.json part {i}: unknown kind {kind!r}")
            continue
        if section is None or section > 5:
            continue
        carried = part.get("carries", [])
        if not carried:
            errs.append(f"spec.json part {i} (§{section}): carries no claim or informative passage: {norm(text)[:80]!r}")
        for cid in carried:
            if cid not in carriers:
                errs.append(f"spec.json part {i}: carries unknown {cid!r}")
            elif carriers[cid] not in norm(text):
                errs.append(f"spec.json part {i}: carries {cid}, whose quote is not in its text")
    return errs


EVIDENCE_WORD = {"proved": "Proved", "bounded": "Bounded", "differential": "Differential", "tested": "Tested",
                 "assumed": "Assumed", "unburned": "Unburned"}


def render_assurance(doc: dict, claims: list = ()) -> str:
    """ASSURANCE.md is a projection of assurance.json: prose parts verbatim, tables rendered from their cells (a `|` in
    a cell escaped). Nothing parses the Markdown; the file must be exactly this rendering. A table whose first header
    is `Claim` holds claim rows. The part `{"unburned": true}` is the debt table, rendered from the unburned claims of
    claims.json and their reasons."""
    out = []
    for part in doc["parts"]:
        if "md" in part:
            out.append(part["md"])
            continue
        if part.get("unburned"):
            part = {"table": {"header": ["Unburned claim", "Why no mutant burns it"],
                              "rows": [[f"`{c['id']}`", c.get("reason", "")] for c in claims
                                       if c["status"] == "unburned"]}}
        t = part["table"]
        cell = lambda c: c.replace("|", "\\|")
        out.append("\n".join(["| " + " | ".join(map(cell, t["header"])) + " |", "|" + "---|" * len(t["header"])]
                             + ["| " + " | ".join(map(cell, r)) + " |" for r in t["rows"]]) + "\n")
    return "".join(out)


def assurance_rows(doc: dict) -> list[tuple[str, str]]:
    """(claim cell, evidence cell) of every row of every claim table of assurance.json: data, not parsed text."""
    return [(norm(r[0]), norm(r[1])) for part in doc["parts"] if "table" in part
            and part["table"]["header"][0] == "Claim" for r in part["table"]["rows"]]


def witness_exists(w: str) -> bool:
    kind, _, name = w.partition(":")
    if kind == "test":
        return re.search(rf"^    def {re.escape(name)}\(", (ROOT / "test_vars1.py").read_text(), re.M) is not None
    if kind == "witness":  # a test of the witness spike's checker (experiments/witness)
        return re.search(rf"^    def {re.escape(name)}\(", (ROOT / WITNESS / "test_witness.py").read_text(), re.M) is not None
    if kind == "import":  # a check vars1.py makes as it loads, named by its message
        return name in (ROOT / "vars1.py").read_text()
    if kind == "prop":
        return re.search(rf"\b{re.escape(name)}\b", (ROOT / "test_vars1_props.py").read_text()) is not None
    if kind == "lean":
        return any(re.search(rf"^(theorem|lemma) {re.escape(name)}\b", f.read_text(), re.M)
                   for f in (ROOT / "proofs").rglob("*.lean") if ".lake" not in f.parts)
    if kind == "kani":
        src = (ROOT / "kernel" / "src" / "lib.rs").read_text()
        return re.search(rf"#\[kani::proof\][^\n]*\n(?:\s*#\[[^\n]*\n)*\s*fn {re.escape(name)}\(", src) is not None
    if kind == "ci":
        return any(f"name: {name}" in f.read_text() for f in (ROOT / ".github" / "workflows").glob("*.yml"))
    return False


def main(argv: list[str]) -> int:
    def arg(name: str, default: Path) -> Path:
        return Path(argv[argv.index(name) + 1]) if name in argv else default

    spec_doc = json.loads(arg("--spec-data", ROOT / "spec.json").read_text())
    data = json.loads(arg("--claims", ROOT / "claims.json").read_text())
    mutants = json.loads((ROOT / "mutants.json").read_text())
    for mid, mu in json.loads((ROOT / WITNESS / "mutants.json").read_text()).items():  # one file, its own harness
        if mid in mutants:
            print(f"mutant id in both mutants.json and {WITNESS}/mutants.json: {mid}")
            return 1
        mutants[mid] = {**mu, "file": f"{WITNESS}/check.py"}
    claims, informative = data["claims"], data["informative"]
    errors: list[str] = []
    spec_text = render_spec(spec_doc)
    if "--write-spec" in argv:
        arg("--spec", ROOT / "VARS-1-SPEC.md").write_text(spec_text)
    if arg("--spec", ROOT / "VARS-1-SPEC.md").read_text() != spec_text:
        errors.append("VARS-1-SPEC.md is not the rendering of spec.json (tools/check_claims.py --write-spec)")
    carriers = {c["id"]: norm(c["quote"]) for c in claims if "source" not in c}
    carriers.update({f"informative:{i}": norm(q) for i, q in enumerate(informative)})
    errors += spec_problems(spec_doc, carriers)
    carried = {cid for part in spec_doc["parts"] for cid in part.get("carries", [])}
    assurance_doc = json.loads(arg("--assurance-data", ROOT / "assurance.json").read_text())
    rendered = render_assurance(assurance_doc, claims)
    if "--write-assurance" in argv:
        arg("--assurance", ROOT / "ASSURANCE.md").write_text(rendered)
    if arg("--assurance", ROOT / "ASSURANCE.md").read_text() != rendered:
        errors.append("ASSURANCE.md is not the rendering of assurance.json (tools/check_claims.py --write-assurance)")
    sources = {"ASSURANCE.md": assurance_rows(assurance_doc)}

    ids = [c["id"] for c in claims]
    for dup in sorted({i for i in ids if ids.count(i) > 1}):
        errors.append(f"claim id used twice: {dup}")
    for c in claims:
        q = norm(c["quote"])
        source = c.get("source")
        if source is not None and source not in sources:
            errors.append(f"{c['id']}: unknown source {source!r}")
        elif source is None and c["id"] not in carried:
            errors.append(f"{c['id']}: carried by no part of spec.json (its quote is not in the spec): {q[:80]!r}")
        elif source is not None:
            # held by exactly one row's claim column, whose evidence column states the claim's own status
            held = [ev for claim, ev in sources[source] if q in claim]
            if len(held) != 1:
                errors.append(f"{c['id']}: quote in {len(held)} rows of {source}, not one: {q[:80]!r}")
            elif not held[0].startswith(EVIDENCE_WORD.get(c["status"], "?")):
                errors.append(f"{c['id']}: {source} row says {held[0][:40]!r}, not {c['status']}")
        if c["status"] not in STATUSES:
            errors.append(f"{c['id']}: unknown status {c['status']!r}")
        if c["status"] != "assumed" and not c.get("witnesses"):
            errors.append(f"{c['id']}: {c['status']} without a witness")
        if c["status"] == "unburned" and c.get("mutants"):
            errors.append(f"{c['id']}: unburned, yet it names mutants (then it is tested or differential)")
        if c["status"] == "unburned" and not c.get("reason", "").strip():
            errors.append(f"{c['id']}: unburned without a reason (why no mutant burns it)")
        if c["status"] != "unburned" and "reason" in c:
            errors.append(f"{c['id']}: {c['status']}, yet it gives a reason for not being burned")
        if c["status"] == "assumed" and (c.get("witnesses") or c.get("mutants")):
            errors.append(f"{c['id']}: assumed, yet it names witnesses or mutants")
        for w in c.get("witnesses", []):
            if not witness_exists(w):
                errors.append(f"{c['id']}: witness does not exist: {w}")
        kinds = {w.partition(":")[0] for w in c.get("witnesses", [])}
        if c["status"] == "proved" and "lean" not in kinds:
            errors.append(f"{c['id']}: proved without a lean witness")
        if c["status"] == "bounded" and "kani" not in kinds:
            errors.append(f"{c['id']}: bounded without a kani witness")
        if c["status"] in ("tested", "differential") and not c.get("mutants"):
            errors.append(f"{c['id']}: {c['status']} without a mutant")
        for m in c.get("mutants", []):
            if m not in mutants:
                errors.append(f"{c['id']}: mutant does not exist: {m}")
            elif mutants[m].get("diagnostic") and not c.get("diagnostic"):
                # it loses the reason a refusal names, not the refusal: it burns no claim about what is refused
                errors.append(f"{c['id']}: names {m}, a diagnostic mutant, but is not a claim about a reason")
    for i, q in enumerate(informative):
        if f"informative:{i}" not in carried:
            errors.append(f"informative passage {i} is carried by no part of spec.json: {norm(q)[:80]!r}")
    for mid, mu in sorted(mutants.items()):  # a mutant whose line was edited away runs nothing (PR #9: CI caught it late)
        if mid == os.environ.get("MINDS_MUTANT"):
            continue  # the mutant being applied by tools/run_mutants.py: its line is replaced on purpose
        target = ROOT / mu["file"]
        n = target.read_text().count(mu["find"]) if target.is_file() else 0
        if n != 1:
            errors.append(f"mutant {mid}: its find string occurs {n} times in {mu['file']}, not once")
    used = {m for c in claims for m in c.get("mutants", [])}
    for m in sorted(set(mutants) - used):
        errors.append(f"mutant not named by any claim: {m}")

    if "--table" in argv:
        for c in claims:
            print(f"{c['id']:<32} {c['status']:<12} {', '.join(c.get('witnesses', [])) or '-'}  "
                  f"[{', '.join(c.get('mutants', []))}]")
    counts = {s: sum(c["status"] == s for c in claims) for s in sorted(STATUSES)}
    print(f"{len(claims)} claims {counts}; {len(mutants)} mutants")
    for s in sorted(DEBT):
        ids = [c["id"] for c in claims if c["status"] == s]
        print(f"debt ({s}, {len(ids)}): {', '.join(ids) or 'none'}")
    for e in errors:
        print("ERROR", e)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
