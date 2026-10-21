#!/usr/bin/env python3
"""The specification as a projection of what holds it (claims.json).

Every block of VARS-1-SPEC.md §0–§5 (a paragraph, a list item, a table, a code block) must contain the exact quote
of a claim or of an informative passage; every quote must still be in the spec, or, for a claim with
`"source": "ASSURANCE.md"` (what this repository's tools establish beyond the spec, such as the release checks), in
the claim column of exactly one table row of ASSURANCE.md (comments removed) whose evidence column begins with the
claim's status; every witness must exist; a claim
that is tested or differential names at least one mutant that `tools/run_mutants.py` kills; every mutant named
exists. Debt is listed, never failed: `assumed` (nothing here checks it) and `unburned` (a witness exists, but no
mutant has shown that it bites). Exit 1 on any violation.

    python3 tools/check_claims.py            # check
    python3 tools/check_claims.py --table    # print claim -> status -> witnesses -> mutants
    python3 tools/check_claims.py --spec FILE --claims FILE [--assurance FILE]
                                             # check other files (tests burn the checker so)
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STATUSES = {"proved", "bounded", "differential", "tested", "unburned", "assumed"}
DEBT = {"unburned", "assumed"}


LINES = re.compile(r"\r\n|\r|\n")  # Markdown's line endings only: str.splitlines also breaks at U+2028, U+0085, ...


def norm(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


UNREAD = re.compile(r"^(?: {0,3}(?:[*+][ \t]|\d+\)[ \t]|~{3,}|>|<[A-Za-z!/?]|(?:=+|-{2,}|\*{3,}|_{3,})[ \t]*$)"
                    r"| {1,3}`{3,}|[ \t]+(?:\d+[.)]|[-*+])[ \t])")


def spec_blocks(spec: str) -> list[tuple[int, str]]:
    """(line, text) of every block in §0–§5: paragraphs, list items (`-` or `N.`), tables and code blocks (```);
    headings excluded. Any other block construct in §0–§5 is refused (ValueError), never read into a neighbour."""
    blocks: list[tuple[int, str]] = []
    section = None
    cur: list[str] = []
    start = 0
    fenced = False

    def flush() -> None:
        nonlocal cur
        if cur and section is not None and section <= 5:
            blocks.append((start, norm(" ".join(cur))))
        cur = []

    for n, line in enumerate(LINES.split(spec), 1):
        if line.startswith("```"):
            if not fenced:
                flush()
                start = n
            cur.append(line)
            fenced = not fenced
            if not fenced:
                flush()
            continue
        if fenced:
            cur.append(line)
            continue
        if section is not None and section <= 5 and (UNREAD.match(line) or (line[:1] in (" ", "\t") and not cur and
                                                                          line.strip())):
            # a block this checker does not split (another list marker, a nested or indented item, indented code, a
            # quote, HTML, a setext underline or a rule, another fence) would be read into its neighbour's coverage
            raise ValueError(f"VARS-1-SPEC.md:{n}: a block construct this checker does not read: {line.strip()[:60]!r}")
        m = re.match(r"^## (\d+)\.", line)
        if m:
            flush()
            section = int(m.group(1))
            continue
        if re.match(r"^ {0,3}#{1,6}(?:[ \t]|$)", line):  # a heading; `#word` is a paragraph (CommonMark)
            flush()
            continue
        if not line.strip():
            flush()
            continue
        if re.match(r"^(\d+\.|-) ", line):
            flush()
        if not cur:
            start = n
        cur.append(line)
    flush()
    return blocks


EVIDENCE_WORD = {"proved": "Proved", "bounded": "Bounded", "differential": "Differential", "tested": "Tested",
                 "assumed": "Assumed", "unburned": "Unburned"}


DELIMITER = re.compile(r"^\|(?: *:?-+:? *\|)+ *$")


def assurance_rows(text: str) -> list[tuple[str, str]]:
    """(claim column, evidence column) of every body row of every table of ASSURANCE.md. Telling a live row from
    hidden, quoted or stray text is a Markdown parser's work, not this checker's (Codex review of PR #4, rounds
    1–8), so the file is held to a form whose rows read the same either way, and anything else is refused: no HTML
    (outside code spans), no fenced block, and every line opening with `|` inside a table, which opens after a blank
    line or a heading with a header row and a delimiter row and runs while lines open with `|`."""
    lines = LINES.split(text)
    for n, line in enumerate(lines, 1):
        bare = re.sub(r"`[^`]*`", "", line)  # code spans are literal text; an unmatched backtick stays, and is read
        if "<" in bare and re.search(r"<[A-Za-z!/?]", bare) or re.match(r"^ {0,3}(`{3,}|~{3,})", line):
            raise ValueError(f"ASSURANCE.md:{n}: HTML or a fenced block; neither may hold or hide a row")
    rows = []
    n = 0
    while n < len(lines):
        line = lines[n]
        if not line.startswith("|"):
            n += 1
            continue
        opens = (n == 0 or not lines[n - 1].strip() or lines[n - 1].startswith("#"))
        if not (opens and n + 1 < len(lines) and DELIMITER.match(lines[n + 1])):
            raise ValueError(f"ASSURANCE.md:{n + 1}: a row outside a table (a table opens after a blank line or a "
                             f"heading, with a header row and a delimiter row)")
        n += 2
        while n < len(lines) and lines[n].startswith("|"):
            cells = [c.strip() for c in lines[n].strip().strip("|").split("|")]
            if len(cells) >= 2:
                rows.append((norm(cells[0]), norm(cells[1])))
            n += 1
    return rows


def witness_exists(w: str) -> bool:
    kind, _, name = w.partition(":")
    if kind == "test":
        return re.search(rf"^    def {re.escape(name)}\(", (ROOT / "test_vars1.py").read_text(), re.M) is not None
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

    spec = arg("--spec", ROOT / "VARS-1-SPEC.md").read_text()
    data = json.loads(arg("--claims", ROOT / "claims.json").read_text())
    mutants = json.loads((ROOT / "mutants.json").read_text())
    claims, informative = data["claims"], data["informative"]
    errors: list[str] = []
    flat = norm(spec)
    try:
        sources = {"ASSURANCE.md": assurance_rows(arg("--assurance", ROOT / "ASSURANCE.md").read_text())}
    except ValueError as e:
        errors.append(str(e))
        sources = {"ASSURANCE.md": []}

    ids = [c["id"] for c in claims]
    for dup in sorted({i for i in ids if ids.count(i) > 1}):
        errors.append(f"claim id used twice: {dup}")
    quotes = [norm(c["quote"]) for c in claims if "source" not in c] + [norm(q) for q in informative]
    for c in claims:
        q = norm(c["quote"])
        source = c.get("source")
        if source is not None and source not in sources:
            errors.append(f"{c['id']}: unknown source {source!r}")
        elif source is None and q not in flat:
            errors.append(f"{c['id']}: quote not in the spec: {q[:80]!r}")
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
    for q in informative:
        if norm(q) not in flat:
            errors.append(f"informative quote not in the spec: {norm(q)[:80]!r}")
    try:
        blocks = spec_blocks(spec)
    except ValueError as e:
        errors.append(str(e))
        blocks = []
    for line, block in blocks:
        if not any(q in block for q in quotes):
            errors.append(f"VARS-1-SPEC.md:{line}: no claim or informative quote covers this block: {block[:90]!r}")
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
