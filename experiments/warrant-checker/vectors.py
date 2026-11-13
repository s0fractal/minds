#!/usr/bin/env python3
"""Vectors for experiment 6a (README.md): warrant's own answers, recorded, that the module must give byte for byte.

    python vectors.py export --warrant DIR [--minds-store FILE] [--out FILE]   # FILE: instead of the store at MINDS_PIN
    python vectors.py check [--module FILE]

`export` imports warrant from DIR, a checkout of s0fractal/warrant whose HEAD is PIN with a clean tree, and asks
warrant's own functions (jcs.loads, records, shapes, engine._schema_problem, engine._body_problem) about every input:
- every schema and every body the engine checks in DIR/.warrant/records.jsonl (`live`) and in this repository's store
  at MINDS_PIN (`live-minds`);
- the same records changed one way at a time (`mutation`);
- inputs made for an edge (`edge`) and bytes that are not canonical (`jcs`).

The answer is the module's output format (src/lib.rs): the code names the return statement the engine took, found by
tracing the call, so nothing here restates a branch of the engine. `check` runs the module under meter.py on every
vector and lists the differences."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import inspect
import json
import subprocess
import sys
import unicodedata
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PIN = "f7e3637b4a965de5cc502ce6c8e6b1cd7f423673"  # s0fractal/warrant master, Merge pull request #370
MINDS_PIN = "fc3cc5cce7af04ddd838cde75c4adde340f25433"  # this repository's store as the experiment was registered
VECTORS = HERE / "vectors.json.gz"
MODULE = HERE / "checker.wasm"
# the committed modules (test 137 rebuilds them from src/ with Rust 1.100.0)
MODULE_SHA256 = "0e5a9f361875f7e00b689bc5b91462b2b11fc7f88d57a5e85dfe43318775f198"
FAULT_VARIANT_SHA256 = "519afaf5c2604277bf4056a783b8912e6b35c4f8164f1b13c911bce7fcdb0089"
FORMAT = "minds.warrant-checker-vectors@1"
BODY_CODES = ("members", "types", "refs", "valid-not-entity", "state", "guard", "valid")
NOT_CANONICAL, NOT_AN_INPUT, NOT_ASKED = -1, -2, -3
BUDGET = 1 << 30  # vars1.MAX_RULES_BUDGET: what a decision may ask the gate to spend on one metered run


# --- warrant's answer

class Reference:
    def __init__(self, warrant: Path):
        sys.path.insert(0, str(warrant))
        from warrant import engine as E, jcs as C, records as R, shapes as S
        if not Path(E.__file__).resolve().is_relative_to(warrant):
            raise SystemExit(f"warrant was imported from {E.__file__}, not from {warrant}")
        self.E, self.C, self.R, self.S = E, C, R, S
        lines, start = inspect.getsourcelines(E._body_problem)
        self.returns = [start + i for i, line in enumerate(lines) if line.lstrip().startswith("return ")]
        if len(self.returns) != len(BODY_CODES):
            raise SystemExit(f"engine._body_problem has {len(self.returns)} return statements, not {len(BODY_CODES)}")

    def traced(self, *args):
        """_body_problem(*args) and the line of the return statement it took."""
        fn, hit = self.E._body_problem, []

        def local(frame, event, arg):
            if event == "return":
                hit.append(frame.f_lineno)
            return local

        sys.settrace(lambda frame, event, arg: local if frame.f_code is fn.__code__ else None)
        try:
            why = fn(*args)
        finally:
            sys.settrace(None)
        return why, BODY_CODES[self.returns.index(hit[-1])]

    def asked(self, r, s) -> bool:
        """The pairs the engine calls _body_problem on (src/lib.rs, -3), in warrant's own predicates."""
        R, S, E = self.R, self.S, self.E
        return (isinstance(r, dict) and set(r) == set(R.MEMBERS) and r["kind"] in ("entity", "attest", "challenge")
                and R.is_list(r["refs"], S.hex64, True) and isinstance(r["body"], dict)
                and (r["guard"] is None or R.guard_problem(r["guard"]) is None)
                and E._schema_problem(s) is None and r["schema"] == s["name"])

    def answer(self, raw: bytes):
        """("output", canonical bytes) or ("refusal", code)."""
        try:
            v = self.C.loads(raw)
        except ValueError:  # NotCanonical, and int's digit limit, which jcs.loads lets through as ValueError
            return "refusal", NOT_CANONICAL
        if not isinstance(v, dict) or set(v) not in ({"schema"}, {"record", "schema"}):
            return "refusal", NOT_AN_INPUT
        if set(v) == {"schema"}:
            why = self.E._schema_problem(v["schema"])
            code = "not-counted" if why else "counted"
        else:
            if not self.asked(v["record"], v["schema"]):
                return "refusal", NOT_ASKED
            why, code = self.traced(v["record"], v["schema"])
        return "output", self.C.canon({"code": code, "reason": why, "verdict": "problem" if why else "ok"})

    def checked(self, r) -> bool:
        """Is `r` a record whose body the engine checks (engine.View._bodies)?"""
        return not (r["kind"] == "schema" or (r["schema"] is None and r["kind"] != "entity")
                    or (r["schema"] == self.R.MIGRATION and r["kind"] == "attest"))


# --- the inputs

H = [hashlib.sha256(bytes([i])).hexdigest() for i in range(8)]  # ids no store holds


def canon(C, v) -> bytes:
    return C.canon(v)


def copy(v):
    return json.loads(json.dumps(v))


def store(path: Path | None = None):
    """A store's records: a file, or this repository's store at MINDS_PIN."""
    text = path.read_text() if path else subprocess.run(["git", "show", f"{MINDS_PIN}:.warrant/records.jsonl"], cwd=ROOT,
                                                        capture_output=True, text=True, check=True).stdout
    return [json.loads(line)["record"] for line in text.splitlines() if line.strip()]


def live(ref: Reference, records, source):
    schemas = {}
    for r in records:
        if r["kind"] == "schema":
            schemas.setdefault(r["body"].get("name"), []).append(r["body"])
            yield source, ref.C.canon({"schema": r["body"]})
    unpaired = 0
    for r in records:
        if ref.checked(r):
            for s in schemas.get(r["schema"], []):
                yield source, ref.C.canon({"record": r, "schema": s})
            unpaired += r["schema"] not in schemas
    ref.unpaired[source] = unpaired


WRONG = {"str": [1, ["x"], {}], "int": ["1", True, None], "bool": [1, 0, "true"], "strs": ["x", [1], [None], {}],
         "ref": ["A" * 64, "a" * 63, "a" * 64 + "\n", "a" * 63 + "g", 1], "refs": ["a" * 64, ["A" * 64], [H[0], 1], {}],
         "obj": [None, [], 1]}


def guard_variants(need):
    """Guards around a schema's guard for a state: equal, weaker in each part, and stronger."""
    yield None
    yield copy(need)
    g = copy(need); g["quorum"] = need["quorum"] - 1
    if g["quorum"] >= 0:
        yield g
    g = copy(need); g["quorum"] = need["quorum"] + 1
    yield g
    g = copy(need); g["roles"] = sorted(set(need["roles"]) | {"zz-other"})
    yield g
    g = copy(need); g["roles"] = []
    yield g
    for k in need["match"]:
        g = copy(need); del g["match"][k]
        yield g
        g = copy(need); g["match"][k] = "something else"
        yield g
    g = copy(need); g["match"]["extra"] = 1
    yield g
    g = copy(need); g["requires"] = sorted(set(need["requires"]) | {H[1]})
    yield g


def mutations(ref: Reference, records):
    C = ref.C
    schemas = {r["body"]["name"]: r["body"] for r in records if r["kind"] == "schema"}
    by_schema = {}
    for r in records:
        if ref.checked(r) and r["schema"] in schemas:
            by_schema.setdefault((r["schema"], r["kind"] == "entity"), []).append(r)
    for (name, entity), rs in sorted(by_schema.items()):
        s = schemas[name]
        for n, r in enumerate(rs[:3] if entity else rs[:2]):
            def out(rr, ss=s):
                return "mutation", C.canon({"record": rr, "schema": ss})
            f = dict(s["fields"])
            if r["kind"] != "entity" and "target" not in f:
                f["target"] = "ref"
            for key, val in (("zz-extra", 1), ("é", 1), ("\U0001f600", "x"), ("￿", 1)):
                m = copy(r); m["body"][key] = val
                yield out(m)
            required = [k for k, t in f.items() if not t.endswith("?") and k in r["body"]]
            for k in required if n == 0 else required[:1]:
                m = copy(r); del m["body"][k]
                yield out(m)
            for k, t in f.items():
                if k not in r["body"] and not t.endswith("?"):
                    continue
                for w in WRONG[t.rstrip("?")] if n == 0 else WRONG[t.rstrip("?")][:1]:
                    m = copy(r); m["body"][k] = w
                    yield out(m)
                if t.endswith("?"):
                    m = copy(r); m["body"][k] = None
                    yield out(m)
                    m = copy(r); m["body"].pop(k, None)
                    yield out(m)
                if t.rstrip("?") in ("ref", "refs"):
                    m = copy(r); m["body"][k] = H[2] if t.rstrip("?") == "ref" else [H[2]]
                    yield out(m)
                    m["refs"] = sorted(set(m["refs"]) | {H[2]})
                    yield out(m)
            if r["kind"] == "entity" and isinstance(s["states"], dict):
                for st in ("no-such-state", "", "OPEN"):
                    m = copy(r); m["body"]["state"] = st
                    yield out(m)
                for st, need in sorted(s["states"].items()):
                    if need is None or n > 0:
                        continue
                    for g in guard_variants(need):
                        m = copy(r); m["body"]["state"] = st; m["guard"] = g
                        yield out(m)
            # the record as another kind
            m = copy(r); m["kind"] = "attest" if r["kind"] == "entity" else "entity"; m["guard"] = None
            yield out(m)
            m = copy(r); m["kind"] = "challenge"; m["guard"] = None; m["body"]["target"] = H[3]
            yield out(m)
            m["refs"] = sorted(set(m["refs"]) | {H[3]})
            yield out(m)
            # pairs the engine never asks (-3)
            for change in ("drop", "add", "schema-kind", "kind", "unsorted", "upper", "body", "guard", "name", "bad-schema"):
                m, ss = copy(r), s
                if change == "drop":
                    del m["at"]
                elif change == "add":
                    m["extra"] = 1
                elif change == "schema-kind":
                    m["kind"] = "schema"
                elif change == "kind":
                    m["kind"] = 1
                elif change == "unsorted":
                    m["refs"] = [H[5], H[4]]
                elif change == "upper":
                    m["refs"] = ["A" * 64]
                elif change == "body":
                    m["body"] = [m["body"]]
                elif change == "guard":
                    m["guard"] = {"quorum": 1}
                elif change == "name":
                    m["schema"] = name + "x"
                else:
                    ss = dict(s, closed=["no-such-state"])
                yield out(m, ss)
        # the schema itself, changed one way at a time
        def sch(b):
            return "mutation", C.canon({"schema": b})
        for k in ("name", "fields", "states", "closed", "successors"):
            b = copy(s); del b[k]
            yield sch(b)
        yield sch(dict(s, extra=1))
        for p in [k for k, t in s["fields"].items() if t in ("obj", "obj?")][:1] + ["state", "nope", 1, None]:
            yield sch(dict(s, pinned=p))
        for nm in ("", "a" * 100, "a" * 101, "\U0001f600" * 100, "\U0001f600" * 101, "migration@1", 1, None):
            yield sch(dict(s, name=nm))
        for fv in ([], "x", None):
            yield sch(dict(s, fields=fv))
        for t in ("str??", "obj?", "string", "", "?", "Str", 1, None, "refs?"):
            yield sch(dict(s, fields=dict(s["fields"], zz=t)))
        if isinstance(s["states"], dict):
            for t in ("str?", "int", None):
                f = dict(s["fields"])
                if t is None:
                    f.pop("state", None)
                else:
                    f["state"] = t
                yield sch(dict(s, fields=f))
            yield sch(dict(s, states=None))
            yield sch(dict(s, states=[]))
            yield sch(dict(s, states=dict(s["states"], zz=1)))
            if s["closed"]:
                yield sch(dict(s, closed=s["closed"] * 2))
                yield sch(dict(s, closed=s["closed"][0]))
            yield sch(dict(s, closed=sorted(s["states"])))
            yield sch(dict(s, closed=sorted(s["states"])[::-1]))
            st = sorted(s["states"])[0]
            for rs in (["a"], ["b", "a"], ["a", "a"], "a", [1]):
                yield sch(dict(s, successors={st: rs}))
        for c in (["zz"], [1], "x"):
            yield sch(dict(s, closed=c))
        for sc in ({"zz": []}, [], None):
            yield sch(dict(s, successors=sc))


ROLES = ["", "a", "a" * 200, "a" * 201, "\U0001f600" * 200, "\U0001f600" * 201, "é", "é", "Å",
         "\U00016d67\U00016d67", "\U00016d68", "a\u0000", "a\u007f", "a\u0085", "a\u009f", "​a", "a​",
         "᠎a", "﻿a", "a b", "é́", "가", "가"]
# Cc anywhere, and white space (Zs, Zl, Zp) at either end: every such character of the reference's tables
CC = [chr(c) for c in range(0x110000) if unicodedata.category(chr(c)) == "Cc"]
EDGE = [chr(c) for c in range(0x110000) if unicodedata.category(chr(c)) in ("Zs", "Zl", "Zp")]


def edges(ref: Reference):
    C = ref.C
    def sch(b):
        return "edge", C.canon({"schema": b})
    base = {"closed": ["c"], "fields": {"state": "str"}, "name": "t@1",
            "states": {"c": {"match": {"verdict": "accept"}, "quorum": 1, "requires": [], "roles": ["r"]}, "o": None},
            "successors": {}}
    guard = base["states"]["c"]
    roles = ROLES + ["a" + c + "a" for c in CC] + [c + "a" for c in EDGE] + ["a" + c for c in EDGE] + ["a" + c + "a" for c in EDGE]
    for role in roles:
        yield sch(dict(base, states={"c": dict(guard, roles=[role]), "o": None}))
        yield sch(dict(base, successors={"o": [role]}))
    for g in ({"quorum": -1}, {"quorum": True}, {"quorum": "1"}, {"quorum": 2 ** 53 - 1}, {"quorum": 0},
              {"roles": ["b", "a"]}, {"roles": ["a", "a"]}, {"roles": "a"}, {"match": []}, {"match": None},
              {"requires": ["A" * 64]}, {"requires": [H[0], H[0]]}, {"requires": sorted(H[:2])[::-1]},
              {"requires": sorted(H[:3])}):
        yield sch(dict(base, states={"c": dict(guard, **g), "o": None}))
    for drop in ("quorum", "roles", "match", "requires"):
        g = dict(guard); del g[drop]
        yield sch(dict(base, states={"c": g, "o": None}))
    yield sch(dict(base, states={"c": dict(guard, extra=1), "o": None}))
    for b in (None, 1, "x", [], {}, [base]):
        yield sch(b)
    yield sch(dict(base, states=None, closed=[], fields={}))
    yield sch(dict(base, states=None, closed=[], fields={"state": "obj"}))
    yield sch(dict(base, pinned="", fields={"": "obj", "state": "str"}))
    yield sch(dict(base, pinned="", fields={"": "obj?", "state": "str"}))

    def body(rec, s):
        return "edge", C.canon({"record": rec, "schema": s})
    def entity(b, s, guard=None, refs=()):
        return {"actor": "a", "at": 0, "body": b, "guard": guard, "kind": "entity", "lineage": None, "prev": None,
                "refs": sorted(refs), "schema": s["name"], "warrant": "3"}
    # Python's == in a guard's match: True == 1, at any depth
    for need_v, g_v in ((1, True), (1, 1), (0, False), (1, "1"), (1, 2), (True, 1), ([1, {"a": 0}], [True, {"a": False}]),
                        ({"a": 1, "b": [0]}, {"a": True, "b": [False]}), ([1], [1, 1]), ([1, 1], [1]), ({"a": 1}, {"a": 1, "b": 1}),
                        ({"a": 1, "b": 1}, {"a": 1}),
                        (None, None), (None, 0), ("x", "x"), ([], {}), ({}, {})):
        need = {"match": {"n": need_v}, "quorum": 1, "requires": [], "roles": ["r"]}
        s = dict(base, states={"c": need, "o": None})
        yield body(entity({"state": "c"}, s, guard=dict(need, match={"n": g_v})), s)
    # quorum and roles: roles count only when the schema asks for an attest
    for nq, gq, groles in ((0, 0, ["zz"]), (1, 1, ["zz"]), (2, 1, ["r"]), (1, 3, ["r"]), (1, 1, []), (0, 0, [])):
        need = {"match": {}, "quorum": nq, "requires": [H[0]], "roles": ["r"]}
        s = dict(base, states={"c": need, "o": None})
        yield body(entity({"state": "c"}, s, guard={"match": {}, "quorum": gq, "requires": [H[0]], "roles": groles}), s)
        yield body(entity({"state": "c"}, s, guard={"match": {}, "quorum": gq, "requires": [], "roles": groles}), s)
    # a state quoted as JSON: keys in code point order, which is not the input's UTF-16 order
    loose = dict(base, states=None, closed=[], fields={"state": "obj?"})
    for st in ({"￿": 1, "\U00010000": 2}, [1, "é", None, True], -5, "a\"b\\c\n\u0001\u007f\U0001f600", None, {}):
        yield body(entity({"state": st}, loose), loose)
    yield body(entity({}, loose), loose)
    yield body(entity({}, dict(base, states=None, closed=[], fields={})), dict(base, states=None, closed=[], fields={}))
    # member names that need escapes, sorted by code point in `members` and kept in the input's order in `types`
    odd = ["a\"b", "\\", "\u0000", "\u007f", "é", "\U0001f600", "￿", "\U00010000", " ", "zz"]
    wide = dict(base, states={"o": None}, closed=[], fields=dict({k: "int" for k in odd}, state="str"))
    yield body(entity(dict({k: 1 for k in odd}, state="o"), wide), wide)
    yield body(entity(dict({k: "1" for k in odd}, state="o"), wide), wide)
    yield body(entity({"state": "o"}, wide), wide)
    yield body(entity(dict({k + "!": 1 for k in odd}, state="o"), wide), wide)
    # a name that needs escapes in the output
    for nm in ("a\"b\\c\n\t\u0001\u007f", "é\U0001f600", "x" * 100):
        s = dict(base, name=nm)
        yield body(entity({"state": "zz"}, s), s)
    # types: `?` once admits null; `??` passes the schema check and admits only null
    for t in ("str??", "ref???", "obj?", "obj", "refs?"):
        s = dict(base, states={"o": None}, closed=[], fields={"state": "str", "v": t})
        for v in (None, "x", H[0], [H[0]], [], 1):
            refs = [H[0]] if v in (H[0], [H[0]]) else []
            yield body(entity({"state": "o", "v": v}, s, refs=refs), s)
    # attests and challenges: a target is a reference too, unless the schema declares it
    for kind in ("attest", "challenge"):
        for fields in ({}, {"target": "str"}, {"target": "ref?"}):
            s = dict(base, states=None, closed=[], fields=fields)
            for b, refs in (({"target": H[0]}, [H[0]]), ({"target": H[0]}, []), ({}, []), ({"target": "x"}, [])):
                rec = dict(entity(b, s, refs=refs), kind=kind)
                yield body(rec, s)


def jcs(ref: Reference, base: bytes):
    """Bytes jcs.loads may refuse, around one canonical input."""
    C = ref.C
    v = C.loads(base)
    yield "jcs", base
    for raw in (base + b" ", b" " + base, base + b"\n", b"\xef\xbb\xbf" + base, base.replace(b":", b": ", 1),
                base[:-1], base + b"0", b"", b"null", b"[]", b"1", b'"x"', b"{}", b"NaN", b"Infinity", b"-Infinity",
                b'{"schema":1,"x":2}', b'{"record":1}', b'{"record":1,"schema":1}', b'{"x":1}',
                b'{"schema":1,"schema":1}', b'{"schema":{},"record":{}}'):
        yield "jcs", raw
    rec, s = v.get("record"), v.get("schema")
    # integers at and past the range, and numbers that are not integers
    for text in (b"0", b"-0", b"01", b"1.0", b"1e2", b"1E2", b"-", b"9007199254740991", b"-9007199254740991",
                 b"9007199254740992", b"-9007199254740992", b"1" * 5000, b"00", b"-01", b"2.5", b"true", b"tru"):
        yield "jcs", b'{"schema":' + text + b"}"
    # strings: the escapes canon writes, and every other way to write the same character
    for text in (b'"\\u0041"', b'"\\/"', b'"\\u001F"', b'"\\u001f"', b'"\x1f"', b'"\\ud800"', b'"\\ud83d\\ude00"',
                 b'"\xed\xa0\x80"', b'"\xff"', b'"\xc0\xaf"', b'"\xe2\x80\xa8"', b'"\x7f"', b'"\\u0008"', b'"\\b"',
                 b'"\\u000a"', b'"\\n"', b'"\\x"', b'"\\u00e9"', '"é"'.encode(), b'"\\"', b'"a', b'"\\u12"'):
        yield "jcs", b'{"schema":{"closed":[],"fields":{},"name":' + text + b',"states":null,"successors":{}}}'
    # members out of order, by code point against UTF-16
    yield "jcs", '{"schema":{"closed":[],"fields":{"\U00010000":"int","￿":"int"},"name":"x","states":null,"successors":{}}}'.encode()
    yield "jcs", '{"schema":{"closed":[],"fields":{"￿":"int","\U00010000":"int"},"name":"x","states":null,"successors":{}}}'.encode()
    # nesting: canon writes a container 256 deep; jcs.loads refuses one 257 deep only when the bytes hold more than
    # 1024 '[' and '{', counted inside strings too
    if rec is not None:
        f = {"closed": [], "fields": {"deep": "obj", "pad": "obj", "state": "str"}, "name": "deep@1",
             "states": {"o": None}, "successors": {}}
        def deep(n, pad):
            r = {"actor": "a", "at": 0, "body": {"deep": 0, "pad": pad, "state": "o"}, "guard": None, "kind": "entity",
                 "lineage": None, "prev": None, "refs": [], "schema": "deep@1", "warrant": "3"}
            raw = C.canon({"record": r, "schema": f})
            return raw.replace(b'"deep":0', b'"deep":' + b"[" * n + b"]" * n)
        for n, pad in ((253, None), (254, None), (255, None), (254, [[]] * 600), (254, [[]] * 800), (253, [[]] * 800),
                       (255, [[]] * 800), (254, "[" * 800), (254, "[" * 700)):
            yield "jcs", deep(n, pad)


def export(args) -> int:
    warrant = Path(args.warrant).resolve()
    head = subprocess.run(["git", "-C", str(warrant), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "-C", str(warrant), "status", "--porcelain"], capture_output=True, text=True).stdout
    if head != PIN or dirty:
        print(f"warrant at {warrant} is {head or 'not a checkout'}{' with changes' if dirty else ''}; the vectors are {PIN}'s",
              file=sys.stderr)
        return 2
    ref = Reference(warrant)
    ref.unpaired = {}
    minds = Path(args.minds_store) if args.minds_store else None
    warrant_records, minds_records = store(warrant / ".warrant" / "records.jsonl"), store(minds)
    inputs = list(live(ref, warrant_records, "live")) + list(live(ref, minds_records, "live-minds"))
    first_body = next(raw for src, raw in inputs if raw.startswith(b'{"record"'))
    inputs += list(mutations(ref, warrant_records)) + list(edges(ref)) + list(jcs(ref, first_body))
    seen, vectors = set(), []
    for source, raw in inputs:
        if raw in seen:
            continue
        seen.add(raw)
        kind, value = ref.answer(raw)
        v = {"source": source}
        try:
            v["in"] = raw.decode("utf-8")
        except UnicodeDecodeError:
            v["in_hex"] = raw.hex()
        if kind == "output":
            v["out"] = value.decode("utf-8")
        else:
            v["refusal"] = value
        vectors.append(v)
    doc = {"format": FORMAT,
           "warrant": {"commit": PIN, "records": len(warrant_records),
                       "checked": sum(1 for r in warrant_records if r["kind"] == "schema" or ref.checked(r)),
                       "unpaired": ref.unpaired["live"]},
           "minds_store": {"commit": None if args.minds_store else MINDS_PIN, "records": len(minds_records),
                           "unpaired": ref.unpaired["live-minds"]},
           "python": sys.version.split()[0], "unicode": unicodedata.unidata_version,
           "vectors": vectors}
    data = json.dumps(doc, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
    out = Path(args.out) if args.out else VECTORS
    out.write_bytes(gzip.compress(data, compresslevel=9, mtime=0))
    counts = {}
    for v in vectors:
        k = (v["source"], json.loads(v["out"])["code"] if "out" in v else v["refusal"])
        counts[k] = counts.get(k, 0) + 1
    print(json.dumps({"vectors": len(vectors), "python": doc["python"], "unicode": doc["unicode"],
                      "by": {f"{a} {b}": n for (a, b), n in sorted(counts.items(), key=str)}}, indent=1))
    return 0


# --- the module's answer

def load(path: Path = VECTORS) -> dict:
    return json.loads(gzip.decompress(path.read_bytes()))


def raw_of(v) -> bytes:
    return v["in"].encode("utf-8") if "in" in v else bytes.fromhex(v["in_hex"])


class Host:
    """host.mjs over one metered module: `run(input, budget)` gives (steps, result), the result being the hex output,
    E<code>, X (exhausted) or T (a trap)."""

    def __init__(self, module: bytes):
        sys.path.insert(0, str(ROOT))
        import meter
        self.p = subprocess.Popen(["node", str(HERE / "host.mjs")], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  text=True)
        self.p.stdin.write(meter.metered(module).hex() + "\n")

    def run(self, raw: bytes, budget: int = BUDGET):
        self.p.stdin.write(f"{budget} {raw.hex()}\n")
        self.p.stdin.flush()
        steps, result = self.p.stdout.readline().split()
        return int(steps), result

    def close(self):
        self.p.stdin.close()
        self.p.stdout.close()
        self.p.wait(timeout=10)


def expected(v) -> str:
    return v["out"].encode("utf-8").hex() if "out" in v else f"E{v['refusal']}"


def check(module: Path = MODULE, doc: dict | None = None):
    """Every vector the module answers otherwise, as (index, expected, got); and the steps of each run."""
    doc = doc or load()
    host = Host(module.read_bytes())
    diffs, steps = [], []
    try:
        for i, v in enumerate(doc["vectors"]):
            n, got = host.run(raw_of(v))
            steps.append(n)
            if got != expected(v):
                diffs.append((i, expected(v), got))
    finally:
        host.close()
    return diffs, steps


def main(argv) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    e = sub.add_parser("export")
    e.add_argument("--warrant", required=True)
    e.add_argument("--minds-store")
    e.add_argument("--out")
    c = sub.add_parser("check")
    c.add_argument("--module", default=str(MODULE))
    c.add_argument("--vectors", default=str(VECTORS))
    args = ap.parse_args(argv)
    if args.cmd == "export":
        return export(args)
    doc = load(Path(args.vectors))
    diffs, steps = check(Path(args.module), doc)
    for i, want, got in diffs[:10]:
        v = doc["vectors"][i]
        print(json.dumps({"index": i, "source": v["source"], "input": v.get("in", v.get("in_hex"))[:300],
                          "expected": bytes.fromhex(want).decode() if not want.startswith("E") else want,
                          "got": bytes.fromhex(got).decode(errors="replace") if got[0] not in "EXT" else got}))
    print(json.dumps({"vectors": len(doc["vectors"]), "differences": len(diffs)}))
    return 1 if diffs else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
