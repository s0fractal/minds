#!/usr/bin/env python3
"""The vectors that hold verify/minds_verify.mjs (the JavaScript verifier) to verify/minds_verify.py, byte for byte.

    .venv/bin/python tools/verify_vectors.py export [--live DIR]   # write verify/vectors.json
    .venv/bin/python tools/verify_vectors.py check                 # the Python file still answers every vector so

`export` runs the offline verifier's own tests (OFFLINE_TESTS) with two recorders and keeps what they gave the
verifier: every command line of minds_verify.py with the files it read (the real bundles of those tests and every
mutation they make), and every call of verify_projection, verify_attestation and compare_projections. It adds
SPOILED: the raw bytes of one real bundle spoiled in ways a JSON reader or a hex reader can be read differently
(read_bundle's refusals and Python's own words for them), and, with `--live DIR`, the published bundles of the live
chain in DIR (`index.json` names them). Then each vector is answered by this checkout's minds_verify.py, in this
process, in one environment (Node on PATH, no NODE_OPTIONS): a command line's exit code, stdout and stderr; a call's
result as `json.dumps(result, indent=2, sort_keys=True)`, or its exception's class and words. The answers are the
file's, not the tests': the tests decide what was asked, this file what Python says.

`check` answers every vector again and requires the same bytes: a change to minds_verify.py that changes an answer
fails here until the vectors are exported again, so the JavaScript port is held to the change too
(verify/check_vectors.mjs, test 134).

Inputs are kept once, by SHA-256 (`blobs`): bundles as the bytes the verifier read, rules modules as hex.
"""
from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VECTORS = ROOT / "verify" / "vectors.json"
FORMAT = "minds.verify-vectors@1"
OFFLINE_TESTS = (
    "test_14_light_client_verifies_a_projection_bundle_without_the_repository",
    "test_15_minds_governs_itself",
    "test_16_light_client_verifies_a_release_attestation",
    "test_17_attestation_evidence_is_complete_at_the_projection_tip",
    "test_19_a_second_member_verifies_releases",
    "test_21_attestation_counts_what_the_lens_counts",
    "test_22_one_member_can_rotate_the_other_out_but_a_reader_pin_holds",
    "test_27_a_historical_attestation_survives_a_rotation",
    "test_28_a_later_invalid_withdraws_only_its_own_verifier",
    "test_36_offline_verifier_in_a_fresh_folder",
    "test_53_v1_releases_survive_a_rules_change",
    "test_90_the_offline_verifier_reads_every_rules_identity_the_host_implements",
    "test_91_a_reader_who_runs_the_rules_checks_what_the_witnesses_vouch_for",
    "test_102_a_key_withdraws_only_its_own_endorsement",
    "test_103_an_invalid_after_the_tip_withdraws_only_its_own_keys",
    "test_104_grounded_carries_settled_across_relies",
    "test_109_a_client_does_not_accept_what_is_not_grounded",
    "test_111_two_bundles_prove_a_fork_and_a_key_that_sealed_both",
    "test_112_a_fork_without_a_shared_key_names_no_one",
    "test_113_one_input_for_one_tip_byte_for_byte",
    "test_116_a_withdrawal_after_the_tip_reaches_grounded",
    "test_117_what_a_decision_rests_on_is_named",
    "test_120_an_input_that_lies_about_its_history_is_refused",
    "test_121_what_two_witnessed_sides_are_worth",
    "test_122_two_tips_at_one_count_are_not_one_tip",
    "test_123_a_spoiled_bundle_is_refused_and_no_crash",
    "test_130_a_release_settles_on_a_majority_and_a_pin_keeps_a_veto",
)
FUNCTIONS = ("verify_projection", "verify_attestation", "compare_projections", "parse_kernel_input")


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class Recorder:
    def __init__(self) -> None:
        self.blobs: dict = {}
        self.vectors: list = []
        self.seen: set = set()
        self.depth = 0

    def blob(self, data: bytes) -> str:
        h = _sha(data)
        self.blobs[h] = data
        return h

    def add(self, vector: dict) -> None:
        key = json.dumps(vector, sort_keys=True)
        if key not in self.seen:
            self.seen.add(key)
            self.vectors.append(vector)

    def command(self, args: list, cwd: Path, source: str) -> None:
        files = {}
        for a in args:
            p = cwd / a
            if a and not a.startswith("-") and "/" not in a and p.is_file():
                files[a] = self.blob(p.read_bytes())
        self.add({"kind": "command", "argv": list(args), "files": files, "source": source})

    def parse(self, data: bytes, encoding: str, source: str) -> None:
        self.add({"kind": "parse", "input": self.blob(bytes(data)), "encoding": encoding, "source": source})

    def call(self, fn: str, bundles: tuple, require, kernels, source: str) -> None:
        try:
            texts = [json.dumps(b, sort_keys=True) for b in bundles]
        except (TypeError, ValueError):
            return  # not a bundle a reader could hold
        self.add({"kind": "call", "function": fn, "bundles": [self.blob(t.encode()) for t in texts],
                  "require": [k.hex() for k in require or []], "kernels": [self.blob(m) for m in kernels or ()],
                  "source": source})


def _record_tests(rec: Recorder) -> None:
    sys.path[:0] = [str(ROOT)]
    import vars1 as V
    import minds_verify as MV
    import test_vars1 as T

    current = {"test": None}
    real_run = subprocess.run

    def run(args, *a, **kw):
        argv = [str(x) for x in args] if isinstance(args, (list, tuple)) else []
        if "minds_verify.py" in argv:
            i = argv.index("minds_verify.py")
            rec.command(argv[i + 1:], Path(kw.get("cwd") or "."), current["test"])
        return real_run(args, *a, **kw)

    originals = {name: getattr(MV, name) for name in FUNCTIONS}

    def wrap(name):
        inner = originals[name]

        def parsed(kernel_input, encoding="v1"):
            if rec.depth == 0 and isinstance(kernel_input, (bytes, bytearray)) and isinstance(encoding, str):
                rec.parse(kernel_input, encoding, current["test"])
            rec.depth += 1
            try:
                return inner(kernel_input, encoding)
            finally:
                rec.depth -= 1

        def recorded(*bundles, require=None, kernels=(), timeout=MV.KERNEL_TIMEOUT):
            if rec.depth == 0 and timeout == MV.KERNEL_TIMEOUT:
                rec.call(name, bundles, require, list(kernels), current["test"])
            rec.depth += 1
            try:
                if name == "compare_projections":
                    return inner(*bundles)
                return inner(*bundles, require=require, kernels=kernels, timeout=timeout)
            finally:
                rec.depth -= 1
        return parsed if name == "parse_kernel_input" else recorded

    subprocess.run = run
    for name in FUNCTIONS:
        setattr(MV, name, wrap(name))
        setattr(V, name, getattr(MV, name))
    try:
        for test in OFFLINE_TESTS:
            current["test"] = test
            result = unittest.TextTestRunner(stream=io.StringIO(), verbosity=0).run(
                unittest.TestLoader().loadTestsFromName(f"TestVars1Conformance.{test}", T))
            if not result.wasSuccessful():
                raise SystemExit(f"{test} failed while recorded: {(result.failures + result.errors)[0][1][-600:]}")
    finally:
        subprocess.run = real_run
        for name in FUNCTIONS:
            setattr(MV, name, originals[name])
            setattr(V, name, originals[name])


def _spoiled(rec: Recorder) -> None:
    """One real bundle (the first projection bundle a test gave the command line), spoiled as text: what read_bundle
    and bytes.fromhex refuse or read, in Python's words."""
    bundle = None
    for v in rec.vectors:
        if v["kind"] == "command" and v["argv"][:1] == ["inspect-projection"]:
            doc = json.loads(rec.blobs[v["files"][v["argv"][1]]])
            if isinstance(doc, dict) and "input" in doc:
                bundle = doc
                break
    assert bundle is not None, "no projection bundle was given to the command line"
    text = json.dumps(bundle, sort_keys=True)
    cases = []
    for n in sorted({0, 1, 2, 9, 10, len(text) // 3, len(text) // 2, len(text) - 2, len(text) - 1}):
        cases.append(("truncated", text[:n].encode()))
    cases += [
        ("bom", b"\xef\xbb\xbf" + text.encode()),
        ("invalid utf-8", text.encode()[:20] + b"\xff" + text.encode()[20:]),
        ("an overlong slash", text.encode()[:20] + b"\xc0\xaf" + text.encode()[20:]),
        ("a cut sequence", text.encode() + b"\xe2\x82"),
        ("an overlong three-byte sequence", text.encode()[:20] + b"\xe0\x80\x80" + text.encode()[20:]),
        ("an encoded surrogate", text.encode()[:20] + b"\xed\xa0\x80" + text.encode()[20:]),
        ("a code point above U+10FFFF", text.encode()[:20] + b"\xf4\x90\x80\x80" + text.encode()[20:]),
        ("a repeated key", text.replace('{"atoms"', '{"cell": "00", "atoms"', 1).encode()),
        ("a nested repeated key", json.dumps({"format": bundle["format"], "x": {"a": 1, "a": 2}}).replace(
            '"x": {"a": 2}', '"x": {"a": 1, "a": 2}').encode()),
        ("NaN", text.replace('{"atoms"', '{"n": NaN, "atoms"', 1).encode()),
        ("-Infinity", text.replace('{"atoms"', '{"n": -Infinity, "atoms"', 1).encode()),
        ("a trailing comma", text[:-1].encode() + b",}"),
        ("a trailing comma in a list", text.replace('"], "cell"', '",], "cell"', 1).encode()),
        ("a control character", text.replace('"format"', '"for\x01mat"', 1).encode()),
        ("an invalid escape", text.replace('"format"', '"for\\xmat"', 1).encode()),
        ("a short \\u escape", text.replace('"format"', '"for\\u12mat"', 1).encode()),
        ("a lone surrogate", text.replace('"format"', '"for\\ud800mat"', 1).encode()),
        ("a surrogate pair", text.replace('"format"', '"for\\ud83d\\ude00mat"', 1).encode()),
        ("extra data", text.encode() + b" {}"),
        ("two lines", text.replace(", ", ",\n", 3).encode() + b"\n x"),
        ("not an object", b"[1, 2.5, -0, 1e400, 12345678901234567890]"),
        ("a big number in the format", text.replace(f'"{bundle["format"]}"', "123456789012345678901234567890", 1).encode()),
        ("a float in the format", text.replace(f'"{bundle["format"]}"', "1.5", 1).encode()),
        ("whitespace inside the cell hex", text.replace(bundle["cell"], " ".join(bundle["cell"][i:i + 2] for i in range(0, len(bundle["cell"]), 2)), 1).encode()),
        ("the cell hex in upper case", text.replace(bundle["cell"], bundle["cell"].upper(), 1).encode()),
        ("an odd cell hex", text.replace(bundle["cell"], bundle["cell"][:-1], 1).encode()),
        ("a non-ASCII digit in the cell hex", text.replace(bundle["cell"], bundle["cell"][:6] + "\\u0661" + bundle["cell"][7:], 1).encode()),
        ("a split pair in the cell hex", text.replace(bundle["cell"], bundle["cell"][:5] + " " + bundle["cell"][5:], 1).encode()),
    ]
    for field in ("cell", "atoms", "seals", "input", "output"):
        for name, value in (("absent", None), ("a number", 5), ("a float", 1.5), ("true", True), ("null", "null"),
                            ("a list", []), ("an object", {}), ("a string", "zz")):
            doc = dict(bundle)
            if value is None:
                del doc[field]
            else:
                doc[field] = None if value == "null" else value
            cases.append((f"{field}: {name}", json.dumps(doc, sort_keys=True).encode()))
    seals = bundle["seals"]
    if seals:
        s = seals[0]
        for name, bad in (("a flipped signature byte", s[:-2] + ("00" if s[-2:] != "00" else "01")),
                          ("a flipped key byte", s[:136] + ("00" if s[136:138] != "00" else "01") + s[138:]),
                          ("a short seal", s[:-2]),
                          ("S = L", s[:200] + (2**252 + 27742317777372353535851937790883648493).to_bytes(32, "little").hex()),
                          ("a small-order R", s[:200 - 128] + "01" + "00" * 31 + s[200 - 64:])):
            cases.append((f"seal: {name}", json.dumps(dict(bundle, seals=[bad] + seals[1:]), sort_keys=True).encode()))
        cases += _forged(bundle)
        cases.append(("seals as an object", json.dumps(dict(bundle, seals={x: 1 for x in seals}), sort_keys=True).encode()))
        cases.append(("seals as a string", json.dumps(dict(bundle, seals=seals[0]), sort_keys=True).encode()))
    for name, data in cases:
        h = rec.blob(data)
        for cmd in ("inspect-projection", "inspect-attestation", "verify-projection"):
            argv = [cmd, "bundle.json"] + (["--require", "00" * 32] if cmd.startswith("verify") else [])
            rec.add({"kind": "command", "argv": argv, "files": {"bundle.json": h}, "source": f"spoiled: {name}"})
    for name, pin in (("an upper-case pin", "AB" * 32), ("a pin with spaces", "ab " * 32), ("an odd pin", "abc"),
                      ("a non-hex pin", "zz"), ("a non-ASCII pin", "ab\u0661"), ("a non-ASCII pin after a bad digit", "zz\u0661")):
        h = rec.blob(text.encode())
        rec.add({"kind": "command", "argv": ["verify-projection", "bundle.json", "--require", pin],
                 "files": {"bundle.json": h}, "source": f"pins: {name}"})
    for argv in (["verify-projection"], ["verify-projection", "bundle.json", "--require"],
                 ["verify-projection", "bundle.json", "--pin", "00"], ["nonsense", "bundle.json"], [],
                 ["verify-projection", "bundle.json"], ["verify-extends", "bundle.json"]):
        rec.add({"kind": "command", "argv": argv, "files": {"bundle.json": rec.blob(text.encode())} if "bundle.json" in argv else {},
                 "source": "command line"})


def _forged(bundle: dict) -> list:
    """Seals that verify under the cofactorless equation yet are refused by the filters minds_verify.py applies before
    it: one whose R is the identity (a small-order point), made with the secret key of a seal of the bundle (the tests'
    keys are fixed bytes), and one by the identity as public key. A host's Ed25519 may accept both, so they test the
    filters of the port, not the host."""
    import minds_verify as MV
    seal = MV.Seal.decode(bytes.fromhex(bundle["seals"][0]))
    sk = next((bytes([i]) * 32 for i in range(256) if MV.ed25519_pubkey(bytes([i]) * 32) == seal.actor_pubkey), None)
    if sk is None:
        return []
    msg = b"SEAL" + seal.h_target + seal.h_scope_ctx + seal.actor_pubkey
    h = hashlib.sha512(sk).digest()
    a = (int.from_bytes(h[:32], "little") & ((1 << 254) - 8)) | (1 << 254)
    R = bytes([1]) + bytes(31)
    k = int.from_bytes(hashlib.sha512(R + seal.actor_pubkey + msg).digest(), "little") % MV._L
    weak_r = msg + R + (k * a % MV._L).to_bytes(32, "little")
    identity = bytes([1]) + bytes(31)
    msg_i = b"SEAL" + seal.h_target + seal.h_scope_ctx + identity
    r = 5
    weak_a = msg_i + MV._ed_enc(MV._ed_mul(MV._B, r)) + r.to_bytes(32, "little")
    assert MV._ed_enc(MV._ed_mul(MV._B, k * a % MV._L)) == MV._ed_enc(MV._ed_add(MV._ed_dec(R), MV._ed_mul(MV._ed_dec(seal.actor_pubkey), k)))
    out = []
    for name, raw in (("a seal whose R is the identity", weak_r), ("a seal by the identity as key", weak_a)):
        out.append((f"seal: {name}", json.dumps(dict(bundle, seals=[raw.hex()] + bundle["seals"]), sort_keys=True).encode()))
    return out


def _live(rec: Recorder, folder: Path) -> None:
    """The published bundles of the live chain (an index.json and the files it names), as a reader fetches them."""
    index = json.loads((folder / "index.json").read_text())
    roster = [m["key"] for m in index["roster"]]
    att, proj = index["attestation"]["file"], index["projection"]["file"]
    files = {"attestation.json": rec.blob((folder / att).read_bytes()), "projection.json": rec.blob((folder / proj).read_bytes())}
    pins = [x for k in roster for x in ("--require", k)]
    both = [x for k in roster if k in index["attestation"]["endorsers"] and k in index["projection"]["witnesses"]
            for x in ("--require", k)]  # the page's default: keys that endorsed the release and witnessed the projection
    singles = [["verify-attestation", "attestation.json", "--require", k] for k in roster]
    for argv in (["inspect-attestation", "attestation.json"], ["verify-attestation", "attestation.json", *pins],
                 ["verify-attestation", "attestation.json", *both], *singles,
                 ["inspect-projection", "projection.json"], ["verify-projection", "projection.json", *pins],
                 ["verify-extends", "projection.json", "attestation.json"],
                 ["verify-equivocation", "projection.json", "attestation.json"]):
        rec.add({"kind": "command", "argv": argv, "files": {a: files[a] for a in argv if a in files}, "source": "live"})


def _environment() -> dict:
    node = shutil.which("node")
    if node is None:
        raise SystemExit("the vectors are answered with Node on PATH (a --kernel vector runs the rules under it)")
    return {"PATH": str(Path(node).parent)}


def answer(vector: dict, blobs: dict) -> dict:
    """What this checkout's minds_verify.py answers to one vector."""
    import minds_verify as MV
    if vector["kind"] == "command":
        with tempfile.TemporaryDirectory() as tmp:
            for name, h in vector["files"].items():
                (Path(tmp) / name).write_bytes(blobs[h])
            out, err = io.StringIO(), io.StringIO()
            here = os.getcwd()
            path = os.environ.get("PATH")
            os.environ["PATH"] = _environment()["PATH"]
            os.chdir(tmp)
            try:
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    code = MV.main(list(vector["argv"]))
            finally:
                os.chdir(here)
                os.environ["PATH"] = path or ""
            return {"code": code, "stdout": out.getvalue(), "stderr": err.getvalue()}
    if vector["kind"] == "parse":
        try:
            ki = MV.parse_kernel_input(blobs[vector["input"]], vector["encoding"])
        except Exception as e:  # noqa: BLE001
            return {"raised": type(e).__name__, "message": str(e)}
        plain = lambda v: (v.hex() if isinstance(v, bytes) else [plain(x) for x in v] if isinstance(v, (list, tuple))
                           else {(k.hex() if isinstance(k, bytes) else k): plain(x) for k, x in v.items()} if isinstance(v, dict) else v)
        return {"result": json.dumps(plain(ki), indent=2, sort_keys=True)}
    fn = getattr(MV, vector["function"])
    bundles = [json.loads(blobs[h]) for h in vector["bundles"]]
    try:
        if vector["function"] == "compare_projections":
            result = fn(*bundles)
        else:
            result = fn(*bundles, require=[bytes.fromhex(k) for k in vector["require"]],
                        kernels=[blobs[h] for h in vector["kernels"]])
    except Exception as e:  # noqa: BLE001 - the class and words are the answer
        return {"raised": type(e).__name__, "message": str(e)}
    return {"result": json.dumps(result, indent=2, sort_keys=True)}


def _load() -> tuple:
    doc = json.loads(VECTORS.read_text())
    if doc.get("format") != FORMAT:
        raise SystemExit(f"{VECTORS} is not {FORMAT}")
    blobs = {h: (bytes.fromhex(v[4:]) if v.startswith("hex:") else v.encode("utf-8", "surrogatepass")) for h, v in doc["blobs"].items()}
    for h, data in blobs.items():
        if _sha(data) != h:
            raise SystemExit(f"blob {h[:12]} does not hash to its name")
    return doc, blobs


def _blob_text(data: bytes) -> str:
    """A blob as the file keeps it: UTF-8 text when it is, else `hex:` and its bytes."""
    try:
        text = data.decode("utf-8")
        if not text.startswith("hex:"):
            return text
    except UnicodeDecodeError:
        pass
    return "hex:" + data.hex()


def check() -> list:
    """Every vector's recorded answer is what minds_verify.py answers now; the differences, by index and source."""
    sys.path[:0] = [str(ROOT), str(ROOT / "verify")]
    doc, blobs = _load()
    return [(i, v["source"]) for i, v in enumerate(doc["vectors"]) if answer(v, blobs) != v["answer"]]


def main(argv: list) -> int:
    if argv[:1] == ["export"] and len(argv) in (1, 3) and argv[1:2] in ([], ["--live"]):
        rec = Recorder()
        _record_tests(rec)
        _spoiled(rec)
        if len(argv) == 3:
            _live(rec, Path(argv[2]))
        for v in rec.vectors:
            v["answer"] = answer(v, rec.blobs)
        used = {h for v in rec.vectors for h in [*v.get("files", {}).values(), *v.get("bundles", []), *v.get("kernels", []),
                                                  *([v["input"]] if "input" in v else [])]}
        doc = {"format": FORMAT,
               "about": "Inputs the offline tests gave verify/minds_verify.py, spoiled bundles and the live bundles, "
                        "with that file's answers (tools/verify_vectors.py). verify/minds_verify.mjs must answer the same bytes.",
               "tests": list(OFFLINE_TESTS),
               "blobs": {h: _blob_text(rec.blobs[h]) for h in sorted(used)},
               "vectors": rec.vectors}
        VECTORS.write_text(json.dumps(doc, indent=1, sort_keys=True, ensure_ascii=True) + "\n")
        kinds = {k: sum(v["kind"] == k for v in rec.vectors) for k in ("command", "call", "parse")}
        print(json.dumps({"vectors": len(rec.vectors), **kinds, "blobs": len(used), "bytes": VECTORS.stat().st_size}))
        return 0
    if argv == ["check"]:
        bad = check()
        print(json.dumps({"differences": bad[:20], "count": len(bad)}))
        return 1 if bad else 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
