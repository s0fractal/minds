#!/usr/bin/env python3
"""VARS-1 reference implementation (no dependencies beyond `sigma-glyph`'s `sigma_resume`).

Section numbers refer to VARS-1-SPEC.md: objects (§1), standard schemas (§2), store and admission gate (§3),
fold and lens (§4), replay against Book I (§5). The fold and lens Passes 1-2 are decided by `kernel/lens.wasm`;
the Python fold and passes here are its differential twin.
"""
from __future__ import annotations

import hashlib
import json
import re
import struct
import shutil
import subprocess
import tempfile
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

# ---------------------------------------------------------------------------
# Pure-Python RFC 8032 Ed25519 + Warrant `weak_public_key` filter
# ---------------------------------------------------------------------------
_Q = 2**255 - 19
_L = 2**252 + 27742317777372353535851937790883648493
_D = -121665 * pow(121666, _Q - 2, _Q) % _Q
_I = pow(2, (_Q - 1) // 4, _Q)

# Exact 10 small-order / torsion encodings from `warrant/warrant/keys.py:18-29`
_WEAK_PUBKEYS: Set[bytes] = {
    bytes.fromhex(h)
    for h in (
        "0100000000000000000000000000000000000000000000000000000000000000",
        "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a",
        "0000000000000000000000000000000000000000000000000000000000000080",
        "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05",
        "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa",
        "0100000000000000000000000000000000000000000000000000000000000080",
        "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    )
}


def weak_public_key(raw: bytes) -> bool:
    """True iff `raw` is not a 32-byte strong canonical Ed25519 public key (`warrant/keys.py:32-35`)."""
    if not isinstance(raw, bytes) or len(raw) != 32 or raw in _WEAK_PUBKEYS:
        return True
    return (int.from_bytes(raw, "little") & ((1 << 255) - 1)) >= _Q


def _xrecover(y: int) -> int:
    xx = (y * y - 1) * pow(_D * y * y + 1, _Q - 2, _Q) % _Q
    x = pow(xx, (_Q + 3) // 8, _Q)
    if (x * x - xx) % _Q != 0:
        x = (x * _I) % _Q
    return _Q - x if x % 2 != 0 else x


_BY = 4 * pow(5, _Q - 2, _Q) % _Q
_BX = _xrecover(_BY)
_B = (_BX % _Q, _BY % _Q, 1, (_BX * _BY) % _Q)


def _ed_add(P: Tuple[int, int, int, int], Qp: Tuple[int, int, int, int]) -> Tuple[int, int, int, int]:
    x1, y1, z1, t1 = P
    x2, y2, z2, t2 = Qp
    a = (y1 - x1) * (y2 - x2) % _Q
    b = (y1 + x1) * (y2 + x2) % _Q
    c = t1 * 2 * _D * t2 % _Q
    dd = z1 * 2 * z2 % _Q
    e, f, g, h = b - a, dd - c, dd + c, b + a
    return (e * f % _Q, g * h % _Q, f * g % _Q, e * h % _Q)


def _ed_mul(P: Tuple[int, int, int, int], e: int) -> Tuple[int, int, int, int]:
    R = (0, 1, 1, 0)
    addend = P
    while e > 0:
        if e & 1:
            R = _ed_add(R, addend)
        addend = _ed_add(addend, addend)
        e >>= 1
    return R


def _ed_enc(P: Tuple[int, int, int, int]) -> bytes:
    x, y, z, _ = P
    zi = pow(z, _Q - 2, _Q)
    x, y = (x * zi) % _Q, (y * zi) % _Q
    out = bytearray(y.to_bytes(32, "little"))
    out[31] |= (x & 1) << 7
    return bytes(out)


@lru_cache(maxsize=4096)
def _ed_dec(s: bytes) -> Tuple[int, int, int, int]:
    if len(s) != 32:
        raise ValueError("invalid Ed25519 point length")
    y = int.from_bytes(s, "little") & ((1 << 255) - 1)
    if y >= _Q:
        raise ValueError("Ed25519 y out of range")
    sign = (s[31] >> 7) & 1
    x = _xrecover(y)
    if (x * x * (_D * y * y + 1) - (y * y - 1)) % _Q != 0 or (x == 0 and sign == 1):
        raise ValueError("point not on Curve25519")
    if (x & 1) != sign:
        x = _Q - x
    return (x, y, 1, (x * y) % _Q)


@lru_cache(maxsize=4096)
def ed25519_pubkey(sk: bytes) -> bytes:
    if len(sk) != 32:
        raise ValueError("Ed25519 secret key must be 32 bytes")
    h = hashlib.sha512(sk).digest()
    a = (int.from_bytes(h[:32], "little") & ((1 << 254) - 8)) | (1 << 254)
    return _ed_enc(_ed_mul(_B, a))


@lru_cache(maxsize=4096)
def ed25519_sign(sk: bytes, msg: bytes) -> bytes:
    h = hashlib.sha512(sk).digest()
    a = (int.from_bytes(h[:32], "little") & ((1 << 254) - 8)) | (1 << 254)
    pk = _ed_enc(_ed_mul(_B, a))
    r = int.from_bytes(hashlib.sha512(h[32:] + msg).digest(), "little") % _L
    R = _ed_enc(_ed_mul(_B, r))
    k = int.from_bytes(hashlib.sha512(R + pk + msg).digest(), "little") % _L
    S = (r + k * a) % _L
    return R + S.to_bytes(32, "little")


@lru_cache(maxsize=4096)
def ed25519_verify(pk: bytes, msg: bytes, sig: bytes) -> bool:
    if weak_public_key(pk) or not isinstance(sig, bytes) or len(sig) != 64:
        return False
    if weak_public_key(sig[:32]):
        return False
    try:
        A, R = _ed_dec(pk), _ed_dec(sig[:32])
    except ValueError:
        return False
    S = int.from_bytes(sig[32:], "little")
    if S >= _L:
        return False
    k = int.from_bytes(hashlib.sha512(sig[:32] + pk + msg).digest(), "little") % _L
    return _ed_enc(_ed_mul(_B, S)) == _ed_enc(_ed_add(R, _ed_mul(A, k)))


# ---------------------------------------------------------------------------
# §1 Intrinsic Constants & Hash Helpers
# ---------------------------------------------------------------------------
def sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


MAX_INT = 2**53 - 1
MAX_STATE_BYTES = 64 * 1024 * 1024
MAX_UTF8_BYTES = 64 * 1024
MAX_LOSS_BYTES = 4096
MAX_HVEC_LEN = 65535
SLOT_NAME_RE = re.compile(
    r"^[a-zA-Z0-9][a-zA-Z0-9_-]{0,31}/[a-zA-Z0-9][a-zA-Z0-9_.-]{0,63}(/[a-zA-Z0-9][a-zA-Z0-9_.-]{0,63})*$"
)


def validate_slot_name(slot_str: str) -> None:
    """Validate `<scope>/<name>`: no `..`, no `.lock`, no leading/trailing `.` or `/`."""
    if not (1 <= len(slot_str) <= 128) or not SLOT_NAME_RE.match(slot_str):
        raise VarsError(f"invalid slot name syntax: {slot_str!r}")
    for seg in slot_str.split("/"):
        if ".." in seg or seg.endswith(".lock") or seg.endswith("."):
            raise VarsError(f"forbidden path segment in slot name: {slot_str!r}")


H_I = bytes.fromhex("2f33694d09810641fa5b8c47a7c0dc42e1b99eb8c9784a00aaee9a66330f4162")
H_K = bytes.fromhex("bc0c2fe26e44e2aed8ce500a74963bc270fd4a49ec0c2e4837ce7a64bb0a486c")
H_S = bytes.fromhex("887045bc22935aec5cba2dc11400d4e4357bc34d06681a6e92f06e7795b1f8a6")
H_FALSE = bytes.fromhex("65cd957fee7ec9fb310bc9d9712cec1726c78f8026fda679ac8f237938a32098")
H_INVALID = bytes.fromhex("af69b5176c7ac3855c2eac3d1f6159c74d5328e92aac0a33cdba68bbaeba4507")

H_EMPTY = sha256(b"HVEC")
H_META_SCHEMA = sha256(b"VARS-META-SCHEMA-V1")
H_ZERO = sha256(b"U64\x00" + b"\x00" * 8)

H_NORMAL_FORM = sha256(b"UTF8NORMAL_FORM")
H_PAUSED = sha256(b"UTF8PAUSED")
H_BLOCKED_REF = sha256(b"UTF8BLOCKED_REFERENCE")
H_CYCLE_PROVEN = sha256(b"UTF8CYCLE_PROVEN")
H_REPLAYED = sha256(b"UTF8REPLAYED")
H_ATTESTED = sha256(b"UTF8ATTESTED")
H_VERDICT_INVALID = sha256(b"UTF8INVALID")
H_NOT_ASSESSED = sha256(b"UTF8NOT_ASSESSED")
H_PROVISIONAL = sha256(b"UTF8provisional")
H_OWNER = sha256(b"UTF8owner")

# The rules a scope is evaluated under are a stored object: the compiled rules kernel (`kernel/`, Rust -> wasm32,
# reproducible). A scope names it by hash; this host implements exactly these rules.
KERNEL_DIR = Path(__file__).resolve().parent / "kernel"
H_LENS_KERNEL = bytes.fromhex("874e714dd14e6d7c144a4c377ae649f4124ea3788b17fa1ff86cf1be8a168ecb")
KERNEL_ATOM = (KERNEL_DIR / "lens.wasm").read_bytes()
if sha256(KERNEL_ATOM) != H_LENS_KERNEL:
    raise RuntimeError("kernel/lens.wasm does not hash to H_LENS_KERNEL")
# Rules v2 (RULES-V2.md, prototype): typed cell references, explicit in the kernel input. A scope's epoch runs the
# rules it names; this host keeps both modules, so every past tip stays recomputable under the rules it had.
KERNEL2_DIR = Path(__file__).resolve().parent / "kernel2"
H_LENS_KERNEL_V2 = bytes.fromhex("4605f0db0df40b98ba888a23463d8bd6b540fb74f94eeb297065481af1f14297")
KERNEL2_ATOM = (KERNEL2_DIR / "lens2.wasm").read_bytes()
if sha256(KERNEL2_ATOM) != H_LENS_KERNEL_V2:
    raise RuntimeError("kernel2/lens2.wasm does not hash to H_LENS_KERNEL_V2")
RULES_MODULES: Dict[bytes, Path] = {H_LENS_KERNEL: KERNEL_DIR / "lens.wasm", H_LENS_KERNEL_V2: KERNEL2_DIR / "lens2.wasm"}
RULES_ATOMS: Dict[bytes, bytes] = {H_LENS_KERNEL: KERNEL_ATOM, H_LENS_KERNEL_V2: KERNEL2_ATOM}
KERNEL2_MAGIC = 0x32524156  # "VAR2": the first word of a v2 kernel input

INTRINSIC_HASHES: Set[bytes] = {
    H_I, H_K, H_S, H_FALSE, H_INVALID,
    H_EMPTY, H_META_SCHEMA, H_ZERO,
    H_NORMAL_FORM, H_PAUSED, H_BLOCKED_REF, H_CYCLE_PROVEN,
    H_REPLAYED, H_ATTESTED, H_VERDICT_INVALID, H_NOT_ASSESSED,
    H_PROVISIONAL, H_OWNER,
}


INTRINSIC_UTF8: Set[bytes] = {
    H_NORMAL_FORM, H_PAUSED, H_BLOCKED_REF, H_CYCLE_PROVEN,
    H_REPLAYED, H_ATTESTED, H_VERDICT_INVALID, H_NOT_ASSESSED,
    H_PROVISIONAL, H_OWNER,
}
# Intrinsic atoms are known without reading the store (§1): their bytes, for every consumer that reads a value
INTRINSIC_ATOMS: Dict[bytes, bytes] = {sha256(raw): raw for raw in (
    b"HVEC", b"U64\x00" + b"\x00" * 8,
    *(b"UTF8" + t for t in (b"NORMAL_FORM", b"PAUSED", b"BLOCKED_REFERENCE", b"CYCLE_PROVEN", b"REPLAYED",
                            b"ATTESTED", b"INVALID", b"NOT_ASSESSED", b"provisional", b"owner")),
)}


assert set(INTRINSIC_ATOMS) <= INTRINSIC_HASHES


def atom_of(h: bytes, atoms: Dict[bytes, bytes], what: str = "atom") -> bytes:
    """The bytes of atom `h`, stored or intrinsic: whether an intrinsic is materialized never changes a result."""
    raw = atoms.get(h)
    if raw is None:
        raw = INTRINSIC_ATOMS.get(h)
    if raw is None:
        raise VarsError(f"{what} {h.hex()[:12]} missing from cas/atoms/")
    return raw


def u64_of(h: bytes, atoms: Dict[bytes, bytes], what: str = "u64") -> int:
    return parse_u64(atom_of(h, atoms, what))


# Fields that may hold H_EMPTY to mean "none"; every other slot must have its declared type.
# Closed: a schema naming another type is refused at the gate, so check_slot_type never sees one
FIELD_TYPES = {"utf8", "u64", "pol1", "root", "digest", "wasm", "cell", "hash"}
VERDICT_CODES = {H_REPLAYED, H_ATTESTED, H_VERDICT_INVALID, H_NOT_ASSESSED}
OPTIONAL_FIELDS = {"required_comp", "expected_outcome", "evaluator_policy", "ckpt_or_witness"}


class VarsError(ValueError):
    """Raised when an Atom, Cell, Seal, or Admission Gate check fails."""


# ---------------------------------------------------------------------------
# §1.1 Class 0: Atom Encoding & Validation
# ---------------------------------------------------------------------------
def atom_u64(val: int) -> bytes:
    if type(val) is not int or not (0 <= val <= MAX_INT):
        raise VarsError(f"U64 out of domain 0..2^53-1: {val!r}")
    return b"U64\x00" + val.to_bytes(8, "big")


def parse_u64(raw: bytes) -> int:
    if len(raw) != 12 or raw[:4] != b"U64\x00":
        raise VarsError("invalid U64 atom")
    val = int.from_bytes(raw[4:], "big")
    if val > MAX_INT:
        raise VarsError(f"U64 exceeds 2^53-1: {val}")
    return val


def atom_utf8(text: str) -> bytes:
    if not isinstance(text, str):
        raise VarsError("UTF8 atom requires str")
    raw = text.encode("utf-8")
    validate_utf8_atom(b"UTF8" + raw)
    return b"UTF8" + raw


def parse_utf8(raw: bytes) -> str:
    validate_utf8_atom(raw)
    return raw[4:].decode("utf-8")


def validate_utf8_atom(raw: bytes) -> None:
    if len(raw) < 4 or raw[:4] != b"UTF8":
        raise VarsError("missing UTF8 magic")
    body = raw[4:]
    if len(body) > MAX_UTF8_BYTES:
        raise VarsError("UTF8 atom exceeds 64 KiB")
    if b"\x00" in body or b"\r" in body:
        raise VarsError("UTF8 atom contains NUL or CR byte")
    if body and (body[0] in (0x20, 0x09, 0x0A) or body[-1] in (0x20, 0x09, 0x0A)):
        raise VarsError("UTF8 atom has leading or trailing ASCII whitespace")
    try:
        body.decode("utf-8", errors="strict")
    except UnicodeDecodeError as e:
        raise VarsError(f"invalid UTF-8: {e}") from None


def atom_hvec(hashes: Iterable[bytes], *, sorted_set: bool = True) -> bytes:
    items = list(hashes)
    for h in items:
        if not isinstance(h, bytes) or len(h) != 32:
            raise VarsError("HVEC element must be 32 bytes")
    if sorted_set:
        items = sorted(set(items))
    if len(items) > MAX_HVEC_LEN:
        raise VarsError("HVEC exceeds 65535 elements")
    return b"HVEC" + b"".join(items)


def parse_hvec(raw: bytes, *, require_sorted: bool = True) -> List[bytes]:
    if len(raw) < 4 or raw[:4] != b"HVEC" or (len(raw) - 4) % 32 != 0:
        raise VarsError("invalid HVEC atom layout")
    n = (len(raw) - 4) // 32
    if n > MAX_HVEC_LEN:
        raise VarsError("HVEC exceeds 65535 elements")
    items = [raw[4 + 32 * i : 4 + 32 * (i + 1)] for i in range(n)]
    if require_sorted:
        for i in range(len(items) - 1):
            if items[i] >= items[i + 1]:
                raise VarsError("HVEC elements are not strictly ascending")
    return items


def atom_pol1(threshold: int, pubkeys_hvec_hash: bytes) -> bytes:
    if type(threshold) is not int or not (1 <= threshold <= MAX_HVEC_LEN):
        raise VarsError(f"invalid POL1 threshold: {threshold}")
    if len(pubkeys_hvec_hash) != 32:
        raise VarsError("POL1 pubkeys_hvec_hash must be 32 bytes")
    return b"POL1" + threshold.to_bytes(2, "big") + pubkeys_hvec_hash


def parse_pol1(raw: bytes) -> Tuple[int, bytes]:
    if len(raw) != 38 or raw[:4] != b"POL1":
        raise VarsError("invalid POL1 atom")
    threshold = int.from_bytes(raw[4:6], "big")
    if threshold < 1:
        raise VarsError("POL1 threshold must be >= 1")
    return threshold, raw[6:38]


def atom_environment(node_hashes: Iterable[bytes]) -> bytes:
    hexes = sorted({h.hex() for h in node_hashes})
    if len(hexes) > MAX_HVEC_LEN:
        raise VarsError("Environment exceeds 65535 hashes")
    doc = {"schema": "sigma-resume.environment@draft-1", "hashes": hexes}
    return json.dumps(doc, sort_keys=True, separators=(",", ":")).encode("utf-8")


def atom_computation_root(
    input_term_hash: bytes,
    environment_id: bytes,
    runtime_id: str = "sigma-book1-0.6.0/hash-thunk/leftmost-outermost",
    cost_model_id: str = "atp/size-priced/adr-001+adr-003",
) -> bytes:
    doc = {
        "schema": "sigma-resume.root@draft-1",
        "runtime_semantics_id": runtime_id,
        "cost_model_id": cost_model_id,
        "input_term_hash": input_term_hash.hex(),
        "environment_id": environment_id.hex(),
    }
    return json.dumps(doc, sort_keys=True, separators=(",", ":")).encode("utf-8")


def validate_atom(raw: bytes) -> None:
    if not raw:
        raise VarsError("empty atom")
    if raw[:4] == b"UTF8":
        validate_utf8_atom(raw)
    elif raw[:4] == b"U64\x00":
        parse_u64(raw)
    elif raw[:4] == b"HVEC":
        parse_hvec(raw, require_sorted=False)
    elif raw[:4] == b"POL1":
        parse_pol1(raw)
    elif raw[:4] == b"SGS1":
        if len(raw) > MAX_STATE_BYTES or len(raw) < 4 + 32 + 33:
            raise VarsError("invalid SGS1 state size")
        sgs1_term_hash(raw)  # the whole state parses
    elif raw[:1] == b"{":
        try:
            doc = json.loads(raw.decode("utf-8"))
        except Exception as e:
            raise VarsError(f"invalid JSON atom: {e}") from None
        if json.dumps(doc, sort_keys=True, separators=(",", ":")).encode("utf-8") != raw:
            raise VarsError("non-canonical JSON atom")
        hex64 = lambda v: isinstance(v, str) and len(v) == 64 and all(ch in "0123456789abcdef" for ch in v)
        if doc.get("schema") == "sigma-resume.root@draft-1":
            if set(doc) != {"schema", "runtime_semantics_id", "cost_model_id", "input_term_hash", "environment_id"} \
                    or not all(isinstance(doc[k], str) and doc[k] for k in ("runtime_semantics_id", "cost_model_id")) \
                    or not hex64(doc["input_term_hash"]) or not hex64(doc["environment_id"]):
                raise VarsError("ComputationRoot must have exactly its five fields, well typed")
        elif doc.get("schema") == "sigma-resume.environment@draft-1":
            hs = doc.get("hashes")
            if set(doc) != {"schema", "hashes"} or not isinstance(hs, list) or not all(hex64(x) for x in hs) \
                    or hs != sorted(set(hs)) or len(hs) > MAX_HVEC_LEN:
                raise VarsError("Environment must be its schema and a sorted, distinct list of hashes")
        else:
            raise VarsError("unknown JSON atom schema")
    elif raw[:8] == b"\x00asm\x01\x00\x00\x00":
        pass  # a wasm module: identity is its hash; only the rules this host implements are ever executed
    elif raw[0] in (0x00, 0x01, 0x02, 0xFF):
        if SR.G.deser(raw) is None:
            raise VarsError("invalid SigmaNodeV2 node")
    else:
        raise VarsError(f"unrecognized atom prefix: {raw[:4]!r}")


# ---------------------------------------------------------------------------
# §1.2 Class 1: Unsigned VAR1 Cell (`296 + 32*K` bytes)
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Cell:
    h_schema: bytes
    h_slot_name: bytes
    h_payload: bytes
    h_relies: bytes = H_EMPTY
    h_attests: bytes = H_EMPTY
    h_supersedes: bytes = H_EMPTY
    h_retires: bytes = H_EMPTY
    h_invalidates: bytes = H_EMPTY
    h_loss: bytes = H_EMPTY
    slots: Tuple[bytes, ...] = ()

    def encode(self) -> bytes:
        k = len(self.slots)
        if k > 64:
            raise VarsError(f"arity {k} > 64")
        fields = [
            self.h_schema, self.h_slot_name, self.h_payload,
            self.h_relies, self.h_attests, self.h_supersedes,
            self.h_retires, self.h_invalidates, self.h_loss,
            *self.slots,
        ]
        for f in fields:
            if not isinstance(f, bytes) or len(f) != 32:
                raise VarsError("all Cell slots must be 32-byte hashes")
        if (self.h_supersedes != H_EMPTY or self.h_retires != H_EMPTY) and self.h_loss == H_EMPTY:
            raise VarsError("H_loss is mandatory when H_supersedes or H_retires is non-empty")
        header = b"VAR1\x00\x00\x00" + bytes([k])
        return header + b"".join(fields)

    @property
    def id(self) -> bytes:
        return sha256(self.encode())

    @staticmethod
    def decode(raw: bytes) -> "Cell":
        if len(raw) < 296 or raw[:4] != b"VAR1":
            raise VarsError("missing VAR1 magic or short cell")
        if raw[4:7] != b"\x00\x00\x00":
            raise VarsError("VAR1 reserved header bytes must be 0x000000")
        k = raw[7]
        if k > 64 or len(raw) != 296 + 32 * k:
            raise VarsError("invalid VAR1 arity or byte length")
        words = [raw[8 + 32 * i : 8 + 32 * (i + 1)] for i in range(9 + k)]
        cell = Cell(
            h_schema=words[0],
            h_slot_name=words[1],
            h_payload=words[2],
            h_relies=words[3],
            h_attests=words[4],
            h_supersedes=words[5],
            h_retires=words[6],
            h_invalidates=words[7],
            h_loss=words[8],
            slots=tuple(words[9:]),
        )
        if (cell.h_supersedes != H_EMPTY or cell.h_retires != H_EMPTY) and cell.h_loss == H_EMPTY:
            raise VarsError("eviction cell missing H_loss")
        return cell


# ---------------------------------------------------------------------------
# §1.3 Class 2: Detached SEAL (`164` bytes)
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Seal:
    h_target: bytes
    h_scope_ctx: bytes
    actor_pubkey: bytes
    signature: bytes

    def encode(self) -> bytes:
        if len(self.h_target) != 32 or len(self.h_scope_ctx) != 32 or len(self.actor_pubkey) != 32 or len(self.signature) != 64:
            raise VarsError("invalid Seal field lengths")
        return b"SEAL" + self.h_target + self.h_scope_ctx + self.actor_pubkey + self.signature

    @property
    def id(self) -> bytes:
        return sha256(self.encode())

    @staticmethod
    def sign(sk: bytes, h_target: bytes, h_scope_ctx: bytes) -> "Seal":
        pk = ed25519_pubkey(sk)
        msg = b"SEAL" + h_target + h_scope_ctx + pk
        sig = ed25519_sign(sk, msg)
        return Seal(h_target=h_target, h_scope_ctx=h_scope_ctx, actor_pubkey=pk, signature=sig)

    @staticmethod
    def decode(raw: bytes) -> "Seal":
        if len(raw) != 164 or raw[:4] != b"SEAL":
            raise VarsError("invalid SEAL length or magic")
        s = Seal(
            h_target=raw[4:36],
            h_scope_ctx=raw[36:68],
            actor_pubkey=raw[68:100],
            signature=raw[100:164],
        )
        if weak_public_key(s.actor_pubkey) or not ed25519_verify(s.actor_pubkey, raw[:100], s.signature):
            raise VarsError("invalid or weak-key Ed25519 signature on SEAL")
        return s


# ---------------------------------------------------------------------------
# §2 Standard Library Schemas
# ---------------------------------------------------------------------------
SCHEMA_SPECS: Dict[str, List[str]] = {
    "axiom": [],
    "contract": ["tier:utf8", "required_comp:root", "expected_outcome:hash", "evaluator_policy:pol1"],
    "computation": [],
    "checkpoint": ["computation_id:root", "credit_total:u64", "spent_total:u64", "peak_size:u64", "kernel_outcome:utf8", "actions:u64"],
    "cycle_witness": ["computation_id:root", "entry_spent:u64", "cycle_actions:u64", "cycle_cost:u64"],
    "decision": ["tier:utf8", "required_comp:root", "expected_outcome:hash", "evaluator_policy:pol1"],
    "question": ["expected_schema:cell", "evaluator_policy:pol1"],
    "acceptance": ["source_scope:utf8", "foreign_scope_cell:cell"],
    "scope": ["admission_policy:pol1", "acceptance_policy:pol1", "rules:wasm"],
    "verdict": ["ckpt_or_witness:cell", "verdict_code:utf8", "verifier_id:utf8"],
    "projection": ["tip:utf8", "rules:wasm", "input:digest", "state:digest", "witness_policy:pol1"],
}


def build_standard_schemas() -> Tuple[Dict[str, Cell], Dict[bytes, bytes]]:
    """Return ({name: schema_cell}, {atom_hash: atom_bytes}) for the 10 standard schemas."""
    atoms: Dict[bytes, bytes] = {}
    schemas: Dict[str, Cell] = {}
    for name, field_specs in SCHEMA_SPECS.items():
        slot_atom = atom_utf8(f"core/schema.{name}")
        h_slot = sha256(slot_atom)
        atoms[h_slot] = slot_atom
        slot_hashes: List[bytes] = []
        for fs in field_specs:
            fa = atom_utf8(fs)
            fh = sha256(fa)
            atoms[fh] = fa
            slot_hashes.append(fh)
        sc = Cell(h_schema=H_META_SCHEMA, h_slot_name=h_slot, h_payload=H_EMPTY, slots=tuple(slot_hashes))
        schemas[name] = sc
    return schemas, atoms


STD_SCHEMAS, STD_SCHEMA_ATOMS = build_standard_schemas()
H_SCHEMA = {name: sc.id for name, sc in STD_SCHEMAS.items()}
STD_SCHEMA_IDS: Set[bytes] = set(H_SCHEMA.values())
STD_SCHEMA_ATOMS[H_LENS_KERNEL] = KERNEL_ATOM  # every genesis stores the rules object

_SIGMA_IMPL_DIR = Path(__file__).resolve().parent.parent / "sigma-glyph" / "impl"
if str(_SIGMA_IMPL_DIR) not in sys.path:
    sys.path.insert(0, str(_SIGMA_IMPL_DIR))
import sigma_resume as SR  # noqa: E402


# ---------------------------------------------------------------------------
# Book I `term_hash` decoding & Deterministic Replay
# ---------------------------------------------------------------------------
def sgs1_term_hash(state_bytes: bytes) -> Tuple[bytes, bytes]:
    """Decode `SGS1` bytes -> (computation_id, book1_term_hash)."""
    if len(state_bytes) < 4 + 32 + 33 or state_bytes[:4] != b"SGS1":
        raise VarsError("not an SGS1 state")
    cid = state_bytes[4:36]
    i = 36
    frames: List[List[bytes]] = []
    op_map = {ord("L"): 0x00, ord("R"): 0x01, ord("D"): 0xFF}
    while True:
        if i >= len(state_bytes):
            raise VarsError("truncated SGS1 state")
        tag = state_bytes[i]
        if tag == ord("A"):
            frames.append([])
            i += 1
            continue
        if i + 33 > len(state_bytes):
            raise VarsError("truncated SGS1 leaf")
        payload = state_bytes[i + 1 : i + 33]
        i += 33
        if tag == ord("T"):
            th = payload
        elif tag in op_map:
            th = sha256(bytes([op_map[tag], 0x01]) + payload)
        else:
            raise VarsError(f"unknown SGS1 tag: {tag}")
        while frames:
            frames[-1].append(th)
            if len(frames[-1]) < 2:
                break
            left, right = frames.pop()
            th = sha256(bytes([0x02, 0x06]) + left + right)
        else:
            if i != len(state_bytes):
                raise VarsError("trailing bytes in SGS1 state")
            return cid, th


def _parent_checkpoint(
    c: Cell, atoms: Dict[bytes, bytes], cells: Optional[Dict[bytes, Cell]]
) -> Optional[Tuple[int, bytes, Cell]]:
    """The highest-spent `schema.checkpoint` of the same computation listed in `c.h_relies`, or None."""
    if cells is None or c.h_relies == H_EMPTY:
        return None
    parent_ckpts = [
        (u64_of(cells[pid].slots[2], atoms), pid, cells[pid])
        for pid in parse_hvec(atoms[c.h_relies], require_sorted=True)
        if pid in cells and cells[pid].h_schema == H_SCHEMA["checkpoint"] and cells[pid].slots[0] == c.slots[0]
    ]
    return max(parent_ckpts, key=lambda item: item[0]) if parent_ckpts else None


def verify_checkpoint_replay(
    c: Cell,
    atoms: Dict[bytes, bytes],
    cells: Optional[Dict[bytes, Cell]] = None,
    *,
    max_atp: Optional[int] = None,
    gate_mode: bool = False,
    memo: Optional[Dict[bytes, str]] = None,
) -> str:
    """Deterministically replay a `schema.checkpoint` cell.

    Each checkpoint is replayed incrementally from the highest-spent parent `schema.checkpoint` in its
    `h_relies` (if any), else from `ComputationRoot`. : a parent's state is a trusted starting point only
    if the parent is itself replay-verified, transitively back to `ComputationRoot`, so the whole lineage is
    verified oldest-first. When `gate_mode=True`, a transition exceeding `VERIFIER_LIMITS['max_atp']` is admitted
    on structure alone as `'NOT_ASSESSED'`, and so is every checkpoint whose lineage contains one. Outside gate
    mode a lineage that is not fully replay-verified raises. `memo` caches per-cell results within one caller.
    """
    lineage = [c]
    seen = {c.id}
    while True:
        parent = _parent_checkpoint(lineage[-1], atoms, cells)
        if parent is None:
            break
        if parent[1] in seen:
            raise VarsError("checkpoint lineage is cyclic")
        seen.add(parent[1])
        lineage.append(parent[2])

    memo = {} if memo is None else memo
    for i in range(len(lineage) - 1, -1, -1):
        cell = lineage[i]
        status = memo.get(cell.id)
        if status is None:
            try:
                status = _replay_from_parent(cell, atoms, cells, max_atp=max_atp, gate_mode=gate_mode)
            except VarsError as e:
                if i == 0:
                    raise
                raise VarsError(
                    f"parent checkpoint {cell.id.hex()[:12]} is not replay-verified, so its state cannot "
                    f"root the replay of {c.id.hex()[:12]}: {e}"
                ) from None
            memo[cell.id] = status
        if status != "REPLAYED":
            # Only gate mode returns a non-REPLAYED status; everything newer in the lineage inherits it.
            for newer in lineage[:i]:
                memo[newer.id] = status
            return status
    return "REPLAYED"


def _replay_from_parent(
    c: Cell,
    atoms: Dict[bytes, bytes],
    cells: Optional[Dict[bytes, Cell]],
    *,
    max_atp: Optional[int],
    gate_mode: bool,
) -> str:
    """Replay one checkpoint from its immediate parent's state (or from `ComputationRoot`).

    Trusts the parent's state: callers MUST go through `verify_checkpoint_replay`, which verifies the
    lineage first."""
    cid_bytes = c.slots[0]
    root_doc, env_doc = _load_root_and_env(cid_bytes, atoms)
    env = SR.Environment([bytes.fromhex(h) for h in env_doc["hashes"]], atoms)
    ctx_err = SR._context_error(root_doc, env)
    if ctx_err:
        raise VarsError(f"checkpoint context error: {ctx_err}")

    credit_total = u64_of(c.slots[1], atoms)
    spent_total = u64_of(c.slots[2], atoms)
    peak_size = u64_of(c.slots[3], atoms)
    outcome_h = c.slots[4]
    if credit_total < spent_total:
        raise VarsError("checkpoint credit_total < spent_total")

    # Incremental replay from the parent checkpoint in H_relies; the caller has verified it
    b_doc, b_id, b_state = SR.start(cid_bytes.hex(), bytes.fromhex(root_doc["input_term_hash"]))
    parent_spent = 0
    parent = _parent_checkpoint(c, atoms, cells)
    if parent is not None:
        parent_spent, p_id, p_cell = parent
        if spent_total < parent_spent:
            raise VarsError("checkpoint spent_total decreased relative to parent checkpoint")
        b_doc = {
            "schema": "sigma-resume.checkpoint@draft-1",
            "computation_id": cid_bytes.hex(),
            "parent_checkpoint_id": p_id.hex(),
            "state_id": p_cell.h_payload.hex(),
            "credit_total": parent_spent,
            "spent_total": parent_spent,
            "peak_semantic_size": u64_of(p_cell.slots[3], atoms),
            "kernel_outcome": "PAUSED",
            "transition_claim": {"actions": 0, "spent_delta": 0},
        }
        b_id = p_id.hex()
        b_state = atoms[p_cell.h_payload]

    delta_spent = spent_total - parent_spent
    eff_max_atp = max_atp if max_atp is not None else SR.G.VERIFIER_LIMITS.get("max_atp", 10_000_000)
    if delta_spent > eff_max_atp:
        if gate_mode:
            return "NOT_ASSESSED"
        raise VarsError("checkpoint delta_spent exceeds host verifier ceiling (NOT_ASSESSED)")

    runtime = root_doc["runtime_semantics_id"]
    try:
        replay = SR.advance(b_doc, b_id, b_state, env, delta_spent, SR.G.VERIFIER_LIMITS, runtime)
    except Exception as e:
        raise VarsError(f"checkpoint replay failed: {e}") from None
    if not replay.kernel:
        if gate_mode and replay.outcome in (SR.RESOURCE_FAULT, SR.ADMISSION_REFUSED, SR.INCOMPLETE):
            return "NOT_ASSESSED"
        raise VarsError(f"checkpoint replay stopped locally ({replay.outcome})")
    if (
        replay.state_bytes != atoms[c.h_payload]
        or replay.checkpoint["spent_total"] != spent_total
        or replay.checkpoint["peak_semantic_size"] != peak_size
    ):
        raise VarsError("forged checkpoint state_bytes, spent_total, or peak_size mismatch on replay")
    if replay.checkpoint["transition_claim"]["actions"] != u64_of(c.slots[5], atoms):
        raise VarsError("checkpoint actions differ from the replayed transition's action count")

    probe_doc = dict(replay.checkpoint, credit_total=spent_total)
    probe = SR.advance(
        probe_doc,
        c.h_payload.hex(),
        replay.state_bytes,
        env,
        credit_total - spent_total,
        SR.G.VERIFIER_LIMITS,
        runtime,
        max_actions=1,
    )
    if outcome_h == H_NORMAL_FORM:
        if not (probe.outcome == "NORMAL_FORM" and probe.checkpoint["transition_claim"]["actions"] == 0):
            raise VarsError("checkpoint claims H_NORMAL_FORM but probe is not terminal NORMAL_FORM")
    elif outcome_h == H_PAUSED:
        if probe.outcome != "PAUSED":
            raise VarsError("checkpoint claims H_PAUSED but probe outcome differs")
    elif outcome_h == H_BLOCKED_REF:
        if not (probe.outcome == "BLOCKED_REFERENCE" and probe.checkpoint["transition_claim"]["actions"] == 0):
            raise VarsError("checkpoint claims H_BLOCKED_REF but probe outcome differs")
    else:
        raise VarsError("unknown checkpoint kernel_outcome hash")
    return "REPLAYED"


def check_slot_type(h: bytes, typ: str, atoms: Dict[bytes, bytes], cells: Dict[bytes, "Cell"]) -> None:
    """a slot must hold a value of the type its schema field declares, not merely an existing hash."""
    def atom(prefix: bytes) -> bytes:
        raw = atoms.get(h)
        if raw is None or not raw.startswith(prefix):
            raise VarsError(f"slot type: {h.hex()[:12]} is not a {typ} atom")
        return raw
    if typ == "utf8":
        if h not in INTRINSIC_UTF8:
            validate_utf8_atom(atom(b"UTF8"))
    elif typ == "u64":
        if h != H_ZERO:
            parse_u64(atom(b"U64\x00"))
    elif typ == "pol1":
        thr, hvec_h = parse_pol1(atom(b"POL1"))
        if hvec_h not in atoms:
            raise VarsError("slot type: POL1 pubkey HVEC missing from cas/atoms/")
        pks = parse_hvec(atoms[hvec_h], require_sorted=True)
        for pk in pks:
            if weak_public_key(pk):
                raise VarsError("weak or non-canonical Ed25519 public key in POL1")
            try:
                _ed_dec(pk)
            except ValueError as e:
                raise VarsError(f"invalid Ed25519 curve point in POL1: {e}") from None
        if not 1 <= thr <= len(pks):
            raise VarsError("slot type: POL1 threshold outside 1..len(pubkeys)")
    elif typ == "root":
        _load_root_and_env(h, atoms)
    elif typ == "digest":
        pass  # a bare SHA-256 value; it names bytes that need not be stored (§2, projection)
    elif typ == "wasm":
        atom(b"\x00asm")
    elif typ == "cell":
        if h not in cells:
            raise VarsError(f"slot type: {h.hex()[:12]} is not a cell")
    elif typ == "hash":
        if h not in atoms and h not in cells and h not in INTRINSIC_HASHES:
            raise VarsError(f"slot type: {h.hex()[:12]} missing from CAS")


def _load_root_and_env(cid_bytes: bytes, atoms: Dict[bytes, bytes]) -> Tuple[dict, dict]:
    """The `ComputationRoot` and `Environment` documents behind `cid_bytes`, or a VarsError (never a JSON/Key error)."""
    def doc(h: bytes, schema: str, what: str) -> dict:
        raw = atoms.get(h)
        if raw is None:
            raise VarsError(f"{what} missing from cas/atoms/")
        try:
            d = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, ValueError):
            raise VarsError(f"{what} is not a canonical JSON atom") from None
        if not isinstance(d, dict) or d.get("schema") != schema:
            raise VarsError(f"invalid {what} schema")
        return d
    root_doc = doc(cid_bytes, "sigma-resume.root@draft-1", "ComputationRoot")
    env_hex = root_doc.get("environment_id")
    if not isinstance(env_hex, str) or len(env_hex) != 64:
        raise VarsError("ComputationRoot environment_id malformed")
    env_doc = doc(bytes.fromhex(env_hex), "sigma-resume.environment@draft-1", "Environment")
    return root_doc, env_doc


def verify_cycle_witness_replay(c: Cell, atoms: Dict[bytes, bytes], *, gate_mode: bool = False) -> str:
    """Deterministically verify a `schema.cycle_witness` cell via `sigma_resume.verify_cycle`."""
    cid_bytes = c.slots[0]
    root_doc, env_doc = _load_root_and_env(cid_bytes, atoms)
    env = SR.Environment([bytes.fromhex(h) for h in env_doc["hashes"]], atoms)
    witness_doc = {
        "schema": "sigma-resume.cycle@draft-1",
        "computation_id": cid_bytes.hex(),
        "entry_spent_total": u64_of(c.slots[1], atoms),
        "entry_state_id": c.h_payload.hex(),
        "cycle_action_count": u64_of(c.slots[2], atoms),
        "cycle_cost": u64_of(c.slots[3], atoms),
    }
    verdict = SR.verify_cycle((root_doc, cid_bytes.hex()), env, witness_doc)
    if verdict.startswith("NOT_ASSESSED") and gate_mode:
        return "NOT_ASSESSED"
    if verdict != "CYCLE_PROVEN":
        raise VarsError(f"cycle_witness replay failed: {verdict}")
    return "CYCLE_PROVEN"


KERNEL_BITS = ("accepted", "invalidated", "effective", "retired", "superseded", "active", "stale")
KERNEL_CODES = {
    -1: "malformed input", -2: "edge not in forward topological order", -3: "out of memory",
    -4: "Pass 2 not monotone", -5: "Pass 2 without fixed point",
    -10: "genesis scope shape", -11: "genesis scope lacks its admission quorum", -12: "local seal context",
    -13: "local seal key", -14: "cross-seal", -15: "unsealed local cell", -16: "evaluator policy not within roster",
    -17: "foreign cell without self-sealed scope", -18: "several new local scopes", -19: "new scope shape",
    -20: "new scope lacks admission quorum", -21: "acceptance not pinned to a self-sealed scope",
    -22: "binding does not reach a prior binding of its name", -23: "unknown policy",
    -6: "reference list differs from the rules' reading", -24: "last commit is not governed by these rules",
    -25: "rotation back to the v1 rules",
}


class KernelRefusal(VarsError):
    """The rules kernel returned a negative code: the fold refused the commit log (or its input was malformed)."""

    def __init__(self, code: int):
        self.code = code
        super().__init__(f"rules kernel E{code}: {KERNEL_CODES.get(code, 'unknown code')}")


class TwinDivergence(RuntimeError):
    """The rules kernel and the host's differential twin disagree: a defect in one of them, never a refusal."""


class KernelRunner:
    """Runs a rules module (`kernel/lens.wasm`, or `kernel2/lens2.wasm` for v2) under Node (WebAssembly, no other
    dependency): the rules object of §4.3."""

    def __init__(self, rules: bytes = H_LENS_KERNEL) -> None:
        self.rules = rules
        self.proc = subprocess.Popen(
            ["node", str(KERNEL_DIR / "run.mjs"), str(RULES_MODULES[rules])],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
        )

    def run(self, kernel_input: bytes) -> bytes:
        """The kernel's output bytes; raises KernelRefusal on a negative code."""
        self.proc.stdin.write(kernel_input.hex() + "\n")
        self.proc.stdin.flush()
        line = self.proc.stdout.readline().strip()
        if not line:
            raise RuntimeError("rules kernel produced no output")
        if line.startswith("E"):
            raise KernelRefusal(int(line[1:]))
        return bytes.fromhex(line)

    def statuses(self, lens: Dict[str, object]) -> Dict[bytes, Dict[str, bool]]:
        """Kernel statuses for a lens result, keyed by cell id, from a fresh run of its kernel input."""
        if lens.get("rules", H_LENS_KERNEL) != self.rules:
            raise RuntimeError("this lens was computed under other rules than this runner's")
        out = self.run(lens["kernel_input"])
        n = len(lens["kernel_order"])
        return {cid: {name: bool(out[4 + i] >> b & 1) for b, name in enumerate(KERNEL_BITS)}
                for i, cid in enumerate(lens["kernel_order"])}

    def close(self) -> None:
        self.proc.stdin.close()
        self.proc.wait(timeout=10)


_KERNELS: Dict[bytes, KernelRunner] = {}


def kernel_runner(rules: bytes = H_LENS_KERNEL) -> KernelRunner:
    if rules not in _KERNELS:
        _KERNELS[rules] = KernelRunner(rules)
    return _KERNELS[rules]


def schema_cell_mask(c: "Cell", atoms: Dict[bytes, bytes]) -> int:
    """A schema cell's `cell`-typed descriptors, bit s for slot s (rules v2, §4.3): host parsing of its UTF8 atoms."""
    mask = 0
    for s, d in enumerate(c.slots):
        raw = atoms.get(d)
        if raw is not None and raw[:4] == b"UTF8" and raw[4:].decode("utf-8", "replace").partition(":")[2] == "cell":
            mask |= 1 << s
    return mask


def commit_rules(scope: str, trees: List[Tuple[Dict[bytes, bytes], Dict[bytes, "Cell"], Dict[bytes, "Seal"]]]) -> List[bytes]:
    """The rules of each commit's epoch: those named by the scope governing it (fixed at its start, §0). Parsed:
    the genesis scope, then the newest local scope born in an earlier commit (§3 check 1 makes it the governing one;
    the kernel recomputes it). A commit log the gate would refuse may get any answer here; the kernel refuses it."""
    out: List[bytes] = []
    cur: Optional[Cell] = None
    seen: Set[bytes] = set()
    name = b"UTF8" + f"{scope}/SCOPE".encode()
    for i, (atoms, cells, _) in enumerate(trees):
        new = [c for cid, c in cells.items()
               if cid not in seen and c.h_schema == H_SCHEMA["scope"] and atoms.get(c.h_slot_name) == name]
        if i == 0 and len(new) == 1:
            cur = new[0]
        out.append(cur.slots[2] if cur is not None and len(cur.slots) == 3 else H_LENS_KERNEL)
        if i > 0 and len(new) == 1:
            cur = new[0]
        seen |= set(cells)
    return out


def cell_refs(c: "Cell", cells: Dict[bytes, "Cell"], atoms: Dict[bytes, bytes], v1: bool) -> List[Tuple[int, bytes]]:
    """The reference positions of a cell (0 payload, 1 + s slot s) and the cells they name. v1 reads every payload or
    slot equal to a cell id as a reference; v2 (RULES-V2.md) reads only the payload of a verdict or acceptance and
    the slots its schema declares `cell`."""
    vals = (c.h_payload, *c.slots)
    if v1:
        return [(p, x) for p, x in enumerate(vals) if x in cells]
    if c.h_schema == H_META_SCHEMA:
        return []
    sc = cells.get(c.h_schema)
    mask = schema_cell_mask(sc, atoms) if sc is not None else 0
    typed = [0] if c.h_schema in (H_SCHEMA["verdict"], H_SCHEMA["acceptance"]) else []
    typed += [1 + s for s in range(len(c.slots)) if mask >> s & 1 and c.slots[s] != H_EMPTY]
    return [(p, vals[p]) for p in typed if vals[p] in cells]


def chain_refs(scope: str, trees) -> Tuple[Dict[bytes, List[Tuple[int, bytes]]], Dict[bytes, int], List[bytes]]:
    """Every cell's references, each read by the rules of its birth epoch; with births and per-commit rules."""
    atoms, cells, _ = trees[-1]
    rules = commit_rules(scope, trees)
    birth: Dict[bytes, int] = {}
    for i, (_, cs, _) in enumerate(trees):
        for cid in cs:
            birth.setdefault(cid, i)
    refs = {cid: cell_refs(c, cells, atoms, rules[birth[cid]] == H_LENS_KERNEL) for cid, c in cells.items()}
    return refs, birth, rules


def topo_order(cells: Dict[bytes, "Cell"], atoms: Dict[bytes, bytes],
               value_refs: Optional[Dict[bytes, List[Tuple[int, bytes]]]] = None
               ) -> Tuple[List[bytes], Dict[bytes, Set[bytes]], Dict[bytes, Set[bytes]]]:
    """Forward topological order (oldest first) over every cell reference, with parents (older) and children (newer).
    `value_refs` are the payload and slot references the rules read (`chain_refs`); by default, v1's reading."""

    def hvec_items(h: bytes) -> List[bytes]:
        return [] if h == H_EMPTY else parse_hvec(atoms[h], require_sorted=True)

    parents_of: Dict[bytes, Set[bytes]] = {cid: set() for cid in cells}  # u -> older v
    children_of: Dict[bytes, Set[bytes]] = {cid: set() for cid in cells}  # older v -> newer u
    for u, c in cells.items():
        refs: Set[bytes] = set()
        for mh in (c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates):
            refs.update(hvec_items(mh))
        if value_refs is None:
            refs.update(x for x in (c.h_payload, *c.slots) if x in cells)
        else:
            refs.update(x for _, x in value_refs[u])
        for v in refs:
            if v in cells and v != u:
                parents_of[u].add(v)
                children_of[v].add(u)
    indeg = {u: len(parents_of[u]) for u in cells}
    queue = sorted(u for u, d in indeg.items() if d == 0)
    order: List[bytes] = []
    while queue:
        u = queue.pop(0)
        order.append(u)
        for ch in sorted(children_of[u]):
            indeg[ch] -= 1
            if indeg[ch] == 0:
                queue.append(ch)
    if len(order) != len(cells):
        raise VarsError("cell references are cyclic")
    return order, parents_of, children_of


def strong_pol1(raw: bytes, atoms: Dict[bytes, bytes]) -> Optional[Tuple[int, List[bytes]]]:
    """A POL1 atom's threshold and keys if it is well formed with strong, distinct-enough keys; else None."""
    try:
        thr, hvec_h = parse_pol1(raw)
        pks = parse_hvec(atoms[hvec_h], require_sorted=True)
        for pk in pks:
            if weak_public_key(pk):
                return None
            _ed_dec(pk)
    except (VarsError, KeyError, ValueError):
        return None
    return (thr, pks) if len(set(pks)) >= thr else None


def chain_rules(scope: str, trees) -> bytes:
    """The rules that evaluate a commit log: those of its last commit's epoch (RULES-V2.md §4)."""
    return commit_rules(scope, trees)[-1]


def kernel_facts(scope: str, trees: List[Tuple[Dict[bytes, bytes], Dict[bytes, "Cell"], Dict[bytes, "Seal"]]]) -> Tuple[bytes, List[bytes]]:
    """Encode a commit log as the input of the rules that evaluate it (§4.3): parsed cells, verified seals, POL1
    rosters; for v2, schema masks and every cell's reference positions too.

    Only parsing happens here: the order of cells, interned origins and keys, and edge lists as cell indices."""
    atoms, cells, seals = trees[-1]
    value_refs, birth_c, rules = chain_refs(scope, trees)
    v2 = rules[-1] != H_LENS_KERNEL
    birth_s: Dict[bytes, int] = {}
    for i, (_, cs, ss) in enumerate(trees):
        for sid in ss:
            birth_s.setdefault(sid, i)
    order, _, _ = topo_order(cells, atoms, value_refs if v2 else None)
    pos = {cid: i for i, cid in enumerate(order)}

    def origin(c: "Cell") -> str:
        return parse_utf8(atoms[c.h_slot_name]).split("/", 1)[0]

    origins = sorted({origin(c) for c in cells.values()} - {scope})
    origin_ix = {scope: 0, **{o: i + 1 for i, o in enumerate(origins)}}
    pols = {}
    for h, raw in atoms.items():
        if raw[:4] == b"POL1":
            got = strong_pol1(raw, atoms)
            if got is not None:
                pols[h] = got
    keys = sorted({pk for _, pks in pols.values() for pk in pks} | {s.actor_pubkey for s in seals.values()})
    key_ix = {k: i for i, k in enumerate(keys)}

    out = bytearray(struct.pack("<I", KERNEL2_MAGIC) if v2 else b"")
    out += struct.pack("<4I", len(trees), len(order), len(keys), len(pols))
    for h in sorted(pols):
        thr, pks = pols[h]
        out += h + struct.pack(f"<{2 + len(pks)}I", thr, len(pks), *(key_ix[k] for k in pks))
    for cid in order:
        c = cells[cid]
        out += cid + c.h_schema + c.h_payload + c.h_slot_name + c.h_loss
        out += struct.pack("<3I", origin_ix[origin(c)], birth_c[cid], len(c.slots)) + b"".join(c.slots)
        if v2:
            mask = schema_cell_mask(c, atoms) if c.h_schema == H_META_SCHEMA else 0
            out += struct.pack("<2I", mask & 0xFFFFFFFF, mask >> 32)
        for mh in (c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates):
            items = [] if mh == H_EMPTY else parse_hvec(atoms[mh], require_sorted=True)
            out += struct.pack(f"<{1 + len(items)}I", len(items), *(pos[v] for v in items))
        if v2:
            rs = value_refs[cid]
            out += struct.pack(f"<{1 + 2 * len(rs)}I", len(rs), *(w for p, x in rs for w in (p, pos[x])))
    out += struct.pack("<I", len(seals))
    for sid in sorted(seals):
        sl = seals[sid]
        out += struct.pack("<4I", pos[sl.h_target], pos[sl.h_scope_ctx], key_ix[sl.actor_pubkey], birth_s[sid])
    return bytes(out), order


# ---------------------------------------------------------------------------
# §3 Git Plumbing Store & Mandatory 5-Check Admission Gate
# ---------------------------------------------------------------------------
class GitVarsRepo:
    def __init__(self, repo_dir: Path | str):
        self.repo_dir = Path(repo_dir)
        self._blob_by_oid: Dict[str, bytes] = {}
        self._oid_by_raw: Dict[bytes, str] = {}

    def _git(self, *args: str, input_bytes: Optional[bytes] = None) -> bytes:
        res = subprocess.run(
            ["git", "-C", str(self.repo_dir), *args],
            input=input_bytes,
            capture_output=True,
            check=False,
        )
        if res.returncode != 0:
            raise VarsError(f"git {' '.join(args)} failed: {res.stderr.decode('utf-8', 'replace').strip()}")
        return res.stdout

    def ref_commit(self, scope: str) -> Optional[str]:
        res = subprocess.run(
            ["git", "-C", str(self.repo_dir), "rev-parse", "--verify", "-q", f"refs/vars/heads/{scope}"],
            capture_output=True,
            text=True,
            check=False,
        )
        return res.stdout.strip() if res.returncode == 0 else None

    def commit_chain(self, tip_commit: str) -> List[str]:
        out = self._git("rev-list", "--reverse", tip_commit).decode().splitlines()
        return [c.strip() for c in out if c.strip()]

    def read_cas_tree(self, commit_oid: str) -> Tuple[Dict[bytes, bytes], Dict[bytes, Cell], Dict[bytes, Seal]]:
        atoms: Dict[bytes, bytes] = {}
        cells: Dict[bytes, Cell] = {}
        seals: Dict[bytes, Seal] = {}
        ls = self._git("ls-tree", "-r", commit_oid).decode().splitlines()
        for line in ls:
            if not line.strip():
                continue
            meta, path = line.split("\t", 1)
            mode, _obj_type, oid = meta.split()
            if mode != "100644":
                raise VarsError(f"non-100644 mode {mode} at {path}")
            m = re.match(r"^cas/(atoms|cells|seals)/([0-9a-f]{2})/([0-9a-f]{62})$", path)
            if not m:
                raise VarsError(f"invalid cas path: {path}")
            kind_dir, aa, bb = m.groups()
            expected_h = bytes.fromhex(aa + bb)
            raw = self._blob_by_oid.get(oid)
            if raw is None:
                raw = self._git("cat-file", "blob", oid)
                self._blob_by_oid[oid] = raw
                self._oid_by_raw[raw] = oid
            if sha256(raw) != expected_h:
                raise VarsError(f"CAS SHA-256 mismatch at {path}")
            if kind_dir == "atoms":
                validate_atom(raw)
                atoms[expected_h] = raw
            elif kind_dir == "cells":
                cells[expected_h] = Cell.decode(raw)
            elif kind_dir == "seals":
                seals[expected_h] = Seal.decode(raw)
        return atoms, cells, seals

    def build_candidate_commit(
        self,
        scope: str,
        atoms: Dict[bytes, bytes],
        cells: Sequence[Cell],
        seals: Sequence[Seal],
        parent_commit: Optional[str] = None,
        extra_tree_entries: Optional[List[Tuple[str, str, str, bytes]]] = None,
    ) -> str:
        """Write blobs into Git and build a candidate commit (without updating the ref yet)."""
        base_atoms, base_cells, base_seals = ({}, {}, {})
        if parent_commit:
            base_atoms, base_cells, base_seals = self.read_cas_tree(parent_commit)

        all_atoms = dict(base_atoms)
        all_atoms.update(atoms)
        all_cells = {cid: c.encode() for cid, c in base_cells.items()}
        for c in cells:
            all_cells[c.id] = c.encode()
        all_seals = {sid: s.encode() for sid, s in base_seals.items()}
        for s in seals:
            all_seals[s.id] = s.encode()

        index_lines: List[str] = []

        def stage_entry(mode: str, path: str, data: bytes) -> None:
            oid = self._oid_by_raw.get(data)
            if oid is None:
                oid = self._git("hash-object", "-w", "--stdin", input_bytes=data).decode().strip()
                self._oid_by_raw[data] = oid
                self._blob_by_oid[oid] = data
            index_lines.append(f"{mode} blob {oid}\t{path}")

        for h, raw in sorted(all_atoms.items()):
            hx = h.hex()
            stage_entry("100644", f"cas/atoms/{hx[:2]}/{hx[2:]}", raw)
        for h, raw in sorted(all_cells.items()):
            hx = h.hex()
            stage_entry("100644", f"cas/cells/{hx[:2]}/{hx[2:]}", raw)
        for h, raw in sorted(all_seals.items()):
            hx = h.hex()
            stage_entry("100644", f"cas/seals/{hx[:2]}/{hx[2:]}", raw)
        for mode, _kind, path, data in extra_tree_entries or []:
            stage_entry(mode, path, data)

        # A private index per call: concurrent builders never share or delete each other's staging
        idx_dir = tempfile.mkdtemp(prefix="vars-idx-")
        env = {**subprocess.os.environ, "GIT_INDEX_FILE": str(Path(idx_dir) / "index")}
        try:
            res_idx = subprocess.run(
                ["git", "-C", str(self.repo_dir), "update-index", "--index-info"],
                input=("\n".join(index_lines) + "\n").encode("utf-8"),
                env=env,
                capture_output=True,
                check=False,
            )
            if res_idx.returncode != 0:
                raise VarsError(res_idx.stderr.decode())
            res_tree = subprocess.run(
                ["git", "-C", str(self.repo_dir), "write-tree"],
                env=env,
                capture_output=True,
                check=True,
            )
        finally:
            shutil.rmtree(idx_dir, ignore_errors=True)
        tree_oid = res_tree.stdout.decode().strip()
        cmd = ["commit-tree", tree_oid, "-m", f"vars({scope}): transition"]
        if parent_commit:
            cmd.extend(["-p", parent_commit])
        return self._git(*cmd).decode().strip()

    def admit_and_advance(self, scope: str, candidate_commit: str, expected_old: Optional[str]) -> None:
        """Run the §3.2 5-Check Admission Gate, then atomically advance `refs/vars/heads/<scope>`.

        Every refusal is a VarsError: an unexpected exception from malformed input is a refusal too,
        never a crash, and nothing is written before all checks pass."""
        try:
            self._admit_and_advance(scope, candidate_commit, expected_old)
        except VarsError:
            raise
        except (KeyError, IndexError, TypeError, ValueError, UnicodeDecodeError) as e:
            raise VarsError(f"malformed commit refused ({type(e).__name__}: {e})") from None

    def _admit_and_advance(self, scope: str, candidate_commit: str, expected_old: Optional[str]) -> None:
        actual_old = self.ref_commit(scope)
        if actual_old != expected_old:
            raise VarsError(f"CAS ref mismatch: expected {expected_old}, actual {actual_old}")

        # Check #1: Single-parent linear chain (or Genesis)
        cat_commit = self._git("cat-file", "commit", candidate_commit).decode()
        header = cat_commit.split("\n\n", 1)[0]  # the message may contain any line
        parents = [line.split()[1] for line in header.splitlines() if line.startswith("parent ")]
        if expected_old is None:
            if parents:
                raise VarsError("Check #1 failed: Genesis commit must have 0 parents")
        else:
            if parents != [expected_old]:
                raise VarsError(f"Check #1 failed: expected single parent {[expected_old]}, got {parents}")

        # Check #2: Strict append-only tree (`--no-renames --diff-filter=a` empty + mode 100644)
        if expected_old is not None:
            diff_out = self._git("diff-tree", "-r", "--no-renames", "--diff-filter=a", expected_old, candidate_commit)
            if diff_out.strip():
                raise VarsError(f"Check #2 failed: non-A tree changes:\n{diff_out.decode()}")

        # Check #3 & #4 & #5: Read and validate full CAS tree, references, replay, and authority fold
        atoms, cells, seals = self.read_cas_tree(candidate_commit)
        known = set(atoms.keys()) | set(cells.keys()) | INTRINSIC_HASHES

        def req_atom(h: bytes, desc: str) -> bytes:
            return atom_of(h, atoms, f"Check #4 failed: atom for {desc}")

        def origin_of(c: Cell) -> str:
            return parse_utf8(req_atom(c.h_slot_name, "H_slot_name")).split("/", 1)[0]

        def req_hvec_cells(src_cid: bytes, src_c: Cell, h: bytes, mname: str) -> List[bytes]:
            if h == H_EMPTY:
                return []
            items = parse_hvec(req_atom(h, mname), require_sorted=True)
            for item in items:
                if item not in cells:
                    raise VarsError(f"{mname} references non-Cell {item.hex()[:12]}")
                if item == src_cid:
                    raise VarsError(f"self-loop on {src_cid.hex()[:12]} in {mname}")
                target_c = cells[item]
                if mname == "supersedes" and target_c.h_schema != src_c.h_schema:
                    raise VarsError("cross-schema supersedes is forbidden")
                if mname == "attests" and target_c.h_schema not in (
                    H_SCHEMA["contract"],
                    H_SCHEMA["decision"],
                    H_SCHEMA["question"],
                ):
                    raise VarsError("attests target must be contract, decision, or question")
                if target_c.h_schema == H_SCHEMA["projection"]:
                    raise VarsError("a projection is an immutable historical fact: no edge may name it")
                if target_c.h_schema == H_SCHEMA["scope"] and not (
                    mname == "supersedes" and src_c.h_schema == H_SCHEMA["scope"]
                ):
                    raise VarsError("scope cell can only be superseded by another scope cell")
                if target_c.h_schema == H_SCHEMA["scope"] and origin_of(src_c) != origin_of(target_c):
                    raise VarsError("a scope cell can only be superseded by a scope cell of the same origin")
            return items

        # Validate every cell's references, edge types & deterministic replay (Check #3 & #4)
        replay_memo: Dict[bytes, str] = {}
        for cid, c in cells.items():
            slot_str = parse_utf8(req_atom(c.h_slot_name, "H_slot_name"))
            validate_slot_name(slot_str)
            if slot_str.startswith("core/schema.") and cid not in STD_SCHEMA_IDS:
                raise VarsError(f"slot name {slot_str!r} is reserved for intrinsic standard schemas")
            # Lean stage-1 finding: `<origin>/SCOPE` is reserved both ways, so a scope rotation can never take the
            # name of another binding (Rule 6 exempts scope cells) and no other cell can take a scope's name.
            is_scope_name = slot_str == f"{slot_str.split('/', 1)[0]}/SCOPE"
            if (c.h_schema == H_SCHEMA["scope"]) != is_scope_name:
                raise VarsError(f"reserved scope name: {slot_str!r} must be <origin>/SCOPE iff the cell is a schema.scope")
            if c.h_schema == H_SCHEMA["scope"] and len(c.slots) == 3 and c.slots[2] not in RULES_MODULES:
                raise VarsError("scope names rules this host does not implement (slots[2] not v1 or v2)")
            if c.h_schema == H_META_SCHEMA:
                if c.h_payload != H_EMPTY or any(
                    m != H_EMPTY for m in (c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates, c.h_loss)
                ):
                    raise VarsError("schema definition cell must have H_EMPTY payload and morphisms")
                for s_h in c.slots:
                    raw = req_atom(s_h, "schema slot descriptor")
                    validate_utf8_atom(raw)
                    fname, sep, ftype = parse_utf8(raw).partition(":")
                    if not fname or not sep or ftype not in FIELD_TYPES:
                        raise VarsError(f"schema field descriptor {parse_utf8(raw)!r} is not name:type of a known type")
                continue

            if c.h_schema not in cells or cells[c.h_schema].h_schema != H_META_SCHEMA:
                raise VarsError(f"Check #4 failed: H_schema {c.h_schema.hex()[:12]} is not a valid schema cell")
            if len(cells[c.h_schema].slots) != len(c.slots):
                raise VarsError("Check #3 failed: cell arity does not match schema arity")
            if c.h_payload not in known:
                raise VarsError("Check #4 failed: H_payload missing from CAS")
            if c.h_schema == H_SCHEMA["projection"] and any(
                m != H_EMPTY for m in (c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates, c.h_loss)
            ):
                raise VarsError("a projection has no edges and no loss")
            if c.h_schema in (H_SCHEMA["acceptance"], H_SCHEMA["verdict"]) and c.h_payload not in cells:
                raise VarsError("Check #4 failed: ACCEPTANCE/VERDICT H_payload must be in cas/cells/")

            relies_ids = req_hvec_cells(cid, c, c.h_relies, "relies")
            req_hvec_cells(cid, c, c.h_attests, "attests")
            req_hvec_cells(cid, c, c.h_supersedes, "supersedes")
            req_hvec_cells(cid, c, c.h_retires, "retires")
            req_hvec_cells(cid, c, c.h_invalidates, "invalidates")

            if c.h_loss != H_EMPTY:
                loss_raw = req_atom(c.h_loss, "H_loss")
                validate_utf8_atom(loss_raw)
                if not (1 <= len(loss_raw) - 4 <= MAX_LOSS_BYTES):
                    raise VarsError("H_loss exceeds 4096 bytes")

            digest_slots = {
                i for i, d in enumerate(cells[c.h_schema].slots)
                if d in atoms and parse_utf8(atoms[d]).endswith(":digest")
            }
            for i, s_h in enumerate(c.slots):
                if i not in digest_slots and s_h not in known:
                    raise VarsError(f"Check #4 failed: slot {s_h.hex()[:12]} missing from CAS")
            # every slot must have the type its schema field declares ("name:type")
            for s_h, desc_h in zip(c.slots, cells[c.h_schema].slots):
                fname, _, ftype = parse_utf8(req_atom(desc_h, "schema field descriptor")).partition(":")
                if s_h == H_EMPTY and fname in OPTIONAL_FIELDS:
                    continue
                check_slot_type(s_h, ftype, atoms, cells)

            # Payloads and enumerations by kind (§2 "Payloads and meaning")
            if c.h_schema in (H_SCHEMA["axiom"], H_SCHEMA["contract"], H_SCHEMA["decision"], H_SCHEMA["question"],
                              H_SCHEMA["scope"]) and c.h_payload not in INTRINSIC_UTF8:
                check_slot_type(c.h_payload, "utf8", atoms, cells)
            if c.h_schema == H_SCHEMA["computation"]:
                _load_root_and_env(c.h_payload, atoms)
            if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]) and c.slots[0] not in (H_PROVISIONAL, H_OWNER):
                raise VarsError("tier must be H_PROVISIONAL or H_OWNER")
            if c.h_schema == H_SCHEMA["projection"] and c.h_payload != H_EMPTY:
                raise VarsError("a projection's payload is H_EMPTY")
            if c.h_schema == H_SCHEMA["verdict"]:
                if c.slots[1] not in VERDICT_CODES:
                    raise VarsError("verdict_code is not one of REPLAYED, ATTESTED, INVALID, NOT_ASSESSED")
                if c.slots[1] == H_ATTESTED and c.slots[0] != H_EMPTY:
                    raise VarsError("an ATTESTED verdict has an empty ckpt_or_witness")


            # Kind-specific structural & deterministic replay invariants
            if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
                if c.slots[1] != H_EMPTY:
                    if not any(
                        cells[r].h_schema == H_SCHEMA["computation"] and cells[r].h_payload == c.slots[1]
                        for r in relies_ids
                    ):
                        raise VarsError(
                            "contract/decision with non-empty required_comp must rely on a matching computation cell"
                        )
            elif c.h_schema == H_SCHEMA["checkpoint"]:
                sgs1 = req_atom(c.h_payload, "checkpoint SGS1")
                if sgs1[:4] != b"SGS1" or sgs1[4:36] != c.slots[0]:
                    raise VarsError("Check #4 failed: SGS1 computation_id != CHECKPOINT.slots[0]")
                if c.h_supersedes != H_EMPTY:
                    raise VarsError("CHECKPOINT must chain via H_relies, never H_supersedes")
                verify_checkpoint_replay(c, atoms, cells, gate_mode=True, memo=replay_memo)
            elif c.h_schema == H_SCHEMA["cycle_witness"]:
                actions = parse_u64(req_atom(c.slots[2], "cycle_actions"))
                cost = parse_u64(req_atom(c.slots[3], "cycle_cost"))
                if actions < 1 or cost < actions:
                    raise VarsError("CYCLE_WITNESS requires actions >= 1 and cost >= actions")
                verify_cycle_witness_replay(c, atoms, gate_mode=True)
            elif c.h_schema == H_SCHEMA["verdict"]:
                if c.slots[0] == H_EMPTY and c.slots[1] == H_REPLAYED:
                    raise VarsError("VERDICT with H_EMPTY checkpoint must use H_ATTESTED, not H_REPLAYED")
                if c.slots[0] != H_EMPTY and c.slots[0] not in relies_ids:
                    raise VarsError("VERDICT with non-empty ckpt_or_witness must include it in H_relies")
                if c.slots[0] != H_EMPTY and cells[c.slots[0]].h_schema not in (H_SCHEMA["checkpoint"],
                                                                                H_SCHEMA["cycle_witness"]):
                    raise VarsError("a verdict's ckpt_or_witness is a checkpoint or cycle witness")
                if c.slots[1] != H_VERDICT_INVALID and cells[c.h_payload].h_schema not in (
                        H_SCHEMA["contract"], H_SCHEMA["decision"], H_SCHEMA["question"]):
                    raise VarsError("only an INVALID verdict may judge a cell other than a contract, decision or question")
            elif c.h_schema == H_SCHEMA["acceptance"]:
                target_origin = parse_utf8(req_atom(cells[c.h_payload].h_slot_name, "target slot")).split("/", 1)[0]
                src_scope = parse_utf8(req_atom(c.slots[0], "source_scope"))
                if src_scope != target_origin or src_scope == scope:
                    raise VarsError("ACCEPTANCE source_scope does not match foreign target cell origin")
                sf_id = c.slots[1]
                if sf_id not in cells or cells[sf_id].h_schema != H_SCHEMA["scope"]:
                    raise VarsError("ACCEPTANCE slots[1] must reference a foreign schema.scope cell")
                sf_origin = parse_utf8(req_atom(cells[sf_id].h_slot_name, "foreign scope slot")).split("/", 1)[0]
                if sf_origin != src_scope:
                    raise VarsError("ACCEPTANCE foreign_scope_cell origin mismatch")

        for sid, s in seals.items():
            if s.h_target not in cells or s.h_scope_ctx not in cells:
                raise VarsError("Check #4 failed: Seal target or scope_ctx missing from cas/cells/")

        prior_chain = self.commit_chain(expected_old) if expected_old is not None else []
        prior_trees = [self.read_cas_tree(x) for x in prior_chain]
        prior_cells = prior_trees[-1][1] if prior_trees else {}
        prior = set(prior_cells)
        # References never point forward in time (§4.3): v1 rules read any payload or slot equal to a cell id as a
        # reference, so a new cell may not have an id that an older cell born in a v1 epoch names there. Cells born
        # under v2 rules read references by type (RULES-V2.md): their opaque values veto nothing.
        prior_rules = commit_rules(scope, prior_trees) if prior_trees else []
        born: Dict[bytes, int] = {}
        for i, (_, cs, _) in enumerate(prior_trees):
            for x in cs:
                born.setdefault(x, i)
        named_before = {x for pid, pc in prior_cells.items() if prior_rules[born[pid]] == H_LENS_KERNEL
                        for x in (pc.h_payload, *pc.slots)}
        for cid in set(cells) - prior:
            if cid in named_before:
                raise VarsError(f"an older cell names {cid.hex()[:12]} in a payload or slot: a reference to a later-born cell")

        # Projections: the gate recomputes the rules at the named tip and refuses any digest that differs
        chain = set(prior_chain)
        for cid, c in cells.items():
            if c.h_schema != H_SCHEMA["projection"] or cid in prior:
                continue
            tip = parse_utf8(req_atom(c.slots[0], "projection tip"))
            if tip not in chain:
                raise VarsError(f"projection tip {tip[:12]} is not a commit of refs/vars/heads/{scope} before this one")
            tip_trees = prior_trees[:prior_chain.index(tip) + 1]
            if c.slots[1] != chain_rules(scope, tip_trees):
                raise VarsError("projection names other rules than those of its tip's epoch")
            h_in, h_state = self.projection_digests(scope, tip)
            if (c.slots[2], c.slots[3]) != (h_in, h_state):
                raise VarsError("projection digests differ from the gate's recomputation of the rules at its tip")

        # Run the commit-chain fold to verify admission authority on the new commit
        self._evaluate_commit_chain(scope, self.commit_chain(candidate_commit))

        # Atomic compare-and-swap update-ref
        cmd = ["update-ref", f"refs/vars/heads/{scope}", candidate_commit]
        if expected_old is not None:
            cmd.append(expected_old)
        else:
            cmd.append("0" * 40)
        self._git(*cmd)

    # -----------------------------------------------------------------------
    # §4 Commit-Chain Fold & Three-Pass Lensing
    # -----------------------------------------------------------------------
    def projection_digests(self, scope: str, tip: str) -> Tuple[bytes, bytes]:
        """`(sha256(kernel input), sha256(kernel output))` for the scope's chain up to and including `tip`: the
        `input` and `state` a projection at `tip` must carry. Anyone holding the chain can recompute them."""
        trees = [self.read_cas_tree(c) for c in self.commit_chain(tip)]
        kernel_input, _ = kernel_facts(scope, trees)
        return sha256(kernel_input), sha256(kernel_runner(chain_rules(scope, trees)).run(kernel_input))

    def _evaluate_commit_chain(self, scope: str, commits: List[str]) -> Dict[str, object]:
        """§4.1 fold. The rules kernel decides authority; `_fold_twin` recomputes it in Python and must agree."""
        trees = [self.read_cas_tree(c) for c in commits]
        try:
            twin, twin_err = self._fold_twin(scope, trees), None
        except VarsError as e:
            twin, twin_err = None, e
        kernel_input, order = kernel_facts(scope, trees)
        value_refs, _, rules = chain_refs(scope, trees)
        try:
            out = kernel_runner(rules[-1]).run(kernel_input)
        except KernelRefusal as e:
            if twin_err is None:
                raise TwinDivergence(f"{e}, but the host fold admits the commit log") from None
            raise VarsError(f"{twin_err} [{e}]") from None
        if twin_err is not None:
            raise TwinDivergence(f"host fold refused ({twin_err}) but the rules kernel admits the commit log")
        cells: Dict[bytes, Cell] = twin["cells"]
        atoms: Dict[bytes, bytes] = twin["atoms"]
        n = len(order)
        status, auth, flags = out[4:4 + n], out[4 + n:4 + 2 * n], iter(out[4 + 2 * n:])
        kernel = {
            "active_scope_id": order[int.from_bytes(out[:4], "little")],
            "latched_scope_auth": {cid for i, cid in enumerate(order) if auth[i] and cells[cid].h_schema == H_SCHEMA["scope"]},
            "latched_acc_auth": {cid for i, cid in enumerate(order) if auth[i] and cells[cid].h_schema == H_SCHEMA["acceptance"]},
            "latched_schema_auth": {cid for i, cid in enumerate(order) if auth[i] and cells[cid].h_schema == H_META_SCHEMA},
            "latched_edge_auth": set(),
        }
        for wid in order:
            w = cells[wid]
            for kind, mh in (("invalidates", w.h_invalidates), ("retires", w.h_retires), ("supersedes", w.h_supersedes)):
                for vid in [] if mh == H_EMPTY else parse_hvec(atoms[mh], require_sorted=True):
                    if next(flags):
                        kernel["latched_edge_auth"].add((wid, vid, kind))
        for k, v in kernel.items():
            if twin[k] != v:
                raise TwinDivergence(f"rules kernel and host fold disagree on {k}")
        return {
            **twin,
            **kernel,
            "kernel_input": kernel_input,
            "kernel_order": order,
            "rules": rules[-1],
            "value_refs": value_refs,
            "kernel_status": {cid: {name: bool(status[i] >> b & 1) for b, name in enumerate(KERNEL_BITS)}
                              for i, cid in enumerate(order)},
        }

    def _fold_twin(self, scope: str, trees: List[Tuple[Dict[bytes, bytes], Dict[bytes, Cell], Dict[bytes, Seal]]]) -> Dict[str, object]:
        """The host's differential twin of the kernel fold (§4.1), plus the endorser sets Pass 3 needs."""
        latched_scope_auth: Set[bytes] = set()
        latched_acc_auth: Set[bytes] = set()
        latched_schema_auth: Set[bytes] = set(STD_SCHEMA_IDS)
        latched_edge_auth: Set[Tuple[bytes, bytes, str]] = set()
        initial_endorsers: Dict[bytes, Set[bytes]] = {}
        cumulative_endorsers: Dict[bytes, Set[bytes]] = {}
        foreign_endorsers_by_scope: Dict[Tuple[bytes, bytes], Set[bytes]] = {}
        self_sealed_foreign_scopes: Set[bytes] = set()
        seen_cells: Set[bytes] = set()
        seen_seals: Set[bytes] = set()
        active_scope_id: Optional[bytes] = None

        for idx, (atoms, cells, seals) in enumerate(trees):

            def pol_quorum(pol_hash: bytes) -> Tuple[int, Set[bytes]]:
                thr, hvec_h = parse_pol1(atoms[pol_hash])
                pks_list = parse_hvec(atoms[hvec_h], require_sorted=True)
                for pk in pks_list:
                    if weak_public_key(pk):
                        raise VarsError("weak or non-canonical Ed25519 public key in POL1")
                    try:
                        _ed_dec(pk)
                    except ValueError as e:
                        raise VarsError(f"invalid Ed25519 curve point in POL1: {e}") from None
                pks = set(pks_list)
                if len(pks) < thr:
                    raise VarsError("POL1 threshold exceeds pubkey count")
                return thr, pks

            def cell_origin(c: Cell) -> str:
                return parse_utf8(atoms[c.h_slot_name]).split("/", 1)[0]

            def hvec_items(h: bytes) -> List[bytes]:
                return [] if h == H_EMPTY else parse_hvec(atoms[h], require_sorted=True)

            new_cids = set(cells.keys()) - seen_cells
            new_sids = set(seals.keys()) - seen_seals

            if idx == 0:
                local_scopes = [
                    cid for cid in new_cids if cells[cid].h_schema == H_SCHEMA["scope"] and cell_origin(cells[cid]) == scope
                ]
                if len(local_scopes) != 1:
                    raise VarsError("Genesis commit must contain exactly one local schema.scope cell")
                active_scope_id = local_scopes[0]
                s0 = cells[active_scope_id]
                if (
                    s0.h_supersedes != H_EMPTY
                    or s0.h_retires != H_EMPTY
                    or s0.h_invalidates != H_EMPTY
                    or s0.h_loss != H_EMPTY
                ):
                    raise VarsError("Genesis scope cell must have empty eviction slots")
                thr0, pks0 = pol_quorum(s0.slots[0])
                pol_quorum(s0.slots[1])
                s0_signers = {
                    seals[sid].actor_pubkey
                    for sid in new_sids
                    if seals[sid].h_target == active_scope_id
                    and seals[sid].h_scope_ctx == active_scope_id
                    and seals[sid].actor_pubkey in pks0
                }
                if len(s0_signers) < thr0:
                    raise VarsError("Genesis scope cell lacks admission quorum seals")
                latched_scope_auth.add(active_scope_id)

            assert active_scope_id is not None
            # Keep s_base_id fixed for the entire commit evaluation
            s_base_id = active_scope_id
            s_base = cells[s_base_id]
            adm_thr, adm_pks = pol_quorum(s_base.slots[0])
            acc_thr, acc_pks = pol_quorum(s_base.slots[1])

            # Self-sealed foreign scopes present in cas/cells/
            valid_foreign_scopes: Dict[str, List[Tuple[bytes, Set[bytes]]]] = {}
            for scid, sc in cells.items():
                if sc.h_schema == H_SCHEMA["scope"] and cell_origin(sc) != scope:
                    f_origin = cell_origin(sc)
                    f_thr, f_pks = pol_quorum(sc.slots[0])
                    pol_quorum(sc.slots[1])
                    f_signers = {
                        seals[sid].actor_pubkey
                        for sid in seals
                        if seals[sid].h_target == scid
                        and seals[sid].h_scope_ctx == scid
                        and seals[sid].actor_pubkey in f_pks
                    }
                    if len(f_signers) >= f_thr:
                        self_sealed_foreign_scopes.add(scid)
                        valid_foreign_scopes.setdefault(f_origin, []).append((scid, f_pks))

            # foreign endorsements accumulate the same way. Recount every foreign cell against each
            # self-sealed scope of its origin, so a foreign co-signature added later is not ignored.
            for fcid, fc in cells.items():
                if fcid in STD_SCHEMA_IDS or cell_origin(fc) == scope:
                    continue
                for sf_id, sf_pks in valid_foreign_scopes.get(cell_origin(fc), []):
                    foreign_endorsers_by_scope[(fcid, sf_id)] = {
                        seals[sid].actor_pubkey
                        for sid in seals
                        if seals[sid].h_target == fcid
                        and seals[sid].h_scope_ctx == sf_id
                        and seals[sid].actor_pubkey in sf_pks
                    }

            # Check #3: Every new local seal must bind to s_base_id and be signed by a roster member
            for sid in new_sids:
                s = seals[sid]
                target_c = cells[s.h_target]
                ctx_c = cells[s.h_scope_ctx]
                local_ctx = ctx_c.h_schema == H_SCHEMA["scope"] and cell_origin(ctx_c) == scope
                if cell_origin(target_c) != scope and local_ctx:
                    # Cross-seal: a local roster member endorses a foreign cell (its only route to local edge authority)
                    if s.h_scope_ctx != s_base_id or s.actor_pubkey not in adm_pks:
                        raise VarsError("Cross-seal on a foreign cell must use the active SCOPE and a roster key")
                if cell_origin(target_c) == scope:
                    if s.h_scope_ctx != s_base_id:
                        raise VarsError("Local seal H_scope_ctx does not match active SCOPE")
                    allowed = adm_pks | (acc_pks if target_c.h_schema == H_SCHEMA["acceptance"] else set())
                    if target_c.h_schema == H_SCHEMA["projection"]:
                        allowed = allowed | pol_quorum(target_c.slots[4])[1]  # its witnesses, roster or not (§4.4)
                    if s.actor_pubkey not in allowed:
                        raise VarsError("Local seal signer not in active SCOPE policy")
                    # an admitted local seal is an endorsement for good. It was checked against the scope
                    # active at its own commit, so a late co-signature counts exactly like a birth signature.
                    cumulative_endorsers.setdefault(s.h_target, set()).add(s.actor_pubkey)

            # Check #3: every new non-standard cell must carry valid seals
            for cid in new_cids:
                if cid in STD_SCHEMA_IDS:
                    continue
                c = cells[cid]
                c_orig = cell_origin(c)
                if c_orig == scope:
                    # writing a cell, and InitialEndorsers, count roster keys only (a projection's outside witnesses
                    # sign it, they do not write it)
                    roster = adm_pks | (acc_pks if c.h_schema == H_SCHEMA["acceptance"] else set())
                    c_signers = {
                        seals[sid].actor_pubkey
                        for sid in seals
                        if seals[sid].h_target == cid and seals[sid].h_scope_ctx == s_base_id
                        and seals[sid].actor_pubkey in roster
                    }
                    if not c_signers:
                        raise VarsError(f"New local cell {cid.hex()[:12]} lacks a valid Seal under active SCOPE")
                    initial_endorsers[cid] = set(c_signers)
                    # Check POL1 subset rule
                    pol_slot = None
                    if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
                        pol_slot = c.slots[3]
                    elif c.h_schema == H_SCHEMA["question"]:
                        pol_slot = c.slots[1]
                    if pol_slot and pol_slot != H_EMPTY:
                        _, custom_pks = pol_quorum(pol_slot)
                        if not custom_pks.issubset(adm_pks):
                            raise VarsError("local cell evaluator policy pubkeys not a subset of scope roster")

                else:
                    # A foreign cell must belong to a self-sealed foreign scope in cas/cells/
                    f_scopes = valid_foreign_scopes.get(c_orig, [])
                    if not f_scopes:
                        raise VarsError(f"foreign cell {cid.hex()[:12]} from {c_orig!r} lacks self-sealed foreign SCOPE")
                    f_ends_union: Set[bytes] = set()
                    for sf_id, sf_pks in f_scopes:
                        sf_ends = {
                            seals[sid].actor_pubkey
                            for sid in seals
                            if seals[sid].h_target == cid
                            and seals[sid].h_scope_ctx == sf_id
                            and seals[sid].actor_pubkey in sf_pks
                        }
                        f_ends_union |= sf_ends
                    initial_endorsers[cid] = f_ends_union

            # Strictly epoch-scoped endorsers under s_base_id
            def endorsers_under_base(cid: bytes, allowed_pks: Set[bytes]) -> Set[bytes]:
                return {
                    seals[sid].actor_pubkey
                    for sid in seals
                    if seals[sid].h_target == cid
                    and seals[sid].h_scope_ctx == s_base_id
                    and seals[sid].actor_pubkey in allowed_pks
                }

            # At most one new local schema.scope cell in any transition commit
            pending_next_scope: Optional[bytes] = None
            if idx >= 1:
                new_local_scopes = [
                    cid for cid in new_cids if cells[cid].h_schema == H_SCHEMA["scope"] and cell_origin(cells[cid]) == scope
                ]
                if len(new_local_scopes) > 1:
                    raise VarsError("multiple local schema.scope cells introduced in a single commit")
                if len(new_local_scopes) == 1:
                    s_next_id = new_local_scopes[0]
                    s_next = cells[s_next_id]
                    pol_quorum(s_next.slots[0])
                    pol_quorum(s_next.slots[1])
                    if (
                        hvec_items(s_next.h_supersedes) != [s_base_id]
                        or s_next.h_retires != H_EMPTY
                        or s_next.h_invalidates != H_EMPTY
                    ):
                        raise VarsError("new schema.scope cell must supersede active SCOPE only")
                    if len(endorsers_under_base(s_next_id, adm_pks)) < adm_thr:
                        raise VarsError("new schema.scope cell lacks admission quorum under active SCOPE")
                    if s_base.slots[2] != H_LENS_KERNEL and s_next.slots[2] == H_LENS_KERNEL:
                        raise VarsError("a rotation may not go back from v2 rules to v1 (RULES-V2.md §4)")
                    pending_next_scope = s_next_id

            # Latch ACCEPTANCE (pinned to a self-sealed foreign scope per §2.5) and custom META_SCHEMA cells
            for cid, c in cells.items():
                if cell_origin(c) != scope:
                    continue
                if c.h_schema == H_SCHEMA["acceptance"] and cid not in latched_acc_auth:
                    if c.slots[1] not in self_sealed_foreign_scopes:
                        raise VarsError("ACCEPTANCE foreign_scope_cell is not self-sealed")
                    if len(endorsers_under_base(cid, acc_pks)) >= acc_thr:
                        latched_acc_auth.add(cid)
                elif c.h_schema == H_META_SCHEMA and cid not in latched_schema_auth:
                    if len(endorsers_under_base(cid, adm_pks)) >= adm_thr:
                        latched_schema_auth.add(cid)

            # Latch eviction / invalidation edges under s_base
            for wid, w in cells.items():
                if w.h_schema == H_META_SCHEMA:
                    continue
                w_ends_adm = endorsers_under_base(wid, adm_pks)
                w_ends_acc = endorsers_under_base(wid, acc_pks)
                for edge_kind, mh in (
                    ("invalidates", w.h_invalidates),
                    ("retires", w.h_retires),
                    ("supersedes", w.h_supersedes),
                ):
                    for vid in hvec_items(mh):
                        if (wid, vid, edge_kind) in latched_edge_auth:
                            continue
                        v = cells[vid]
                        # Total Governing Policy Function Pol_i(v) & AuthorCanEvict(v)
                        if v.h_schema == H_SCHEMA["scope"] or (
                            v.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]) and v.slots[0] == H_OWNER
                        ):
                            p_thr, p_pks, w_ends = adm_thr, adm_pks, w_ends_adm
                            author_can = False
                        elif v.h_schema == H_SCHEMA["acceptance"]:
                            p_thr, p_pks, w_ends = acc_thr, acc_pks, w_ends_acc
                            author_can = False
                        elif v.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]) and v.slots[0] == H_PROVISIONAL:
                            p_thr, p_pks = pol_quorum(v.slots[3]) if v.slots[3] != H_EMPTY else (adm_thr, adm_pks)
                            w_ends = w_ends_adm
                            author_can = True
                        elif v.h_schema == H_SCHEMA["question"]:
                            p_thr, p_pks = pol_quorum(v.slots[1]) if v.slots[1] != H_EMPTY else (adm_thr, adm_pks)
                            w_ends = w_ends_adm
                            author_can = True
                        else:
                            p_thr, p_pks, w_ends = adm_thr, adm_pks, w_ends_adm
                            author_can = True

                        quorum_ok = len(w_ends & p_pks) >= p_thr
                        author_ok = (
                            edge_kind in ("supersedes", "retires")
                            and author_can
                            and cell_origin(v) == scope  # foreign birth signers are not local authors
                            and bool(w_ends & initial_endorsers.get(vid, set()))
                        )
                        if quorum_ok or author_ok:
                            latched_edge_auth.add((wid, vid, edge_kind))

            # unique binding per H_slot_name, checked after this commit's authorization latch.
            # Every new local cell c (except a scope cell, which has its own single-lineage rule) must reach every
            # other local cell bound to the same name through supersedes edges: c's own first hop may still await
            # co-signatures (c stays inactive until all its supersedes edges latch), every later hop must already be
            # latched. Latches never unlatch and Superseded is transitive in Pass 1, so at most one binding is Active.
            latched_sup: Dict[bytes, Set[bytes]] = {}
            for e_w, e_v, e_kind in latched_edge_auth:
                if e_kind == "supersedes":
                    latched_sup.setdefault(e_w, set()).add(e_v)
            any_sup: Dict[bytes, Set[bytes]] = {oid: set(hvec_items(oc.h_supersedes)) for oid, oc in cells.items()}

            def sup_reach(src: bytes, adj: Dict[bytes, Set[bytes]]) -> Set[bytes]:
                out: Set[bytes] = set()
                todo = list(adj.get(src, ()))
                while todo:
                    nxt = todo.pop()
                    if nxt not in out:
                        out.add(nxt)
                        todo.extend(adj.get(nxt, ()))
                return out

            bound_by_name: Dict[bytes, List[bytes]] = {}
            for oid, oc in cells.items():
                if oid not in STD_SCHEMA_IDS and cell_origin(oc) == scope:
                    bound_by_name.setdefault(oc.h_slot_name, []).append(oid)
            for cid in sorted(new_cids):
                c = cells[cid]
                if cid in STD_SCHEMA_IDS or cell_origin(c) != scope or c.h_schema == H_SCHEMA["scope"]:
                    continue
                peers = [oid for oid in bound_by_name.get(c.h_slot_name, []) if oid != cid]
                if not peers:
                    continue
                def binding_reach(src: bytes) -> Set[bytes]:
                    first = set(hvec_items(cells[src].h_supersedes))
                    out = set(first)
                    for hop in first:
                        out |= sup_reach(hop, latched_sup)
                    return out

                reach_c = binding_reach(cid)
                for oid in peers:
                    if oid in reach_c:
                        continue
                    if oid in new_cids and cid in binding_reach(oid):
                        continue  # same-commit pair: the other cell is the newer binding
                    slot = parse_utf8(atoms[c.h_slot_name])
                    linked = oid in sup_reach(cid, any_sup) or any(
                        oid in hvec_items(m) for m in (c.h_retires, c.h_invalidates)
                    )
                    if linked:
                        raise VarsError(
                            f"binding of slot {slot!r} does not reach the prior binding "
                            f"{oid.hex()[:12]} through authorized supersedes edges"
                        )
                    raise VarsError(f"duplicate unlinked binding for slot {slot!r}")

            # End-of-commit scope transition
            if pending_next_scope is not None:
                latched_scope_auth.add(pending_next_scope)
                active_scope_id = pending_next_scope

            seen_cells |= new_cids
            seen_seals |= new_sids

        return {
            "atoms": atoms,
            "cells": cells,
            "seals": seals,
            "active_scope_id": active_scope_id,
            "latched_scope_auth": latched_scope_auth,
            "latched_acc_auth": latched_acc_auth,
            "latched_schema_auth": latched_schema_auth,
            "latched_edge_auth": latched_edge_auth,
            "initial_endorsers": initial_endorsers,
            "cumulative_endorsers": cumulative_endorsers,
            "foreign_endorsers_by_scope": foreign_endorsers_by_scope,
        }

    def lens(self, scope: str) -> Dict[str, object]:
        tip = self.ref_commit(scope)
        if tip is None:
            raise VarsError(f"no ref refs/vars/heads/{scope}")
        fold = self._evaluate_commit_chain(scope, self.commit_chain(tip))
        atoms: Dict[bytes, bytes] = fold["atoms"]
        cells: Dict[bytes, Cell] = fold["cells"]
        latched_scope_auth: Set[bytes] = fold["latched_scope_auth"]
        latched_acc_auth: Set[bytes] = fold["latched_acc_auth"]
        latched_schema_auth: Set[bytes] = fold["latched_schema_auth"]
        latched_edge_auth: Set[Tuple[bytes, bytes, str]] = fold["latched_edge_auth"]
        cumulative_endorsers: Dict[bytes, Set[bytes]] = fold["cumulative_endorsers"]
        foreign_endorsers_by_scope: Dict[Tuple[bytes, bytes], Set[bytes]] = fold["foreign_endorsers_by_scope"]
        active_scope_id: bytes = fold["active_scope_id"]
        s_active = cells[active_scope_id]

        def hvec_items(h: bytes) -> List[bytes]:
            return [] if h == H_EMPTY else parse_hvec(atoms[h], require_sorted=True)

        def cell_origin(c: Cell) -> str:
            return parse_utf8(atoms[c.h_slot_name]).split("/", 1)[0]

        forward_order, parents_of, children_of = topo_order(
            cells, atoms, fold["value_refs"] if fold["rules"] != H_LENS_KERNEL else None)
        reverse_order = list(reversed(forward_order))

        # Pass 1 (Reverse-Topological: newest/sinks -> oldest/sources)
        accepted: Dict[bytes, bool] = {}
        accepted_scopes: Dict[bytes, Set[bytes]] = {cid: set() for cid in cells}
        invalidated: Dict[bytes, bool] = {}
        effective: Dict[bytes, bool] = {}
        retired: Dict[bytes, bool] = {}
        superseded: Dict[bytes, bool] = {}
        active: Dict[bytes, bool] = {}

        for cid in reverse_order:
            c = cells[cid]
            c_orig = cell_origin(c)
            if cid in STD_SCHEMA_IDS or c_orig == scope:
                accepted[cid] = True
            else:
                direct_scopes = {
                    cells[ch].slots[1]
                    for ch in children_of[cid]
                    if ch in active and active[ch]
                    and cells[ch].h_schema == H_SCHEMA["acceptance"]
                    and ch in latched_acc_auth
                    and cells[ch].h_payload == cid
                }
                # Hereditary acceptance bounded to the same foreign origin scope
                hereditary_scopes: Set[bytes] = set()
                for ch in children_of[cid]:
                    if ch in accepted and accepted[ch] and cell_origin(cells[ch]) == c_orig:
                        hereditary_scopes |= accepted_scopes[ch]
                accepted_scopes[cid] = direct_scopes | hereditary_scopes
                accepted[cid] = bool(accepted_scopes[cid])

            inv = any(
                w in effective and effective[w] and accepted.get(w, False)
                and cid in hvec_items(cells[w].h_invalidates)
                and (w, cid, "invalidates") in latched_edge_auth
                and (cells[w].h_schema != H_SCHEMA["verdict"] or cells[w].slots[1] == H_VERDICT_INVALID)
                for w in children_of[cid]
            )
            invalidated[cid] = inv
            effective[cid] = not inv

            ret = any(
                w in effective and effective[w] and accepted.get(w, False)
                and cid in hvec_items(cells[w].h_retires)
                and (w, cid, "retires") in latched_edge_auth
                for w in children_of[cid]
            )
            # supersession is transitive along authorized supersedes edges. v is Superseded if some
            # Effective and Accepted cell reaches it, even when an intermediate replacement was invalidated.
            sup = any(
                cid in hvec_items(cells[w].h_supersedes)
                and (w, cid, "supersedes") in latched_edge_auth
                and ((effective.get(w, False) and accepted.get(w, False)) or superseded.get(w, False))
                for w in children_of[cid]
            )
            # A replacement cell with non-empty `supersedes` is only Active once all its supersedes edges are authorized
            sup_edges_authorized = all(
                (cid, vid, "supersedes") in latched_edge_auth for vid in hvec_items(c.h_supersedes)
            )
            retired[cid] = ret
            superseded[cid] = sup
            active[cid] = effective[cid] and not ret and not sup and accepted[cid] and sup_edges_authorized

        # Pass 2 (Forward-Topological LFP: oldest/sources -> newest/sinks, fixing ,  & )
        # iterate to the least fixed point, never a fixed number of rounds. The round operator is monotone:
        # dependency staleness grows with `stale`, and LiveAcceptedScopes only shrinks as `stale` grows, so from
        # all-False every round only flips False -> True. At most |cells| rounds change something; one more confirms.
        stale: Dict[bytes, bool] = {cid: False for cid in cells}
        live_accepted_scopes: Dict[bytes, Set[bytes]] = {cid: set() for cid in cells}
        for _round in range(len(cells) + 1):
            live_accepted_scopes = {cid: set() for cid in cells}
            for cid in reverse_order:
                c = cells[cid]
                c_orig = cell_origin(c)
                if cid in STD_SCHEMA_IDS or c_orig == scope:
                    continue
                direct_live = {
                    cells[ch].slots[1]
                    for ch in children_of[cid]
                    if active.get(ch, False)
                    and not stale.get(ch, False)
                    and cells[ch].h_schema == H_SCHEMA["acceptance"]
                    and ch in latched_acc_auth
                    and cells[ch].h_payload == cid
                }
                hereditary_live: Set[bytes] = set()
                for ch in children_of[cid]:
                    if live_accepted_scopes.get(ch) and cell_origin(cells[ch]) == c_orig:
                        hereditary_live |= live_accepted_scopes[ch]
                live_accepted_scopes[cid] = direct_live | hereditary_live

            changed = False
            for cid in forward_order:
                if not active[cid]:
                    new_st = False
                else:
                    deps = hvec_items(cells[cid].h_relies)
                    dep_st = any(not active.get(d, False) or stale.get(d, False) for d in deps)
                    foreign_st = (
                        cid not in STD_SCHEMA_IDS
                        and cell_origin(cells[cid]) != scope
                        and not bool(live_accepted_scopes.get(cid))
                    )
                    new_st = dep_st or foreign_st
                if new_st != stale[cid]:
                    if stale[cid]:
                        raise VarsError("Pass 2 is not monotone (a cell went from Stale back to non-Stale)")
                    stale[cid] = new_st
                    changed = True
            if not changed:
                break
        else:
            raise VarsError("Pass 2 did not reach its fixed point within |cells| + 1 rounds")

        # The rules kernel computed Passes 1-2; the Python passes above are its differential twin.
        kst: Dict[bytes, Dict[str, bool]] = fold["kernel_status"]
        twin_st = {"accepted": accepted, "invalidated": invalidated, "effective": effective, "retired": retired,
                   "superseded": superseded, "active": active, "stale": stale}
        if fold["kernel_order"] != forward_order:
            raise TwinDivergence("rules kernel and host lens order cells differently")
        for cid in forward_order:
            for name in KERNEL_BITS:
                if kst[cid][name] != twin_st[name][cid]:
                    raise TwinDivergence(f"rules kernel and host lens disagree on {name} of {cid.hex()[:12]}")
        accepted, invalidated, effective, retired, superseded, active, stale = (
            {cid: kst[cid][name] for cid in forward_order} for name in KERNEL_BITS)

        # Pass 3 (Constructive Maximal Witness Set W_max -> Settled vs Provisional)
        def pol_quorum(pol_hash: bytes) -> Tuple[int, Set[bytes]]:
            thr, hvec_h = parse_pol1(atoms[pol_hash])
            return thr, set(parse_hvec(atoms[hvec_h], require_sorted=True))

        adm_thr, adm_pks = pol_quorum(s_active.slots[0])
        lens_replay_memo: Dict[bytes, str] = {}
        settled: Dict[bytes, bool] = {}
        provisional: Dict[bytes, bool] = {}

        def witness_endorsers(wid: bytes) -> Set[bytes]:
            w_cell = cells[wid]
            if cell_origin(w_cell) == scope:
                return cumulative_endorsers.get(wid, set())  # late co-signatures count
            out_ends: Set[bytes] = set()
            for sf_id in live_accepted_scopes.get(wid, set()):
                out_ends |= foreign_endorsers_by_scope.get((wid, sf_id), set())
            return out_ends

        for cid in forward_order:
            c = cells[cid]
            if not active[cid] or stale[cid]:
                settled[cid] = False
                provisional[cid] = False
                continue
            if c.h_schema == H_META_SCHEMA:
                is_auth = cid in latched_schema_auth
                settled[cid] = is_auth
                provisional[cid] = not is_auth
                continue
            if c.h_schema == H_SCHEMA["scope"]:
                is_auth = cid in latched_scope_auth
                settled[cid] = is_auth
                provisional[cid] = not is_auth
                continue
            if c.h_schema == H_SCHEMA["axiom"]:
                settled[cid] = True
                provisional[cid] = False
                continue
            if c.h_schema == H_SCHEMA["projection"]:
                # Settled once its witness policy has signed it (late co-signatures count)
                w_thr, w_pks = pol_quorum(c.slots[4])
                is_set = len(witness_endorsers(cid) & w_pks) >= w_thr
                settled[cid] = is_set
                provisional[cid] = not is_set
                continue

            # Determine evaluation policy `EvalPol(v)`
            if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
                p_thr, p_pks = pol_quorum(c.slots[3]) if c.slots[3] != H_EMPTY else (adm_thr, adm_pks)
            elif c.h_schema == H_SCHEMA["question"]:
                p_thr, p_pks = pol_quorum(c.slots[1]) if c.slots[1] != H_EMPTY else (adm_thr, adm_pks)
            else:
                settled[cid] = True
                provisional[cid] = False
                continue

            valid_endorsers: Set[bytes] = set()
            for wid in children_of[cid]:
                w = cells[wid]
                if not active.get(wid, False) or stale.get(wid, False):
                    continue
                if cid not in hvec_items(w.h_attests):
                    continue
                if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
                    if w.h_schema != H_SCHEMA["verdict"] or w.h_payload != cid:
                        continue
                    # Contradictory active INVALID verdict under the same verifier_id blocks settlement
                    has_conflict = any(
                        active.get(bad_id, False)
                        and not stale.get(bad_id, False)
                        and bad_c.h_schema == H_SCHEMA["verdict"]
                        and bad_c.slots[1] == H_VERDICT_INVALID
                        and bad_c.slots[2] == w.slots[2]
                        and (
                            bad_c.h_payload == cid
                            or (w.slots[0] != H_EMPTY and bad_c.slots[0] == w.slots[0])
                        )
                        and bool(witness_endorsers(bad_id) & p_pks)
                        for bad_id, bad_c in cells.items()
                    )
                    if has_conflict:
                        continue
                    req_comp, exp_out = c.slots[1], c.slots[2]
                    if req_comp == H_EMPTY:
                        if w.slots[0] != H_EMPTY or w.slots[1] != H_ATTESTED:
                            continue
                    else:
                        if w.slots[1] != H_REPLAYED or w.slots[0] not in cells:
                            continue
                        cw_id = w.slots[0]
                        cw = cells[cw_id]
                        if not active.get(cw_id, False) or stale.get(cw_id, False):
                            continue
                        if cw.h_schema == H_SCHEMA["checkpoint"]:
                            if cw.slots[0] != req_comp or cw.slots[4] != H_NORMAL_FORM:
                                continue
                            try:
                                if verify_checkpoint_replay(cw, atoms, cells, gate_mode=False, memo=lens_replay_memo) != "REPLAYED":
                                    continue
                            except VarsError:
                                continue
                            _, th = sgs1_term_hash(atoms[cw.h_payload])
                            if th != exp_out:
                                continue
                        elif cw.h_schema == H_SCHEMA["cycle_witness"]:
                            if cw.slots[0] != req_comp or exp_out != H_CYCLE_PROVEN:
                                continue
                            try:
                                if verify_cycle_witness_replay(cw, atoms, gate_mode=False) != "CYCLE_PROVEN":
                                    continue
                            except VarsError:
                                continue
                        else:
                            continue
                elif c.h_schema == H_SCHEMA["question"]:
                    if w.h_schema != c.slots[0]:
                        continue
                valid_endorsers |= (witness_endorsers(wid) & p_pks)

            is_set = len(valid_endorsers) >= p_thr
            settled[cid] = is_set
            provisional[cid] = not is_set

        return {
            "kernel_input": fold["kernel_input"],
            "kernel_order": forward_order,
            "rules": fold["rules"],
            "cells": cells,
            "atoms": atoms,
            "accepted": accepted,
            "invalidated": invalidated,
            "effective": effective,
            "retired": retired,
            "superseded": superseded,
            "active": active,
            "stale": stale,
            "settled": settled,
            "provisional": provisional,
        }


# ---------------------------------------------------------------------------
# §4.4 Projection bundles: what a client without the repository holds and checks
# ---------------------------------------------------------------------------
BUNDLE_FORMAT = "vars-1.projection-bundle@1"


def parse_kernel_input(kernel_input: bytes) -> Dict[str, object]:
    """A kernel input (§4.3) as data: POL1 rosters as key indices, cells in order with their slots and edges as cell
    indices, and seals as (target, context, key index, commit). Key bytes are not in the input, only their order."""
    def u32(off: int) -> int:
        if off + 4 > len(kernel_input):
            raise VarsError("kernel input truncated")
        return struct.unpack_from("<I", kernel_input, off)[0]

    def take(off: int, n: int) -> bytes:
        if off + n > len(kernel_input):
            raise VarsError("kernel input truncated")
        return kernel_input[off:off + n]

    v2 = len(kernel_input) >= 4 and u32(0) == KERNEL2_MAGIC  # rules v2 inputs begin with "VAR2" (RULES-V2.md)
    base = 4 if v2 else 0
    n, p = u32(base + 4), u32(base + 12)
    off = base + 16
    pols: Dict[bytes, Tuple[int, List[int]]] = {}
    for _ in range(p):
        k = u32(off + 36)
        pols[take(off, 32)] = (u32(off + 32), [u32(off + 40 + 4 * j) for j in range(k)])
        off += 40 + 4 * k
    cells = []
    for _ in range(n):
        cid, schema, payload = take(off, 32), take(off + 32, 32), take(off + 64, 32)
        off += 160
        origin, k = u32(off), u32(off + 8)
        off += 12
        slots = [take(off + 32 * j, 32) for j in range(k)]
        off += 32 * k
        if v2:
            off += 8  # the schema mask; the kernel checks the reference list against it
        edges = []
        for _ in range(5):
            m = u32(off)
            edges.append([u32(off + 4 + 4 * j) for j in range(m)])
            off += 4 + 4 * m
        refs: Optional[List[int]] = None
        if v2:
            m = u32(off)
            refs = [u32(off + 8 + 8 * j) for j in range(m)]
            off += 4 + 8 * m
        cells.append({"id": cid, "schema": schema, "payload": payload, "origin": origin, "slots": slots,
                      "relies": edges[0], "attests": edges[1], "edges": edges, "refs": refs})
    seals = []
    for j in range(u32(off)):
        seals.append(tuple(u32(off + 4 + 16 * j + 4 * i) for i in range(4)))
    if off + 4 + 16 * len(seals) != len(kernel_input):
        raise VarsError("kernel input has trailing bytes")
    pos = {c["id"]: i for i, c in enumerate(cells)}
    for c in cells:
        if c["refs"] is None:  # v1: every payload or slot equal to a cell id
            c["refs"] = [pos[x] for x in (c["payload"], *c["slots"]) if x in pos]
    return {"pols": pols, "cells": cells, "seals": seals, "rules": H_LENS_KERNEL_V2 if v2 else H_LENS_KERNEL}


def pass3_at_tip(ki: Dict[str, object], output: bytes, di: int,
                 blocked_after: Optional[Set[bytes]] = None) -> Tuple[bool, Set[int], int, bytes]:
    """§4.2 Pass 3 for the contract or decision at index `di` (without `required_comp`), from a parsed kernel input
    and the kernel's output alone: whether it is Settled, the key indices that endorse it, the threshold, and the
    policy hash. Endorsers are counted as the lens counts them: every admitted seal on a local verdict; on a
    foreign verdict, seals under a scope of its origin that a live acceptance (of it or of a newer cell of its
    origin that references it) names, by that scope's admission keys. A contradicting INVALID verdict of the same
    verifier, endorsed by a policy key, blocks; `blocked_after` adds the verifier ids that such INVALID verdicts
    recorded after the tip block."""
    kc, pols, seals = ki["cells"], ki["pols"], ki["seals"]
    n = len(kc)
    if len(output) < 4 + 2 * n:
        raise VarsError("kernel output is shorter than its cell count")
    bit = lambda i, name: bool(output[4 + i] >> KERNEL_BITS.index(name) & 1)
    live = [bit(i, "active") and not bit(i, "stale") for i in range(n)]
    auth = [bool(output[4 + n + i]) for i in range(n)]
    pos = {c["id"]: i for i, c in enumerate(kc)}
    children: List[Set[int]] = [set() for _ in range(n)]
    for u, c in enumerate(kc):
        refs = {v for e in c["edges"] for v in e} | set(c["refs"])
        for v in refs - {u}:
            children[v].add(u)
    # live accepted scopes of foreign cells, newest first (children are newer)
    lacs: List[Set[int]] = [set() for _ in range(n)]
    for u in reversed(range(n)):
        if kc[u]["origin"] == 0 or kc[u]["schema"] == H_META_SCHEMA:
            continue
        for ch in children[u]:
            c = kc[ch]
            if live[ch] and c["schema"] == H_SCHEMA["acceptance"] and auth[ch] and c["payload"] == kc[u]["id"] \
                    and len(c["slots"]) > 1 and c["slots"][1] in pos:
                lacs[u].add(pos[c["slots"][1]])
            if lacs[ch] and kc[ch]["origin"] == kc[u]["origin"]:
                lacs[u] |= lacs[ch]
    signed: Dict[Tuple[int, int], Set[int]] = {}
    on: Dict[int, Set[int]] = {}
    for t, ctx, k, _ in seals:
        signed.setdefault((t, ctx), set()).add(k)
        on.setdefault(t, set()).add(k)

    def adm(sf: int) -> Optional[Tuple[int, List[int]]]:
        c = kc[sf]
        return pols.get(c["slots"][0]) if c["schema"] == H_SCHEMA["scope"] and c["slots"] else None

    def endorsers(w: int) -> Set[int]:
        if kc[w]["origin"] == 0:
            return on.get(w, set())
        out: Set[int] = set()
        for sf in lacs[w]:
            pol = adm(sf)  # the gate admits only acceptances that pin a self-sealed scope, and seals stay
            if pol is None or kc[sf]["origin"] != kc[w]["origin"]:
                continue
            out |= signed.get((w, sf), set()) & set(pol[1])
        return out

    d = kc[di]
    scope_cell = kc[struct.unpack_from("<I", output, 0)[0]]
    p = d["slots"][3] if d["slots"][3] != H_EMPTY else scope_cell["slots"][0]
    if p not in pols:
        raise VarsError("the kernel input lacks the evaluator policy")
    thr, pk = pols[p][0], set(pols[p][1])
    did = d["id"]
    bad = [b for b in range(n) if live[b] and kc[b]["schema"] == H_SCHEMA["verdict"]
           and kc[b]["slots"][1] == H_VERDICT_INVALID and kc[b]["payload"] == did and endorsers(b) & pk]
    blocked = {kc[b]["slots"][2] for b in bad} | (blocked_after or set())
    end: Set[int] = set()
    for w in children[di]:
        c = kc[w]
        if not live[w] or di not in c["attests"] or c["schema"] != H_SCHEMA["verdict"] or c["payload"] != did:
            continue
        if c["slots"][2] in blocked or c["slots"][0] != H_EMPTY or c["slots"][1] != H_ATTESTED:
            continue
        end |= endorsers(w) & pk
    return live[di] and len(end) >= thr, end, thr, p


def kernel_input_order(kernel_input: bytes) -> List[bytes]:
    """The cell ids of a kernel input (§4.3), in its order; the kernel's output indexes cells by this order."""
    return [c["id"] for c in parse_kernel_input(kernel_input)["cells"]]


def export_projection(repo: "GitVarsRepo", scope: str, projection_id: bytes, with_data: bool = True) -> Dict[str, object]:
    """A self-contained bundle for `projection_id` at the scope's tip: the cell, the atoms its check needs, every
    seal on it, and (with `with_data`) the kernel's input and output at its tip, which its digests commit to."""
    atoms, cells, seals = repo.read_cas_tree(repo.ref_commit(scope))
    cell = cells.get(projection_id)
    if cell is None or cell.h_schema != H_SCHEMA["projection"]:
        raise VarsError("not a projection cell of this scope")
    pol = atoms[cell.slots[4]]
    need = [cell.slots[0], cell.slots[4], parse_pol1(pol)[1]]
    bundle: Dict[str, object] = {
        "format": BUNDLE_FORMAT,
        "cell": cell.encode().hex(),
        "atoms": [atoms[h].hex() for h in need],
        "seals": sorted(s.encode().hex() for s in seals.values() if s.h_target == projection_id),
    }
    if with_data:
        tip = parse_utf8(atoms[cell.slots[0]])
        trees = [repo.read_cas_tree(c) for c in repo.commit_chain(tip)]
        kernel_input, _ = kernel_facts(scope, trees)
        bundle["input"] = kernel_input.hex()
        bundle["output"] = kernel_runner(chain_rules(scope, trees)).run(kernel_input).hex()
    return bundle


def verify_projection(bundle: Dict[str, object]) -> Dict[str, object]:
    """Check a projection bundle with no repository (§4.4).

    Every seal must be a valid Ed25519 seal on this projection; `witnessed` says whether distinct keys of its
    `witness_policy` meet the threshold. With `input` and `output`, both must hash to the projection's digests, and
    the statuses are read by cell id. Any inconsistency raises VarsError; too few witnesses is `witnessed: false`.
    This establishes what the named witnesses vouch for at `tip` — not freshness after it, and not Pass 3."""
    if bundle.get("format") != BUNDLE_FORMAT:
        raise VarsError("unknown projection bundle format")
    cell = Cell.decode(bytes.fromhex(bundle["cell"]))
    if cell.h_schema != H_SCHEMA["projection"] or len(cell.slots) != 5:
        raise VarsError("bundle cell is not a projection")
    atoms: Dict[bytes, bytes] = {}
    for a in bundle["atoms"]:
        raw = bytes.fromhex(a)
        validate_atom(raw)
        atoms[sha256(raw)] = raw
    try:
        tip = parse_utf8(atoms[cell.slots[0]])
        thr, hvec_h = parse_pol1(atoms[cell.slots[4]])
        keys = parse_hvec(atoms[hvec_h], require_sorted=True)
    except KeyError:
        raise VarsError("bundle lacks the projection's tip or witness policy atoms") from None
    if any(weak_public_key(k) for k in keys) or not 1 <= thr <= len(keys):
        raise VarsError("witness policy is malformed or names a weak key")
    witnesses: Set[bytes] = set()
    contexts: Set[bytes] = set()
    for sh in bundle["seals"]:
        seal = Seal.decode(bytes.fromhex(sh))  # verifies the Ed25519 signature
        if seal.h_target != cell.id:
            raise VarsError("a seal in the bundle names another cell than the projection")
        contexts.add(seal.h_scope_ctx)
        if seal.actor_pubkey in keys:
            witnesses.add(seal.actor_pubkey)
    result: Dict[str, object] = {
        "projection": cell.id.hex(),
        "tip": tip,
        "rules": cell.slots[1].hex(),
        "rules_implemented_here": cell.slots[1] in RULES_MODULES,
        "threshold": thr,
        "witnesses": sorted(k.hex() for k in witnesses),
        "witnessed": len(witnesses) >= thr,
        "seal_contexts": sorted(c.hex() for c in contexts),
        "data_ok": None,
        "scope": None,
        "statuses": None,
    }
    if "input" in bundle or "output" in bundle:
        kernel_input = bytes.fromhex(bundle.get("input", ""))
        output = bytes.fromhex(bundle.get("output", ""))
        if sha256(kernel_input) != cell.slots[2]:
            raise VarsError("bundle input does not hash to the projection's input digest")
        if sha256(output) != cell.slots[3]:
            raise VarsError("bundle output does not hash to the projection's state digest")
        if cell.slots[1] in RULES_MODULES and parse_kernel_input(kernel_input)["rules"] != cell.slots[1]:
            raise VarsError("bundle input is not encoded for the rules the projection names")
        order = kernel_input_order(kernel_input)
        n = len(order)
        if len(output) < 4 + n:
            raise VarsError("bundle output is shorter than its cell count")
        result["data_ok"] = True
        result["scope"] = order[int.from_bytes(output[:4], "little")].hex()
        result["statuses"] = {
            cid.hex(): {name: bool(output[4 + i] >> b & 1) for b, name in enumerate(KERNEL_BITS)}
            for i, cid in enumerate(order)
        }
    return result


ATTESTATION_FORMAT = "vars-1.attestation-bundle@1"


def export_attestation(repo: "GitVarsRepo", scope: str, decision_id: bytes,
                       projection_id: Optional[bytes] = None) -> Dict[str, object]:
    """A self-contained bundle for a contract or decision at the scope's tip: the cell, the governing scope cell, the
    atoms its evaluator policy and statement need, every verdict on it and every seal on it and on those verdicts,
    and optionally a projection bundle whose statuses cover them. With a projection, the scope is the one governing
    the projection's tip, which its evidence is about; a later rotation does not change it."""
    tip = repo.ref_commit(scope)
    atoms, cells, seals = repo.read_cas_tree(tip)
    d = cells.get(decision_id)
    if d is None or d.h_schema not in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
        raise VarsError("not a contract or decision cell of this scope")
    at = tip
    if projection_id is not None:
        pc = cells.get(projection_id)
        if pc is None or pc.h_schema != H_SCHEMA["projection"]:
            raise VarsError("not a projection cell of this scope")
        at = parse_utf8(atoms[pc.slots[0]])
    s_cell = cells[repo._evaluate_commit_chain(scope, repo.commit_chain(at))["active_scope_id"]]
    pol = d.slots[3] if d.slots[3] != H_EMPTY else s_cell.slots[0]
    verdicts = [c for c in cells.values() if c.h_schema == H_SCHEMA["verdict"] and c.h_payload == decision_id]
    need = [pol, parse_pol1(atoms[pol])[1], d.h_payload]
    for w in verdicts:
        need += [w.h_attests, w.slots[2]]
    targets = {decision_id} | {w.id for w in verdicts}
    bundle: Dict[str, object] = {
        "format": ATTESTATION_FORMAT,
        "cell": d.encode().hex(),
        "scope": s_cell.encode().hex(),
        "atoms": sorted({atoms[h].hex() for h in need if h in atoms}),
        "verdicts": sorted(w.encode().hex() for w in verdicts),
        "seals": sorted(x.encode().hex() for x in seals.values() if x.h_target in targets),
    }
    if projection_id is not None:
        bundle["projection"] = export_projection(repo, scope, projection_id)
    return bundle


def verify_attestation(bundle: Dict[str, object], require: Optional[List[bytes]] = None) -> Dict[str, object]:
    """Recompute §4.2 Pass 3 for one contract or decision from a bundle, with no repository.

    `attested`: over the supplied verdicts, ATTESTED verdicts on the cell, sealed by distinct keys of its evaluator
    policy (else the bundled scope's admission policy), meet the threshold, after excluding verdicts contradicted by an
    INVALID verdict of the same verifier sealed by a policy key. A supplier can omit verdicts, so on its own this is
    `evidence: "supplied"`.

    With a projection bundle whose tip holds the cell, the projection's kernel input — every cell and verified seal
    at that tip, committed to by its digest — is the evidence: the bundle must supply every verdict on the cell that
    the input holds, and `attested_at_tip` is Pass 3 recomputed from the input and output alone (`pass3_at_tip`,
    local and foreign verdicts as the lens counts them; `evidence: "complete_at_tip"`). `accepted` requires that,
    the projection witnessed, and no supplied verdict from after the tip contradicting it by a policy key; it says
    nothing else about the chain after the tip. Any inconsistency raises VarsError. Decisions that require a
    computation need replay, hence the repository.

    The chain's admission quorum may rotate its roster, so a key that refused a release can be rotated out and
    later releases settle without it. A reader who wants a veto for certain keys pins them: with `require`, each
    must also endorse the cell at the tip and witness the projection, and `required_missing` lists those that
    do not."""
    if bundle.get("format") != ATTESTATION_FORMAT:
        raise VarsError("unknown attestation bundle format")
    d = Cell.decode(bytes.fromhex(bundle["cell"]))
    if d.h_schema not in (H_SCHEMA["contract"], H_SCHEMA["decision"]) or len(d.slots) != 4:
        raise VarsError("bundle cell is not a contract or decision")
    if d.slots[1] != H_EMPTY:
        raise VarsError("a decision that requires a computation needs replay, hence the repository")
    sc = Cell.decode(bytes.fromhex(bundle["scope"]))
    if sc.h_schema != H_SCHEMA["scope"]:
        raise VarsError("bundle scope is not a scope cell")
    atoms: Dict[bytes, bytes] = {}
    for a in bundle["atoms"]:
        raw = bytes.fromhex(a)
        validate_atom(raw)
        atoms[sha256(raw)] = raw
    pol = d.slots[3] if d.slots[3] != H_EMPTY else sc.slots[0]
    try:
        thr, hvec_h = parse_pol1(atoms[pol])
        keys = set(parse_hvec(atoms[hvec_h], require_sorted=True))
    except KeyError:
        raise VarsError("bundle lacks the evaluator policy atoms") from None
    if any(weak_public_key(k) for k in keys) or not 1 <= thr <= len(keys):
        raise VarsError("evaluator policy is malformed or names a weak key")
    verdicts: Dict[bytes, Cell] = {}
    for vh in bundle["verdicts"]:
        w = Cell.decode(bytes.fromhex(vh))
        if w.h_schema != H_SCHEMA["verdict"] or w.h_payload != d.id:
            raise VarsError("a verdict in the bundle does not judge this cell")
        verdicts[w.id] = w
    signers: Dict[bytes, set] = {d.id: set(), **{wid: set() for wid in verdicts}}
    for sh in bundle["seals"]:
        seal = Seal.decode(bytes.fromhex(sh))  # verifies the Ed25519 signature
        if seal.h_target not in signers:
            raise VarsError("a seal in the bundle names an unrelated cell")
        signers[seal.h_target].add(seal.actor_pubkey)
    contradicted = {w.slots[2] for wid, w in verdicts.items()
                    if w.slots[1] == H_VERDICT_INVALID and signers[wid] & keys}
    attests = lambda w: w.h_attests in atoms and d.id in parse_hvec(atoms[w.h_attests], require_sorted=True)
    counted = [wid for wid, w in verdicts.items() if attests(w)
               and w.slots[0] == H_EMPTY and w.slots[1] == H_ATTESTED and w.slots[2] not in contradicted]
    endorsers = set().union(*(signers[wid] & keys for wid in counted)) if counted else set()
    result: Dict[str, object] = {
        "cell": d.id.hex(),
        "statement": parse_utf8(atoms[d.h_payload]) if d.h_payload in atoms else None,
        "scope": sc.id.hex(),
        "threshold": thr,
        "policy_keys": sorted(k.hex() for k in keys),
        "authors": sorted(k.hex() for k in signers[d.id]),
        "endorsers": sorted(k.hex() for k in endorsers),
        "attested": len(endorsers) >= thr,
        "evidence": "supplied",
        "tip": None,
        "projection_witnessed": None,
        "attested_at_tip": None,
        "active_at_tip": None,
        "accepted": False,
    }
    if "projection" not in bundle:
        return result
    pr = verify_projection(bundle["projection"])
    if not pr["data_ok"]:
        raise VarsError("the projection in an attestation bundle must carry its input and output")
    result["tip"] = pr["tip"]
    result["projection_witnessed"] = pr["witnessed"]
    ki = parse_kernel_input(bytes.fromhex(bundle["projection"]["input"]))
    kc = ki["cells"]
    pos = {c["id"]: i for i, c in enumerate(kc)}
    if d.id not in pos:
        return result  # the tip predates the cell
    if bytes.fromhex(pr["scope"]) != sc.id:
        raise VarsError("the bundled scope does not govern the projection's tip")
    at_tip = {c["id"] for c in kc if c["schema"] == H_SCHEMA["verdict"] and c["payload"] == d.id}
    missing = at_tip - set(verdicts)
    if missing:
        raise VarsError(f"the bundle omits {len(missing)} verdict(s) on this cell that the projection's tip holds")
    settled, end, t_thr, p = pass3_at_tip(ki, bytes.fromhex(bundle["projection"]["output"]), pos[d.id])
    if p != pol or t_thr != thr or len(ki["pols"][p][1]) != len(keys):
        raise VarsError("the projection's input disagrees with the bundle on the evaluator policy")
    key_of = dict(zip(ki["pols"][p][1], sorted(keys)))  # both orders are the keys' byte order
    # Verdicts supplied from after the tip contradict as at the tip: an INVALID by a policy key withdraws the
    # ATTESTED verdicts of its own verifier, and Pass 3 is recomputed without them
    later_blocks = {w.slots[2] for wid, w in verdicts.items()
                    if wid not in at_tip and w.slots[1] == H_VERDICT_INVALID and signers[wid] & keys}
    now, end_now = settled, end
    if later_blocks:
        now, end_now, _, _ = pass3_at_tip(ki, bytes.fromhex(bundle["projection"]["output"]), pos[d.id], later_blocks)
    st = pr["statuses"][d.id.hex()]
    result["evidence"] = "complete_at_tip"
    result["endorsers_at_tip"] = sorted(key_of[k].hex() for k in end)
    result["attested_at_tip"] = settled
    result["active_at_tip"] = st["active"] and not st["stale"]
    result["contradicted_after_tip"] = settled and not now
    standing = {key_of[k].hex() for k in end_now}
    missing = [k.hex() for k in require or [] if k.hex() not in standing or k.hex() not in pr["witnesses"]]
    result["required_missing"] = missing
    result["accepted"] = bool(now and pr["witnessed"] and not missing)
    return result


def _main(argv: List[str]) -> int:
    if len(argv) == 2 and argv[0] == "verify-projection":
        try:
            result = verify_projection(json.loads(Path(argv[1]).read_text(encoding="utf-8")))
        except (VarsError, ValueError, KeyError) as e:
            print(f"refused: {e}", file=sys.stderr)
            return 2
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0 if result["witnessed"] and result["data_ok"] in (True, None) else 1
    if len(argv) >= 2 and argv[0] == "verify-attestation" and len(argv) % 2 == 0 \
            and all(a == "--require" for a in argv[2::2]):
        try:
            result = verify_attestation(json.loads(Path(argv[1]).read_text(encoding="utf-8")),
                                        require=[bytes.fromhex(k) for k in argv[3::2]])
        except (VarsError, ValueError, KeyError) as e:
            print(f"refused: {e}", file=sys.stderr)
            return 2
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0 if result["accepted"] else 1
    print("usage: vars1.py verify-projection BUNDLE.json | verify-attestation BUNDLE.json [--require PUBKEY]...",
          file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(_main(sys.argv[1:]))
