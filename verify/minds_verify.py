#!/usr/bin/env python3
"""VARS-1 offline bundle verifier (VARS-1-SPEC.md §4.4): one file, standard library only.

Checks a projection bundle or an attestation bundle with no repository, no git, no network and no sibling checkout:
copy this file anywhere and run

    python3 -I minds_verify.py verify-attestation BUNDLE.json --require PUBKEY [--require PUBKEY]...
    python3 -I minds_verify.py verify-projection BUNDLE.json --require PUBKEY [--require PUBKEY]...
    python3 -I minds_verify.py inspect-attestation|inspect-projection BUNDLE.json

`verify-*` trusts only keys the reader names; `inspect-*` checks a bundle against its own policies and claims no
trust. With `--kernel RULES.wasm`, a reader who has Node also runs the projection's rules module on its input, so the
output is checked here rather than taken on its witnesses' word.

`vars1.py` delegates its bundle checks here, so there is one implementation. Every result carries `explain`: which
witnesses and keys were counted, which verifiers were blocked, the scope epoch, the policy, why a pinned key is
missing, and whether the rules identity is one this verifier interprets. `explain` is derived from the bundle by the
same computation as the verdict fields; it is a reading aid, not authority, and a reader who doubts it recomputes.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import struct
import subprocess
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Optional, Set, Tuple

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

# The rules identities this verifier interprets, each with the kernel input encoding it reads (§4.3, RULES-V2.md §3):
# `kernel/lens.wasm` (v1); `kernel/` built with `commit-bound` (v1b: v1's encoding and output, one more refusal); and
# `kernel2/lens2.wasm` (v2: typed references, listed in the input). They are only names here; nothing is executed. A
# projection that names other rules is reported as unsupported, never read. `vars1.py` refuses to load unless every
# rules identity it implements is one of these, with its encoding; a release profile (`tools/minds_chain.py`) reads
# this table from the file's bytes, so it stays one row per line: id, encoding, name.
KNOWN_RULES_TABLE = """
874e714dd14e6d7c144a4c377ae649f4124ea3788b17fa1ff86cf1be8a168ecb v1 H_LENS_KERNEL
2a2e440a548b73adbb3072c23e21ee8d9d7bd7867fa7bc3e38150c477f1b11cd v1 H_LENS_KERNEL_V1B
1ca798b5013bf45735d3de836ecff23ca148e5bac2f6ca2c7d6289c2cf26707e v2 H_LENS_KERNEL_V2
"""
_RULES_ROWS = [row.split(" ") for row in KNOWN_RULES_TABLE.strip("\n").split("\n")]
KNOWN_RULES: Dict[bytes, str] = {bytes.fromhex(h): enc for h, enc, _ in _RULES_ROWS}
_RULES_BY_NAME = {name: bytes.fromhex(h) for h, _, name in _RULES_ROWS}
H_LENS_KERNEL = _RULES_BY_NAME["H_LENS_KERNEL"]
H_LENS_KERNEL_V1B = _RULES_BY_NAME["H_LENS_KERNEL_V1B"]
H_LENS_KERNEL_V2 = _RULES_BY_NAME["H_LENS_KERNEL_V2"]
KERNEL2_MAGIC = 0x32524156  # "VAR2": the first word of a v2 kernel input


MAX_KIN1_BYTES = 1 << 20  # a rules input carried as an atom (KIN1, §1.1): the counterexample of a rules change


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

def validate_atom(raw: bytes, extended: Optional[Callable[[bytes], None]] = None) -> None:
    """Refuse an atom that is not well formed. SGS1 states and SigmaNodeV2 nodes need Book I (sigma-glyph) to decode:
    `extended` checks them, and without it (offline) they are refused, since no bundle check reads one."""
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
    elif raw[:4] == b"SGS1" or (raw[:8] != b"\x00asm\x01\x00\x00\x00" and raw[0] in (0x00, 0x01, 0x02, 0xFF)):
        if extended is None:
            raise VarsError("an SGS1 state or SigmaNodeV2 node needs Book I to check: not checkable offline")
        extended(raw)
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
    elif raw[:4] == b"KIN1":
        if len(raw) - 4 > MAX_KIN1_BYTES:
            raise VarsError("KIN1 rules input over 1 MiB")  # any bytes: an input of rules, valid or not (§4.3)
    elif raw[:8] == b"\x00asm\x01\x00\x00\x00":
        pass  # a wasm module: identity is its hash; only the rules this host implements are ever executed
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

KERNEL_BITS = ("accepted", "invalidated", "effective", "retired", "superseded", "active", "stale")


# ---------------------------------------------------------------------------
# §4.4 Projection bundles: what a client without the repository holds and checks
# ---------------------------------------------------------------------------
BUNDLE_FORMAT = "vars-1.projection-bundle@1"


def parse_kernel_input(kernel_input: bytes, encoding: str = "v1") -> Dict[str, object]:
    """A kernel input (§4.3) in `encoding` as data: POL1 rosters as key indices, cells in order with their slots,
    edges and references as cell indices, and seals as (target, context, key index, commit). Key bytes are not in the
    input, only their order. A cell's `refs` are the cells its payload and slots name as the rules read them: in v1
    every payload or slot equal to a cell id; in v2 the input's own list (RULES-V2.md §3), each entry checked to name
    an older cell whose id is the value at its position."""
    def u32(off: int) -> int:
        if off + 4 > len(kernel_input):
            raise VarsError("kernel input truncated")
        return struct.unpack_from("<I", kernel_input, off)[0]

    def take(off: int, n: int) -> bytes:
        if off + n > len(kernel_input):
            raise VarsError("kernel input truncated")
        return kernel_input[off:off + n]

    if encoding not in ("v1", "v2"):
        raise VarsError(f"no kernel input encoding {encoding!r}")
    v2 = encoding == "v2"
    if v2 and u32(0) != KERNEL2_MAGIC:
        raise VarsError("the kernel input is not in the v2 encoding of the rules it names")
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
            off += 8  # the schema mask (mask_lo, mask_hi): the kernel checks it; Pass 3 does not read it
        edges = []
        for _ in range(5):
            m = u32(off)
            edges.append([u32(off + 4 + 4 * j) for j in range(m)])
            off += 4 + 4 * m
        cell = {"id": cid, "schema": schema, "payload": payload, "origin": origin, "slots": slots,
                "relies": edges[0], "attests": edges[1], "edges": edges}
        if v2:
            vals, i = (payload, *slots), len(cells)
            listed = [(u32(off + 4 + 8 * j), u32(off + 8 + 8 * j)) for j in range(u32(off))]
            off += 4 + 8 * len(listed)
            if any(not (q < len(vals) and x < i and vals[q] == cells[x]["id"]) for q, x in listed):
                raise VarsError("a v2 kernel input lists a reference its cell does not hold")
            cell["refs"] = [x for _, x in listed]
        cells.append(cell)
    if not v2:
        pos = {c["id"]: i for i, c in enumerate(cells)}
        for c in cells:
            c["refs"] = [pos[x] for x in (c["payload"], *c["slots"]) if x in pos]
    seals = []
    for j in range(u32(off)):
        seals.append(tuple(u32(off + 4 + 16 * j + 4 * i) for i in range(4)))
    if off + 4 + 16 * len(seals) != len(kernel_input):
        raise VarsError("kernel input has trailing bytes")
    return {"pols": pols, "cells": cells, "seals": seals, "encoding": encoding}


def pass3_at_tip(ki: Dict[str, object], output: bytes, di: int,
                 blocked_after: Optional[Set[bytes]] = None,
                 trace: Optional[Dict[str, object]] = None) -> Tuple[bool, Set[int], int, bytes]:
    """§4.2 Pass 3 for the contract or decision at index `di` (without `required_comp`), from a parsed kernel input
    and the kernel's output alone: whether it is Settled, the key indices that endorse it, the threshold, and the
    policy hash. Endorsers are counted as the lens counts them: every admitted seal on a local verdict; on a
    foreign verdict, seals under a scope of its origin that a live acceptance (of it or of a newer cell of its
    origin that references it, by an edge or by a reference the input's rules read) names, by that scope's
    admission keys. A contradicting INVALID verdict of the same verifier, endorsed by a policy key, blocks;
    `blocked_after` adds the verifier ids that such INVALID verdicts recorded after the tip block. With `trace`, it
    is filled with what was counted: `counted` maps each counted verdict's index to the key indices that endorse it,
    `blocked_at_tip` holds the verifier ids blocked by INVALID verdicts at the tip, and `blocked_after` those added
    from after it."""
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
    si = struct.unpack_from("<I", output, 0)[0]
    if si >= n:
        raise VarsError("kernel output names a scope outside its input")
    scope_cell = kc[si]
    p = d["slots"][3] if d["slots"][3] != H_EMPTY else scope_cell["slots"][0]
    if p not in pols:
        raise VarsError("the kernel input lacks the evaluator policy")
    thr, pk = pols[p][0], set(pols[p][1])
    did = d["id"]
    bad = [b for b in range(n) if live[b] and kc[b]["schema"] == H_SCHEMA["verdict"]
           and kc[b]["slots"][1] == H_VERDICT_INVALID and kc[b]["payload"] == did and endorsers(b) & pk]
    blocked = {kc[b]["slots"][2] for b in bad} | (blocked_after or set())
    end: Set[int] = set()
    counted: Dict[int, Set[int]] = {}
    for w in children[di]:
        c = kc[w]
        if not live[w] or di not in c["attests"] or c["schema"] != H_SCHEMA["verdict"] or c["payload"] != did:
            continue
        if c["slots"][2] in blocked or c["slots"][0] != H_EMPTY or c["slots"][1] != H_ATTESTED:
            continue
        got = endorsers(w) & pk
        if got:
            counted[w] = got
        end |= got
    if trace is not None:
        trace.update(counted=counted, blocked_at_tip={kc[b]["slots"][2] for b in bad},
                     blocked_after=set(blocked_after or set()) - {kc[b]["slots"][2] for b in bad})
    return live[di] and len(end) >= thr, end, thr, p


def kernel_input_order(kernel_input: bytes, encoding: str = "v1") -> List[bytes]:
    """The cell ids of a kernel input (§4.3), in its order; the kernel's output indexes cells by this order."""
    return [c["id"] for c in parse_kernel_input(kernel_input, encoding)["cells"]]

RULES_UNSUPPORTED = ("this verifier interprets only the rules of KNOWN_RULES (v1, v1b, v2): the digests are checked, "
                     "but the kernel input and output are not read as statuses, scope or Pass 3")


def rules_status(rules: bytes) -> Dict[str, object]:
    """Whether a rules identity is one this verifier interprets (`KNOWN_RULES`), and the input encoding it reads."""
    if rules in KNOWN_RULES:
        return {"id": rules.hex(), "status": "known", "encoding": KNOWN_RULES[rules], "reason": None}
    return {"id": rules.hex(), "status": "unsupported", "encoding": None, "reason": RULES_UNSUPPORTED}


def _bundle_atoms(bundle: Dict[str, object]) -> Dict[bytes, bytes]:
    atoms: Dict[bytes, bytes] = {}
    for a in bundle["atoms"]:
        raw = bytes.fromhex(a)
        validate_atom(raw)
        atoms[sha256(raw)] = raw
    return atoms


# A reader's own run of the rules (optional, `--kernel`). Every other check here is Python's standard library; this
# one runs the rules module under Node's WebAssembly, as the host does (§4.3), so a reader who has Node checks the one
# thing a projection's witnesses otherwise vouch for: that the bundle's output is what its rules give its input.
KERNEL_DRIVER = r"""
const chunks = [];
process.stdin.on("data", (c) => chunks.push(c));
process.stdin.on("end", async () => {
  const [mod, inp] = Buffer.concat(chunks).toString().trim().split("\n");
  const { instance } = await WebAssembly.instantiate(Buffer.from(mod, "hex"), {});
  const { memory, reset, alloc, run } = instance.exports;
  const input = Buffer.from(inp, "hex");
  reset();
  const ptr = alloc(input.length);
  new Uint8Array(memory.buffer, ptr, input.length).set(input);
  const out = run(ptr, input.length);
  if (out < 0) { process.stdout.write(`E${out}\n`); return; }
  const n = new DataView(memory.buffer).getUint32(out, true);
  process.stdout.write(Buffer.from(new Uint8Array(memory.buffer, out + 4, n)).toString("hex") + "\n");
});
"""
KERNEL_TIMEOUT = 120.0  # seconds a reader's run of the rules may take before it is reported as not run
# The one reply the driver gives: a refusal code, or the output as lowercase hex, on one line
KERNEL_REPLY = re.compile(rb"(E-[1-9][0-9]{0,9}|(?:[0-9a-f]{2})+)\n")


def run_rules(module: bytes, kernel_input: bytes, timeout: float = KERNEL_TIMEOUT) -> Tuple[str, object]:
    """Run a rules module on one kernel input under Node: ("output", bytes after the length word), ("refusal",
    its negative code), or ("not_run", why) when Node is missing, does not start, fails (a trap included), outlasts
    `timeout` seconds or replies other than the driver does. Not running is a fact about this host, never about the
    input. Node is the binary `node` on PATH, run with an empty environment: inherited startup code (NODE_OPTIONS
    --require, NODE_PATH) would run in the engine beside the module, which its hash does not cover (Codex review of
    PR #24, P24-F1)."""
    node = shutil.which("node")
    if node is None:
        return "not_run", "node is not on PATH"
    try:
        got = subprocess.run([node, "-e", KERNEL_DRIVER], capture_output=True, timeout=timeout, env={},
                             input=(module.hex() + "\n" + kernel_input.hex() + "\n").encode())
    except subprocess.TimeoutExpired:
        return "not_run", f"the run outlasted {timeout:g} s"
    except OSError as e:
        return "not_run", f"node did not start: {e}"[:200]
    if got.returncode != 0:
        why = (got.stderr.decode("utf-8", "replace").strip().splitlines() or ["no output"])[-1]
        return "not_run", f"node failed: {why[:200]}"
    if not KERNEL_REPLY.fullmatch(got.stdout):
        return "not_run", f"node replied other than the driver does: {got.stdout[:80]!r}"
    line = got.stdout[:-1].decode("ascii")
    if line.startswith("E"):
        return "refusal", int(line[1:])
    return "output", bytes.fromhex(line)


def verify_projection(bundle: Dict[str, object], require: Optional[List[bytes]] = None,
                      kernels: Iterable[bytes] = (), timeout: float = KERNEL_TIMEOUT) -> Dict[str, object]:
    """Check a projection bundle with no repository (§4.4).

    Every seal must be a valid Ed25519 seal on this projection; `witnessed` says whether distinct keys of its
    `witness_policy` meet the threshold. With `input` and `output`, both must hash to the projection's digests; if the
    projection names rules of `KNOWN_RULES`, the input is read in their encoding (an input in another is refused), the
    statuses are read by cell id and `scope` is the scope cell at the tip (the scope epoch). A projection naming other
    rules has `rules_status: "unsupported"` and no statuses or scope: its data is not interpreted as known. Any
    inconsistency raises VarsError; too few witnesses is `witnessed: false`.
    This establishes what the named witnesses vouch for at `tip` — not freshness after it, and not Pass 3.

    The witness policy is the projection's own: whoever made it chose it. A reader trusts a projection only for keys
    it chose beforehand; `require` names them, and `required_missing` lists those that did not witness it.

    That the output is what the rules give the input is the witnesses' word, `kernel: "witnessed"`, unless the reader
    supplies the rules module in `kernels` (module bytes; the one used is the one whose SHA-256 is the projection's
    rules, so its identity is the reader's, not the bundle's). Then it is run on the input (`run_rules`): the same
    output is `kernel: "verified_here"`; a refusal or another output raises VarsError; a run that cannot be made
    leaves `kernel: "witnessed"` with the reason in `explain.kernel`."""
    if bundle.get("format") != BUNDLE_FORMAT:
        raise VarsError("unknown projection bundle format")
    cell = Cell.decode(bytes.fromhex(bundle["cell"]))
    if cell.h_schema != H_SCHEMA["projection"] or len(cell.slots) != 5:
        raise VarsError("bundle cell is not a projection")
    atoms = _bundle_atoms(bundle)
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
    witness_seals: List[Dict[str, object]] = []
    for sh in bundle["seals"]:
        seal = Seal.decode(bytes.fromhex(sh))  # verifies the Ed25519 signature
        if seal.h_target != cell.id:
            raise VarsError("a seal in the bundle names another cell than the projection")
        contexts.add(seal.h_scope_ctx)
        if seal.actor_pubkey in keys:
            witnesses.add(seal.actor_pubkey)
        witness_seals.append({"seal": seal.id.hex(), "key": seal.actor_pubkey.hex(),
                              "context": seal.h_scope_ctx.hex(), "counted": seal.actor_pubkey in keys})
    rules = rules_status(cell.slots[1])
    result: Dict[str, object] = {
        "projection": cell.id.hex(),
        "tip": tip,
        "rules": cell.slots[1].hex(),
        "rules_implemented_here": rules["status"] == "known",
        "rules_status": rules["status"],
        "threshold": thr,
        "witnesses": sorted(k.hex() for k in witnesses),
        "witnessed": len(witnesses) >= thr,
        "seal_contexts": sorted(c.hex() for c in contexts),
        "data_ok": None,
        "scope": None,
        "statuses": None,
        "required_missing": [k.hex() for k in require or [] if k not in witnesses],
        "kernel": None,
    }
    result["explain"] = {
        "rules": rules,
        "witness_policy": {"id": cell.slots[4].hex(), "threshold": thr, "keys": [k.hex() for k in keys]},
        "witness_seals": sorted(witness_seals, key=lambda x: (x["key"], x["seal"])),
        "witnesses_missing": sorted(k.hex() for k in set(keys) - witnesses),
        "scope_epoch": None,
        "kernel": None,
    }
    if "input" in bundle or "output" in bundle:
        kernel_input = bytes.fromhex(bundle.get("input", ""))
        output = bytes.fromhex(bundle.get("output", ""))
        if sha256(kernel_input) != cell.slots[2]:
            raise VarsError("bundle input does not hash to the projection's input digest")
        if sha256(output) != cell.slots[3]:
            raise VarsError("bundle output does not hash to the projection's state digest")
        result["data_ok"] = True
        if rules["status"] != "known":
            return result
        # the reader's own run first, on the raw bytes, before anything of the output is read
        kernel = {"status": "witnessed", "module": None, "reason": "no module of these rules was supplied"}
        module = {sha256(m): m for m in kernels}.get(cell.slots[1])
        if module is not None:
            kernel["module"] = cell.slots[1].hex()
            how, got = run_rules(module, kernel_input, timeout)
            if how == "refusal":
                raise VarsError(f"the projection's rules refuse its input (E{got}): its witnesses vouch for an output "
                                "the rules do not give")
            if how == "output" and got != output:
                raise VarsError("the projection's rules give its input another output than the bundle's")
            if how == "output":
                kernel.update(status="verified_here", reason=None)
            else:
                kernel["reason"] = got
        result["kernel"], result["explain"]["kernel"] = kernel["status"], kernel
        order = kernel_input_order(kernel_input, rules["encoding"])
        n = len(order)
        if len(output) < 4 + n:
            raise VarsError("bundle output is shorter than its cell count")
        si = int.from_bytes(output[:4], "little")
        if si >= n:
            raise VarsError("bundle output names a scope outside its input")
        result["scope"] = order[si].hex()
        result["explain"]["scope_epoch"] = result["scope"]
        result["statuses"] = {
            cid.hex(): {name: bool(output[4 + i] >> b & 1) for b, name in enumerate(KERNEL_BITS)}
            for i, cid in enumerate(order)
        }
    return result


ATTESTATION_FORMAT = "vars-1.attestation-bundle@1"


def verify_attestation(bundle: Dict[str, object], require: Optional[List[bytes]] = None,
                       kernels: Iterable[bytes] = (), timeout: float = KERNEL_TIMEOUT) -> Dict[str, object]:
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
    computation need replay, hence the repository. A projection naming rules outside `KNOWN_RULES` is not read:
    `rules_status: "unsupported"`, and nothing is accepted on it.

    The chain's admission quorum may rotate its roster, so a key that refused a release can be rotated out and
    later releases settle without it. A reader who wants a veto for certain keys pins them: with `require`, each
    must also endorse the cell at the tip and witness the projection, and `required_missing` lists those that
    do not (`explain.required` says why). `kernels` and `timeout` are the projection's (`verify_projection`):
    `kernel` says whether its output was the witnesses' word or checked here."""
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
    atoms = _bundle_atoms(bundle)
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

    def verifier(h: bytes) -> str:
        """A verifier id as text when its atom is supplied, else its hash."""
        try:
            return parse_utf8(atoms[h])
        except (KeyError, VarsError):
            return h.hex()

    def witness_rows(rows: Iterable[Tuple[bytes, bytes, Set[bytes]]]) -> List[Dict[str, object]]:
        return sorted(({"verdict": wid.hex(), "verifier": verifier(vid), "endorsers": sorted(k.hex() for k in ks)}
                       for wid, vid, ks in rows), key=lambda x: x["verdict"])

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
        "rules_status": None,
        "kernel": None,
    }
    explain: Dict[str, object] = {
        "policy": {"id": pol.hex(), "source": "evaluator_policy" if d.slots[3] != H_EMPTY else "scope_admission",
                   "threshold": thr, "keys": sorted(k.hex() for k in keys)},
        "supplied": {
            "counted": witness_rows((wid, verdicts[wid].slots[2], signers[wid] & keys)
                                    for wid in counted if signers[wid] & keys),
            "blocked_verifiers": sorted(verifier(v) for v in contradicted),
        },
        "rules": None,
        "scope_epoch": None,
        "at_tip": None,
        "after_tip": None,
        "required": [{"key": k.hex(), "reasons": ["no projection: a pinned key is checked only at a projection's tip"]}
                     for k in require or []],
        "projection": None,
    }
    result["explain"] = explain
    if require:
        result["required_missing"] = [k.hex() for k in require]
    if "projection" not in bundle:
        return result
    pr = verify_projection(bundle["projection"], kernels=kernels, timeout=timeout)
    if not pr["data_ok"]:
        raise VarsError("the projection in an attestation bundle must carry its input and output")
    result["tip"] = pr["tip"]
    result["projection_witnessed"] = pr["witnessed"]
    result["rules_status"] = pr["rules_status"]
    result["kernel"] = pr["kernel"]
    explain["rules"] = pr["explain"]["rules"]
    explain["projection"] = pr["explain"]
    if pr["rules_status"] != "known":
        for row in explain["required"]:
            row["reasons"] = ["the projection's rules are unsupported: nothing is read at its tip"]
        return result
    ki = parse_kernel_input(bytes.fromhex(bundle["projection"]["input"]), pr["explain"]["rules"]["encoding"])
    kc = ki["cells"]
    pos = {c["id"]: i for i, c in enumerate(kc)}
    explain["scope_epoch"] = pr["scope"]
    if d.id not in pos:
        for row in explain["required"]:
            row["reasons"] = ["the projection's tip predates the cell"]
        return result  # the tip predates the cell
    if bytes.fromhex(pr["scope"]) != sc.id:
        raise VarsError("the bundled scope does not govern the projection's tip")
    at_tip = {c["id"] for c in kc if c["schema"] == H_SCHEMA["verdict"] and c["payload"] == d.id}
    missing = at_tip - set(verdicts)
    if missing:
        raise VarsError(f"the bundle omits {len(missing)} verdict(s) on this cell that the projection's tip holds")
    output = bytes.fromhex(bundle["projection"]["output"])
    trace: Dict[str, object] = {}
    settled, end, t_thr, p = pass3_at_tip(ki, output, pos[d.id], trace=trace)
    if p != pol or t_thr != thr or len(ki["pols"][p][1]) != len(keys):
        raise VarsError("the projection's input disagrees with the bundle on the evaluator policy")
    key_of = dict(zip(ki["pols"][p][1], sorted(keys)))  # both orders are the keys' byte order
    # Verdicts supplied from after the tip contradict as at the tip: an INVALID by a policy key withdraws the
    # ATTESTED verdicts of its own verifier, and Pass 3 is recomputed without them
    later_blocks = {w.slots[2] for wid, w in verdicts.items()
                    if wid not in at_tip and w.slots[1] == H_VERDICT_INVALID and signers[wid] & keys}
    now, end_now, trace_now = settled, end, trace
    if later_blocks:
        trace_now = {}
        now, end_now, _, _ = pass3_at_tip(ki, output, pos[d.id], later_blocks, trace=trace_now)
    st = pr["statuses"][d.id.hex()]
    result["evidence"] = "complete_at_tip"
    result["endorsers_at_tip"] = sorted(key_of[k].hex() for k in end)
    result["attested_at_tip"] = settled
    result["active_at_tip"] = st["active"] and not st["stale"]
    result["contradicted_after_tip"] = settled and not now
    standing = {key_of[k].hex() for k in end_now}
    at_tip_keys = {key_of[k].hex() for k in end}
    rows = lambda tr: witness_rows((kc[w]["id"], kc[w]["slots"][2], {key_of[k] for k in ks})
                                   for w, ks in tr["counted"].items())
    explain["at_tip"] = {"counted": rows(trace), "blocked_verifiers": sorted(verifier(v) for v in trace["blocked_at_tip"]),
                         "endorsers": sorted(at_tip_keys), "settled": settled}
    explain["after_tip"] = {"blocked_verifiers": sorted(verifier(v) for v in trace_now["blocked_after"]),
                            "counted": rows(trace_now), "withdrawn_endorsers": sorted(at_tip_keys - standing)}
    required = []
    for k in require or []:
        reasons = []
        if k.hex() not in at_tip_keys:
            reasons.append("does not endorse the cell at the projection's tip")
        elif k.hex() not in standing:
            reasons.append("its endorsement is withdrawn by an INVALID verdict after the tip")
        if k.hex() not in pr["witnesses"]:
            reasons.append("did not witness the projection")
        required.append({"key": k.hex(), "reasons": reasons})
    explain["required"] = required
    result["required_missing"] = [row["key"] for row in required if row["reasons"]]
    result["accepted"] = bool(now and pr["witnessed"] and not result["required_missing"])
    return result


USAGE = """usage: minds_verify.py COMMAND BUNDLE.json [--require PUBKEY]... [--kernel RULES.wasm]...
  verify-projection   exit 0 iff every pinned key witnessed it, its data matches, and its rules are known
  verify-attestation  exit 0 iff it is accepted at a witnessed tip and every pinned key endorsed and witnessed it
  inspect-projection  exit 0 iff it is consistent and witnessed under its own policy (no trust claimed)
  inspect-attestation exit 0 iff it is accepted under the bundle's own scope policy (no trust claimed); its result
                      says `accepted_under_own_policy`, never `accepted`, the word of verify-attestation
A bundle must read one way: one that is not UTF-8 JSON, or whose object names a key twice, is refused.
verify-* needs at least one --require: a bundle's own policy was chosen by whoever made it, not by the reader.
Exit 0 or 1 is the verdict; 2 a refusal of the bundle or the command line; 3 an error of this file, never a verdict.
--kernel runs the projection's rules module on its input under Node (the file whose SHA-256 is its rules), so the
output is checked here, not taken on its witnesses' word; then every command also needs `kernel: verified_here`."""


def read_bundle(raw: bytes) -> object:
    """The bundle in `raw`, read one way only: an object that names a key twice has two readings (Python keeps the
    last value, other readers the first), so it is refused rather than read by one convention."""
    def one_reading(pairs: List[Tuple[str, object]]) -> Dict[str, object]:
        if len({k for k, _ in pairs}) != len(pairs):
            raise VarsError("an object of the bundle names a key twice")
        return dict(pairs)
    return json.loads(raw.decode("utf-8"), object_pairs_hook=one_reading)


def main(argv: List[str]) -> int:
    """The command line: exit 0 or 1 is a verdict, 2 a refusal of the bundle or the command line, 3 an error of this
    file, which no verdict uses (an uncaught Python error would exit 1, the code of a negative verdict)."""
    try:
        return _run(argv)
    except Exception as e:
        print(f"error: {type(e).__name__}: {e}", file=sys.stderr)
        return 3


def _run(argv: List[str]) -> int:
    cmds = ("verify-projection", "verify-attestation", "inspect-projection", "inspect-attestation")
    opts = list(zip(argv[2::2], argv[3::2]))
    if len(argv) < 2 or argv[0] not in cmds or len(argv) % 2 \
            or not all(k in ("--require", "--kernel") for k, _ in opts):
        print(USAGE, file=sys.stderr)
        return 2
    cmd = argv[0]
    pins = [v for k, v in opts if k == "--require"]
    modules = [v for k, v in opts if k == "--kernel"]
    if cmd.startswith("verify-") and not pins:
        print("refused: verify needs --require PUBKEY, keys you trust; inspect-* checks consistency only",
              file=sys.stderr)
        return 2
    try:
        bundle = read_bundle(Path(argv[1]).read_bytes())
        keys = [bytes.fromhex(k) for k in pins]
        kernels = [Path(m).read_bytes() for m in modules]
        if cmd.endswith("-projection"):
            result = verify_projection(bundle, require=keys, kernels=kernels)
        else:
            result = verify_attestation(bundle, require=keys, kernels=kernels)
    except (VarsError, ValueError, KeyError, TypeError, OSError) as e:
        print(f"refused: {e}", file=sys.stderr)
        return 2
    if cmd == "inspect-attestation":  # the bundle's own policy is no trust anchor, so its acceptance has its own word
        result["accepted_under_own_policy"] = result.pop("accepted")
    print(json.dumps(result, indent=2, sort_keys=True))
    if cmd == "inspect-projection":
        ok = result["witnessed"] and result["data_ok"] in (True, None) and result["rules_status"] == "known"
    elif cmd == "verify-projection":
        ok = (result["witnessed"] and result["data_ok"] is True and result["rules_status"] == "known"
              and not result["required_missing"])
    elif cmd == "inspect-attestation":
        ok = result["accepted_under_own_policy"]
    else:
        ok = result["accepted"]
    if modules:  # the reader asked for the output to be checked here: the witnesses' word is not enough
        ok = ok and result["kernel"] == "verified_here"
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
