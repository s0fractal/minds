#!/usr/bin/env python3
"""VARS-1 reference implementation (no dependencies beyond `sigma-glyph`'s `sigma_resume`, from PyPI).

Section numbers refer to VARS-1-SPEC.md: objects (§1), standard schemas (§2), store and admission gate (§3),
fold and lens (§4), replay against Book I (§5). The fold and lens Passes 1-2 are decided by `kernel/lens.wasm`;
the Python fold and passes here are its differential twin.
"""
from __future__ import annotations

import json
import re
import struct
import shutil
import subprocess
import tempfile
import sys
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple


# The bundle verifier (§4.4) is its own standalone file: Ed25519, atoms, cells, seals, the standard schemas and the
# projection/attestation checks live there, and this module re-exports them, so there is one implementation.
def _load_minds_verify():
    import importlib.util
    if "minds_verify" in sys.modules:
        return sys.modules["minds_verify"]
    spec = importlib.util.spec_from_file_location("minds_verify", Path(__file__).resolve().parent / "verify" / "minds_verify.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules["minds_verify"] = mod  # registered first: its dataclasses resolve their module by name
    spec.loader.exec_module(mod)
    return mod


_MV = _load_minds_verify()
from minds_verify import (  # noqa: E402
    _B, _D, _I, _L, _Q, _ed_add, _ed_dec, _ed_enc, _ed_mul, _xrecover,
    ed25519_pubkey, ed25519_sign, ed25519_verify, weak_public_key, sha256,
    MAX_INT, MAX_STATE_BYTES, MAX_UTF8_BYTES, MAX_LOSS_BYTES, MAX_HVEC_LEN, MAX_KIN1_BYTES,
    H_I, H_K, H_S, H_FALSE, H_INVALID, H_EMPTY, H_META_SCHEMA, H_ZERO, H_NORMAL_FORM, H_PAUSED, H_BLOCKED_REF,
    H_CYCLE_PROVEN, H_REPLAYED, H_ATTESTED, H_VERDICT_INVALID, H_NOT_ASSESSED, H_PROVISIONAL, H_OWNER, H_LENS_KERNEL,
    VarsError, atom_u64, parse_u64, atom_utf8, parse_utf8, validate_utf8_atom, atom_hvec, parse_hvec, atom_pol1,
    parse_pol1, Cell, Seal, SCHEMA_SPECS, build_standard_schemas, STD_SCHEMAS, STD_SCHEMA_ATOMS, H_SCHEMA,
    KERNEL_BITS, BUNDLE_FORMAT, ATTESTATION_FORMAT, parse_kernel_input, pass3_at_tip, kernel_input_order,
    rules_status, verify_projection, verify_attestation,
)

# ---------------------------------------------------------------------------
# §1 Intrinsic Constants & Hash Helpers
# ---------------------------------------------------------------------------
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



# The rules a scope is evaluated under are a stored object: the compiled rules kernel (`kernel/`, Rust -> wasm32,
# reproducible). A scope names it by hash; this host implements exactly these rules.
KERNEL_DIR = Path(__file__).resolve().parent / "kernel"
KERNEL_ATOM = (KERNEL_DIR / "lens.wasm").read_bytes()
if sha256(KERNEL_ATOM) != H_LENS_KERNEL:
    raise RuntimeError("kernel/lens.wasm does not hash to H_LENS_KERNEL")
# Rules v2 (RULES-V2.md): typed cell references, explicit in the kernel input, with v1b's commit bound (-7), the
# rotation delay of §4.1 latch 4a and the rules-change quarantine of latch 4b in v2 epochs. Dormant: v1 is the
# default, and a scope moves to v2 only by a rotation admitted with a rules-change decision (§4.3). The host keeps
# both modules, so every past tip stays recomputable under the rules of its epoch.
KERNEL2_DIR = Path(__file__).resolve().parent / "kernel2"
H_LENS_KERNEL_V2 = bytes.fromhex("1ca798b5013bf45735d3de836ecff23ca148e5bac2f6ca2c7d6289c2cf26707e")
KERNEL2_ATOM = (KERNEL2_DIR / "lens2.wasm").read_bytes()
if sha256(KERNEL2_ATOM) != H_LENS_KERNEL_V2:
    raise RuntimeError("kernel2/lens2.wasm does not hash to H_LENS_KERNEL_V2")
# v1 with the commit count bounded by the input's length (`kernel/`, built with `--features commit-bound`): the first
# resource hardening (AMENDMENTS.md). Dormant like v2: a scope reaches it only by a rules change (§4.3).
H_LENS_KERNEL_V1B = bytes.fromhex("2a2e440a548b73adbb3072c23e21ee8d9d7bd7867fa7bc3e38150c477f1b11cd")
KERNEL1B_ATOM = (KERNEL_DIR / "lens1b.wasm").read_bytes()
if sha256(KERNEL1B_ATOM) != H_LENS_KERNEL_V1B:
    raise RuntimeError("kernel/lens1b.wasm does not hash to H_LENS_KERNEL_V1B")


@dataclass(frozen=True)
class Rules:
    """A rules module this host implements: its file, the input encoding it reads (`v1`, or `v2` with typed
    references, RULES-V2.md), its resource refusals: the negative codes by which it refuses an input for its
    size, not its meaning (§4.3, a resource hardening), and the commits a rotation that removes keys without their
    consent waits under it before its scope governs (0: at once; §4.1)."""
    path: Path
    encoding: str
    resource_codes: FrozenSet[int] = frozenset()
    rotation_delay: int = 0


RULES: Dict[bytes, Rules] = {
    H_LENS_KERNEL: Rules(KERNEL_DIR / "lens.wasm", "v1"),
    H_LENS_KERNEL_V2: Rules(KERNEL2_DIR / "lens2.wasm", "v2", frozenset({-7}), rotation_delay=16),
    H_LENS_KERNEL_V1B: Rules(KERNEL_DIR / "lens1b.wasm", "v1", frozenset({-7})),
}
RULES_MODULES: Dict[bytes, Path] = {h: r.path for h, r in RULES.items()}
RULES_ATOMS: Dict[bytes, bytes] = {H_LENS_KERNEL: KERNEL_ATOM, H_LENS_KERNEL_V2: KERNEL2_ATOM,
                                   H_LENS_KERNEL_V1B: KERNEL1B_ATOM}
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


if not set(INTRINSIC_ATOMS) <= INTRINSIC_HASHES:
    raise RuntimeError("an intrinsic atom does not hash to an intrinsic id")


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
FIELD_TYPES = {"utf8", "u64", "pol1", "root", "digest", "wasm", "kin1", "cell", "hash"}
VERDICT_CODES = {H_REPLAYED, H_ATTESTED, H_VERDICT_INVALID, H_NOT_ASSESSED}
OPTIONAL_FIELDS = {"required_comp", "expected_outcome", "evaluator_policy", "ckpt_or_witness"}




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
    """Refuse an atom that is not well formed (§1.1); SGS1 states and SigmaNodeV2 nodes are checked with Book I."""
    _MV.validate_atom(raw, extended=_validate_book1_atom)


def _validate_book1_atom(raw: bytes) -> None:
    if raw[:4] == b"SGS1":
        if len(raw) > MAX_STATE_BYTES or len(raw) < 4 + 32 + 33:
            raise VarsError("invalid SGS1 state size")
        sgs1_term_hash(raw)  # the whole state parses
    elif SR.G.deser(raw) is None:
        raise VarsError("invalid SigmaNodeV2 node")


STD_SCHEMA_IDS: Set[bytes] = set(H_SCHEMA.values())
STD_SCHEMA_ATOMS[H_LENS_KERNEL] = KERNEL_ATOM  # every genesis stores the rules object

try:
    import sigma_resume as SR  # noqa: E402  (sigma-glyph from PyPI: requirements.txt)
except ImportError:
    raise RuntimeError("install Book I: python3 -m venv .venv && .venv/bin/pip install --require-hashes "
                       "-r requirements.txt, then run with .venv/bin/python") from None
# Book I as the spec pins it (sigma-glyph c864d3e): the modules' bytes, however they were installed
BOOK_I_SHA256 = {
    "sigma_resume.py": "575a198d47519f56cb8cf75458d5d9754492433f98650d1ddf1f3580a363e858",
    "sigma_glyph.py": "f4d9990d40f07c8cfd3aa10512c2195a0a04e8dc78bc955c0f53dfe737d3feb4",
}
for _mod in (SR, SR.G):
    _p = Path(_mod.__file__)
    if sha256(_p.read_bytes()).hex() != BOOK_I_SHA256[_p.name]:
        raise RuntimeError(f"{_p} is not Book I as VARS-1-SPEC.md pins it (sigma-glyph c864d3e)")


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
    elif typ == "kin1":
        atom(b"KIN1")
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


def check_scope_rules(c: Cell) -> None:
    """§3 check 3: a scope cell names rules this host implements. The fold has no answer of its own for other rules
    (it cannot even look them up), so this check is the refusal that names the reason."""
    if c.h_schema == H_SCHEMA["scope"] and len(c.slots) == 3 and c.slots[2] not in RULES:
        raise VarsError("scope names rules this host does not implement (slots[2] is not in RULES)")


def gate_cycle_witness(c: Cell, atoms: Dict[bytes, bytes]) -> str:
    """§3 check 4 for a `schema.cycle_witness` cell: `1 <= cycle_actions <= cycle_cost`, then `verify_cycle`.
    Returns CYCLE_PROVEN or NOT_ASSESSED (the period or the entry above the host ceiling); anything else is a
    VarsError."""
    actions = parse_u64(atom_of(c.slots[2], atoms, "Check #4 failed: atom for cycle_actions"))
    cost = parse_u64(atom_of(c.slots[3], atoms, "Check #4 failed: atom for cycle_cost"))
    if actions < 1 or cost < actions:
        raise VarsError("CYCLE_WITNESS requires actions >= 1 and cost >= actions")
    # An entry beyond the host ceiling cannot be replayed here: like any transition beyond it (§5), the witness is
    # admitted on structure alone as NOT_ASSESSED, not refused (`verify_cycle` reads it as PREFIX_MISMATCH).
    # proofs/Vars1/Cycle.lean `gateCycle`; it never answers in Pass 3 (`cycle_witness_answers`).
    if u64_of(c.slots[1], atoms) > SR.G.VERIFIER_LIMITS["max_atp"]:
        return "NOT_ASSESSED"
    return verify_cycle_witness_replay(c, atoms, gate_mode=True)


def cycle_witness_answers(cw: Cell, req_comp: bytes, exp_out: bytes, atoms: Dict[bytes, bytes]) -> bool:
    """§4.2 Pass 3: a cycle witness answers a contract or decision with `required_comp = req_comp` and
    `expected_outcome = exp_out` iff it is a witness of that computation, the outcome is `H_CYCLE_PROVEN`, and
    `verify_cycle` proves it (a NOT_ASSESSED witness never answers)."""
    if cw.slots[0] != req_comp or exp_out != H_CYCLE_PROVEN:
        return False
    try:
        return verify_cycle_witness_replay(cw, atoms, gate_mode=False) == "CYCLE_PROVEN"
    except VarsError:
        return False


KERNEL_CODES = {
    -1: "malformed input", -2: "edge not in forward topological order", -3: "out of memory",
    -4: "Pass 2 not monotone", -5: "Pass 2 without fixed point",
    -10: "genesis scope shape", -11: "genesis scope lacks its admission quorum", -12: "local seal context",
    -13: "local seal key", -14: "cross-seal", -15: "unsealed local cell", -16: "evaluator policy not within roster",
    -17: "foreign cell without self-sealed scope", -18: "several new local scopes", -19: "new scope shape",
    -20: "new scope lacks admission quorum", -21: "acceptance not pinned to a self-sealed scope",
    -22: "binding does not reach a prior binding of its name", -23: "unknown policy",
    -6: "reference list differs from the rules' reading", -25: "rotation back to the v1 rules",
    -7: "more commits than input bytes (a resource bound)",
    -24: "a new scope while a rotation waits",
}


class KernelRefusal(VarsError):
    """The rules kernel returned a negative code: the fold refused the commit log (or its input was malformed)."""

    def __init__(self, code: int):
        self.code = code
        super().__init__(f"rules kernel E{code}: {KERNEL_CODES.get(code, 'unknown code')}")


class EvidenceMissing(VarsError):
    """What a rules-change decision names is not in this repository: its replay cannot run here. This is not a
    refutation of the decision; fetch its evidence (`refs/vars/evidence/*`, AMENDMENTS.md) and replay again."""


class TwinDivergence(RuntimeError):
    """The rules kernel and the host's differential twin disagree: a defect in one of them, never a refusal."""


class KernelRunner:
    """Runs a rules module (`kernel/lens.wasm`, or `kernel2/lens2.wasm` for v2) under Node (WebAssembly, no other
    dependency): the rules object of §4.3."""

    def __init__(self, rules: bytes = H_LENS_KERNEL, module: Optional[Path] = None) -> None:
        """`module` runs another build in place of the one `rules` names (a mutant of the kernel, in tests): it is
        never admitted as rules, only compared."""
        self.rules = rules
        self.proc = subprocess.Popen(
            ["node", str(KERNEL_DIR / "run.mjs"), str(module or RULES_MODULES[rules])],
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
        self.proc.stdout.close()
        self.proc.wait(timeout=10)


@dataclass(frozen=True)
class RulesResult:
    """What running rules on an input under a budget of steps gives (§4.3): an `output` (its bytes), a `refusal`
    (its code), `exhausted` (the budget ran out first) or `fault` (the module trapped: a defect, never a verdict).
    Exhaustion is a fact about the budget, not about the input: it is a local result, never a semantic one."""
    kind: str
    output: bytes = b""
    code: int = 0

    def encode(self) -> bytes:
        """`O` + output bytes, `E` + the code as i32 little-endian, `X` or `T`: what a decision's digests hash."""
        if self.kind == "output":
            return b"O" + self.output
        if self.kind == "refusal":
            return b"E" + struct.pack("<i", self.code)
        return {"exhausted": b"X", "fault": b"T"}[self.kind]


MAX_RULES_BUDGET = 1 << 30  # steps a decision may ask the gate to spend on one metered run


class MeteredRunner:
    """Runs a rules module rewritten by `meter.metered` under a budget of steps (kernel/run_metered.mjs)."""

    def __init__(self, rules: bytes) -> None:
        import meter
        self.rules = rules
        self.proc = subprocess.Popen(["node", str(KERNEL_DIR / "run_metered.mjs")],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        self.proc.stdin.write(meter.metered(RULES_MODULES[rules].read_bytes()).hex() + "\n")

    def run(self, kernel_input: bytes, budget: int) -> RulesResult:
        if not 0 <= budget <= MAX_RULES_BUDGET:
            raise VarsError(f"a budget of {budget} steps is outside 0..{MAX_RULES_BUDGET}")
        self.proc.stdin.write(f"{budget} {kernel_input.hex()}\n")
        self.proc.stdin.flush()
        line = self.proc.stdout.readline().strip()
        if not line:
            raise RuntimeError("metered rules kernel produced no output")
        if line == "X":
            return RulesResult("exhausted")
        if line == "T":
            return RulesResult("fault")
        if line.startswith("E"):
            return RulesResult("refusal", code=int(line[1:]))
        return RulesResult("output", output=bytes.fromhex(line))


_KERNELS: Dict[bytes, KernelRunner] = {}
_METERED: Dict[bytes, MeteredRunner] = {}


def metered_runner(rules: bytes) -> MeteredRunner:
    if rules not in _METERED:
        _METERED[rules] = MeteredRunner(rules)
    return _METERED[rules]


def kernel_runner(rules: bytes = H_LENS_KERNEL) -> KernelRunner:
    if rules not in _KERNELS:
        _KERNELS[rules] = KernelRunner(rules)
    return _KERNELS[rules]


def schema_cell_mask(c: "Cell", atoms: Dict[bytes, bytes]) -> int:
    """A schema cell's `cell`-typed descriptors, bit s for slot s (rules v2): host parsing of its UTF8 atoms."""
    mask = 0
    for s, d in enumerate(c.slots):
        raw = atoms.get(d)
        if raw is not None and raw[:4] == b"UTF8" and raw[4:].decode("utf-8", "replace").partition(":")[2] == "cell":
            mask |= 1 << s
    return mask


def commit_rules(scope: str, deltas: List["Delta"]) -> List[bytes]:
    """The rules of each commit's epoch: those named by the scope governing it (fixed at its start, §0). Parsed: the
    genesis scope, then the newest local scope born in an earlier commit (§3 check 1 makes it the governing one, or,
    under rules with a rotation delay, the one waiting to govern, which names the same rules (§4.1 latch 4a)). Under
    those rules a rotation to other rules governs only after their delay, and never if a local cell of its window
    names it (latch 4b: the gate admits such a cell only as a veto). The twin records the rules it folds each commit
    under and refuses any difference from these (TwinDivergence); the kernel recomputes the governing scope. A
    commit log the gate would refuse may get any answer here; the kernel refuses it."""
    out: List[bytes] = []
    cur: Optional[Cell] = None
    waiting: Optional[Tuple[Cell, int]] = None  # a rules change in its window, and the commit that admitted it
    name = b"UTF8" + f"{scope}/SCOPE".encode()
    atoms: Dict[bytes, bytes] = {}
    rules_of = lambda c: c.slots[2] if c is not None and len(c.slots) == 3 else H_LENS_KERNEL  # noqa: E731
    for i, (d_atoms, d_cells, _) in enumerate(deltas):
        atoms.update(d_atoms)
        new = [c for c in d_cells.values() if c.h_schema == H_SCHEMA["scope"] and atoms.get(c.h_slot_name) == name]
        if i == 0 and len(new) == 1:
            cur = new[0]
        out.append(rules_of(cur))
        local = b"UTF8" + f"{scope}/".encode()
        if waiting is not None and any(
                waiting[0].id in (c.h_payload, *c.slots) for c in d_cells.values()
                if atoms.get(c.h_slot_name, b"").startswith(local)):
            waiting = None  # vetoed
        if i > 0 and len(new) == 1:
            delay = RULES[rules_of(cur)].rotation_delay if rules_of(cur) in RULES else 0
            if delay and rules_of(new[0]) != rules_of(cur):
                waiting = (new[0], i)
            else:
                cur = new[0]
        if waiting is not None and i >= waiting[1] + RULES[rules_of(cur)].rotation_delay:
            cur, waiting = waiting[0], None
    return out


def chain_rules(scope: str, deltas: List["Delta"]) -> bytes:
    """The rules that evaluate a commit log: those of its last commit's epoch (RULES-V2.md §4)."""
    return commit_rules(scope, deltas)[-1]


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


def chain_refs(scope: str, deltas: List["Delta"]) -> Tuple[Dict[bytes, List[Tuple[int, bytes]]], Dict[bytes, int], List[bytes]]:
    """Every cell's references, each read by the rules of its birth epoch; with births and per-commit rules."""
    atoms: Dict[bytes, bytes] = {}
    cells: Dict[bytes, Cell] = {}
    birth: Dict[bytes, int] = {}
    for i, (d_atoms, d_cells, _) in enumerate(deltas):
        atoms.update(d_atoms)
        cells.update(d_cells)
        for cid in d_cells:
            birth.setdefault(cid, i)
    rules = commit_rules(scope, deltas)
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
    queue = deque(sorted(u for u, d in indeg.items() if d == 0))
    order: List[bytes] = []
    while queue:
        u = queue.popleft()
        order.append(u)
        for ch in sorted(children_of[u]):
            indeg[ch] -= 1
            if indeg[ch] == 0:
                queue.append(ch)
    if len(order) != len(cells):
        raise VarsError("cell references are cyclic")
    return order, parents_of, children_of


# What one chain commit adds to its parent's tree (the whole tree for the genesis commit): atoms, cells, seals by hash
Delta = Tuple[Dict[bytes, bytes], Dict[bytes, Cell], Dict[bytes, Seal]]


# §4.3 Changing the rules. A rules-change decision is a cell of one of the scope's rules-change schemas, one per class
# of change, each with exactly its fields; their ids are fixed by the scope's name, so the gate recognises a decision
# by schema id. A semantic correction (`<scope>/rules-change/schema`, the first class) carries (a)-(c):
RULES_CHANGE_FIELDS = (
    "old_rules:wasm", "new_rules:wasm",          # the governing scope's rules, and those the rotation names
    "basis:utf8",                                # hex id of the rotation's parent: the chain so far
    "reproduce:digest",                          # (a) over the chain so far
    "counterexample_scope:utf8", "counterexample:utf8",  # (b) a chain this gate admits: its scope and tip commit
    "cell:u64", "status:u64", "right:u64",       # (b) cell index in the new rules' input, status bit, right value
    "refutes:digest",                            # (b)
    "latches:digest",                            # (c) over both logs
)
# A resource hardening or a validation tightening: the new rules refuse an input (a KIN1 atom) on which the old rules
# exhaust the budget or trap (hardening), or give an output (tightening); the chain so far is reproduced byte for byte.
REFUSAL_CHANGE_FIELDS = (
    "old_rules:wasm", "new_rules:wasm", "basis:utf8", "reproduce:digest",
    "input:kin1",                                # the counterexample: an input of both rules (one encoding)
    "budget:u64",                                # steps each rules may take on it (meter.py)
    "refusal:u64",                               # the new rules' refusal code, negated
    "refutes:digest",                            # over both results on the input
)
# An implementation-equivalent change: other bytes, the same output over the chain so far, byte for byte.
EQUIVALENT_CHANGE_FIELDS = ("old_rules:wasm", "new_rules:wasm", "basis:utf8", "reproduce:digest")
RULES_CHANGE_CLASSES: Dict[str, Tuple[str, Tuple[str, ...]]] = {
    "correction": ("rules-change/schema", RULES_CHANGE_FIELDS),
    "hardening": ("rules-change/hardening/schema", REFUSAL_CHANGE_FIELDS),
    "tightening": ("rules-change/tightening/schema", REFUSAL_CHANGE_FIELDS),
    "equivalent": ("rules-change/equivalent/schema", EQUIVALENT_CHANGE_FIELDS),
}


def rules_change_schema(scope: str, kind: str = "correction") -> Tuple[Cell, Dict[bytes, bytes]]:
    """The schema cell whose instances are `scope`'s rules-change decisions of class `kind`, with the atoms it
    names."""
    atoms: Dict[bytes, bytes] = {}

    def put(raw: bytes) -> bytes:
        atoms[sha256(raw)] = raw
        return sha256(raw)

    name, fields = RULES_CHANGE_CLASSES[kind]
    cell = Cell(h_schema=H_META_SCHEMA, h_slot_name=put(atom_utf8(f"{scope}/{name}")), h_payload=H_EMPTY,
                slots=tuple(put(atom_utf8(d)) for d in fields))
    return cell, atoms


def veto_schema(scope: str) -> Tuple[Cell, Dict[bytes, bytes]]:
    """The schema cell of `scope`'s vetoes of a waiting rules change (§4.1 latch 4b), with the atoms it names:
    `change`, the waiting scope, and `cell`, a record the chain had when the change was decided."""
    atoms: Dict[bytes, bytes] = {}

    def put(raw: bytes) -> bytes:
        atoms[sha256(raw)] = raw
        return sha256(raw)

    cell = Cell(h_schema=H_META_SCHEMA, h_slot_name=put(atom_utf8(f"{scope}/veto/schema")), h_payload=H_EMPTY,
                slots=(put(atom_utf8("change:cell")), put(atom_utf8("cell:cell"))))
    return cell, atoms


def rules_change_class(scope: str, schema_id: bytes) -> Optional[str]:
    """The class of change whose decision schema of `scope` has id `schema_id`, if any."""
    for kind in RULES_CHANGE_CLASSES:
        if rules_change_schema(scope, kind)[0].id == schema_id:
            return kind
    return None


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


def atom_kin1(kernel_input: bytes) -> bytes:
    """A KIN1 atom: an input of rules (§4.3), carried as the counterexample of a hardening or a tightening."""
    return b"KIN1" + kernel_input


def kernel_facts(scope: str, deltas: List["Delta"], rules: Optional[bytes] = None) -> Tuple[bytes, List[bytes]]:
    """Encode a commit log as the input of `rules` (§4.3), by default the rules of its last commit's epoch: parsed
    cells, verified seals, POL1 rosters; for v2, schema masks and every cell's references, each read by the rules of
    its birth epoch. v1's encoding reads every payload or slot equal to a cell id as a reference, whatever the epoch.

    `deltas[i]` holds what commit i adds to its parent's tree, so an object's birth is the index of its delta.
    Only parsing happens here: the order of cells, interned origins and keys, and edge lists as cell indices."""
    value_refs, _, epochs = chain_refs(scope, deltas)
    v2 = RULES[epochs[-1] if rules is None else rules].encoding == "v2"
    atoms: Dict[bytes, bytes] = {}
    cells: Dict[bytes, Cell] = {}
    seals: Dict[bytes, Seal] = {}
    birth_c: Dict[bytes, int] = {}
    birth_s: Dict[bytes, int] = {}
    for i, (d_atoms, d_cells, d_seals) in enumerate(deltas):
        atoms.update(d_atoms)
        cells.update(d_cells)
        seals.update(d_seals)
        for cid in d_cells:
            birth_c.setdefault(cid, i)
        for sid in d_seals:
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
    out += struct.pack("<4I", len(deltas), len(order), len(keys), len(pols))
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


def canonical_commit_id(repo_dir: Path | str, name: str) -> bool:
    """`name` is the canonical id of a commit in the repository at `repo_dir`: Git resolves it, as a commit, to
    exactly `name`. Git reads a lowercase hex string of the repository's native object-id length as that object's
    id, never as a ref, and prints ids that way; any other string, a hex one of the other length (SHA-1 versus
    SHA-256) included, may be a ref, an abbreviation or a revision expression, whose meaning can move, and resolves
    to a different string, if at all."""
    got = subprocess.run(["git", "-C", str(repo_dir), "rev-parse", "--verify", "--quiet", "--end-of-options",
                          f"{name}^{{commit}}"], capture_output=True, text=True)
    return got.returncode == 0 and got.stdout.strip() == name


# ---------------------------------------------------------------------------
# §3 Git Plumbing Store & Mandatory 5-Check Admission Gate
# ---------------------------------------------------------------------------
# the signature of an assumed seal (`what_if(assume=True)`): R encodes a point of order 4 and S = 0, so under a key
# that is not weak it verifies only if the challenge is 0 mod L (probability ~2^-252); Seal.decode refuses it
ZERO_SIGNATURE = bytes(64)


class GitVarsRepo:
    def __init__(self, repo_dir: Path | str):
        self.repo_dir = Path(repo_dir)
        self._blob_by_oid: Dict[str, bytes] = {}
        self._oid_by_raw: Dict[bytes, str] = {}
        self._delta_by_commit: Dict[str, Delta] = {}
        self._checked: Dict[Tuple[str, bytes], object] = {}
        self._fold_memo: Dict[Tuple[str, str], Dict[str, object]] = {}
        self._gate_checked: Set[Tuple[str, str]] = set()  # (scope, commit): every gate check passed for that chain
        self._commit_ids: Set[str] = set()  # names checked to be canonical commit ids (an id never changes meaning)
        # seal ids taken as signed without checking: only ever set on a throwaway instance `what_if` makes for an
        # assumed hypothesis, whose seals carry a zero signature no real check accepts
        self._assumed: frozenset = frozenset()

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
        """The commits from genesis to `tip_commit`, oldest first. A chain is one line of single-parent commits (the
        gate's Check #1), so a history with a merge or a second root is refused rather than linearized."""
        if not self.is_commit_id(tip_commit):
            raise VarsError(f"{tip_commit[:80]!r} is not the full commit id of a commit in this repository")
        chain: List[str] = []
        for line in self._git("rev-list", "--reverse", "--parents", tip_commit).decode().splitlines():
            commit, *parents = line.split()
            if parents != chain[-1:]:
                raise VarsError(f"commit {commit[:12]} does not continue a single-parent chain")
            chain.append(commit)
        return chain

    # Reading the store. A commit's tree is its parent's tree plus what the commit adds (the gate refuses anything
    # else, Check #2), so the host reads each commit once, as the delta `git diff-tree` reports, and never re-reads
    # history. Two caches make that hold across calls, both keyed by content and filled only after the checks pass:
    # `_delta_by_commit` (a commit id names its tree and its parent) and `_checked` (an object's SHA-256 names its
    # bytes, so decoding and the seal signature check are done once per object). Bytes not yet seen are always read
    # from Git, hashed against their path and checked: a cache never stands in for new bytes.
    _CAS_PATH = re.compile(r"^cas/(atoms|cells|seals)/([0-9a-f]{2})/([0-9a-f]{62})$")

    def _checked_object(self, kind: str, h: bytes, raw: bytes, path: str) -> object:
        if sha256(raw) != h:
            raise VarsError(f"CAS SHA-256 mismatch at {path}")
        if kind == "seals" and h in self._assumed:  # structure only, never cached
            if len(raw) != 164 or raw[:4] != b"SEAL" or weak_public_key(raw[68:100]):
                raise VarsError("an assumed seal is SEAL, target, context and a key that is not weak")
            return Seal(h_target=raw[4:36], h_scope_ctx=raw[36:68], actor_pubkey=raw[68:100], signature=raw[100:])
        hit = self._checked.get((kind, h))
        if hit is not None:
            return hit
        if kind == "atoms":
            validate_atom(raw)
            obj: object = raw
        elif kind == "cells":
            obj = Cell.decode(raw)
        else:
            obj = Seal.decode(raw)
        self._checked[(kind, h)] = obj
        return obj

    def _read_blobs(self, oids: List[str]) -> None:
        """Read the blobs not yet held, with one `git cat-file --batch`; a missing object is a refusal."""
        want = [o for o in dict.fromkeys(oids) if o not in self._blob_by_oid]
        if not want:
            return
        out = self._git("cat-file", "--batch", input_bytes=("\n".join(want) + "\n").encode())
        at = 0
        for oid in want:
            nl = out.index(b"\n", at)
            header = out[at:nl].decode().split()
            if len(header) != 3 or header[0] != oid or header[1] != "blob":
                raise VarsError(f"git object {oid} is missing or not a blob ({' '.join(header[1:])})")
            size = int(header[2])
            raw = out[nl + 1:nl + 1 + size]
            if len(raw) != size or out[nl + 1 + size:nl + 2 + size] != b"\n":
                raise VarsError(f"git cat-file returned a short object {oid}")
            at = nl + 2 + size
            self._blob_by_oid[oid] = raw
            self._oid_by_raw[raw] = oid

    def _load_deltas(self, commits: List[str]) -> None:
        """Fill `_delta_by_commit` for `commits` (consecutive chain commits) with one `git diff-tree --stdin`."""
        missing = [c for c in commits if c not in self._delta_by_commit]
        if not missing:
            return
        out = self._git("diff-tree", "--stdin", "-r", "--root", "--always", "--no-renames", "--no-abbrev",
                        input_bytes=("\n".join(missing) + "\n").encode()).decode()
        entries: Dict[str, List[Tuple[str, bytes, str, str]]] = {}
        cur: Optional[List[Tuple[str, bytes, str, str]]] = None
        for line in out.splitlines():
            if not line:
                continue
            if not line.startswith(":"):
                cur = entries.setdefault(line.split()[0], [])
                continue
            if cur is None:
                raise VarsError("git diff-tree output without a commit")
            meta, path = line.split("\t", 1)
            _src_mode, mode, _src_oid, oid, status = meta[1:].split()
            if status != "A":
                raise VarsError(f"non-A tree change {status} at {path}: a chain commit only adds objects")
            if mode != "100644":
                raise VarsError(f"non-100644 mode {mode} at {path}")
            m = self._CAS_PATH.match(path)
            if not m:
                raise VarsError(f"invalid cas path: {path}")
            kind, aa, bb = m.groups()
            cur.append((kind, bytes.fromhex(aa + bb), oid, path))
        if set(entries) != set(missing):
            raise VarsError("git diff-tree did not report every chain commit")
        self._read_blobs([oid for es in entries.values() for _, _, oid, _ in es])
        for commit in missing:
            delta: Delta = ({}, {}, {})
            for kind, h, oid, path in entries[commit]:
                obj = self._checked_object(kind, h, self._blob_by_oid[oid], path)
                delta[("atoms", "cells", "seals").index(kind)][h] = obj
            self._delta_by_commit[commit] = delta

    def read_commit_delta(self, commit_oid: str) -> Delta:
        """What `commit_oid` adds to its parent's tree (all of it for a genesis commit), every object checked."""
        self._load_deltas([commit_oid])
        return self._delta_by_commit[commit_oid]

    def chain_deltas(self, commits: List[str]) -> List[Delta]:
        self._load_deltas(commits)
        return [self.read_commit_delta(c) for c in commits]

    def read_cas_tree(self, commit_oid: str) -> Tuple[Dict[bytes, bytes], Dict[bytes, Cell], Dict[bytes, Seal]]:
        """The whole CAS of `commit_oid`, each kind ordered by hash (as the tree lists it)."""
        atoms: Dict[bytes, bytes] = {}
        cells: Dict[bytes, Cell] = {}
        seals: Dict[bytes, Seal] = {}
        for d_atoms, d_cells, d_seals in self.chain_deltas(self.commit_chain(commit_oid)):
            atoms.update(d_atoms)
            cells.update(d_cells)
            seals.update(d_seals)
        return dict(sorted(atoms.items())), dict(sorted(cells.items())), dict(sorted(seals.items()))

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
        evidence = self._check_commit(scope, candidate_commit, expected_old)
        self._gate_checked.add((scope, candidate_commit))

        # Atomic compare-and-swap of the scope's ref, in one transaction with the evidence refs of a rules change
        # (§4.3): its counterexample stays reachable from refs/vars/* wherever the chain goes
        lines = [f"update refs/vars/heads/{scope} {candidate_commit} {expected_old or '0' * self.oid_hex_len()}"]
        lines += [f"update {ref} {commit}" for ref, commit in evidence]
        self._git("update-ref", "--stdin", input_bytes=("\n".join(lines) + "\n").encode())

    def is_commit_id(self, name: str) -> bool:
        """`name` is the canonical id of a commit in this repository (`canonical_commit_id`)."""
        if name in self._commit_ids:
            return True
        ok = canonical_commit_id(self.repo_dir, name)
        if ok:
            self._commit_ids.add(name)
        return ok

    def check_chain(self, scope: str, tip: str) -> None:
        """Every commit from genesis to `tip` passes the gate's checks for `scope`, as at its admission; no ref moves.
        A rules-change decision's counterexample must be such a chain (§4.3)."""
        parent: Optional[str] = None
        for commit in self.commit_chain(tip):
            if (scope, commit) not in self._gate_checked:
                try:
                    self._check_commit(scope, commit, parent)
                except VarsError:
                    raise
                except (KeyError, IndexError, TypeError, ValueError, UnicodeDecodeError) as e:
                    raise VarsError(f"malformed commit refused ({type(e).__name__}: {e})") from None
                self._gate_checked.add((scope, commit))
            parent = commit

    def _check_commit(self, scope: str, candidate_commit: str, expected_old: Optional[str]) -> List[Tuple[str, str]]:
        """Checks #1-#7 and the fold for `candidate_commit` on top of `expected_old` (§3); nothing is written.
        Both are read through `commit_chain`, which takes canonical commit ids only. Returns the evidence refs a
        rules change asks to be written with it (§4.3)."""
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
            check_scope_rules(c)
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
                gate_cycle_witness(c, atoms)
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
        prior_deltas = self.chain_deltas(prior_chain)
        prior_cells = {cid: c for _, d_cells, _ in prior_deltas for cid, c in d_cells.items()}
        prior = set(prior_cells)
        # References never point forward in time (§4.3): v1 rules read any payload or slot equal to a cell id as a
        # reference, so a new cell may not have an id that an older cell born in a v1 epoch names there. A cell born
        # under v2 rules reads references by type (RULES-V2.md): its opaque values veto nothing.
        prior_rules = commit_rules(scope, prior_deltas) if prior_deltas else []
        named_before = {x for i, (_, d_cells, _) in enumerate(prior_deltas) if RULES[prior_rules[i]].encoding == "v1"
                        for pc in d_cells.values() for x in (pc.h_payload, *pc.slots)}
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
            if c.slots[1] != chain_rules(scope, prior_deltas[:prior_chain.index(tip) + 1]):
                raise VarsError("projection names other rules than those of its tip's epoch")
            h_in, h_state = self.projection_digests(scope, tip)
            if (c.slots[2], c.slots[3]) != (h_in, h_state):
                raise VarsError("projection digests differ from the gate's recomputation of the rules at its tip")

        # Run the commit-chain fold to verify admission authority on the new commit
        self._evaluate_commit_chain(scope, self.commit_chain(candidate_commit))

        # A rules change in its window (§4.1 latch 4b): both rules read every commit, and a veto carries its evidence
        self._check_rules_window(scope, expected_old, prior_chain, candidate_commit, cells, atoms, prior)

        # Changing the rules (§4.3): only by a rotation admitted with a decision whose computations replay
        return self._check_rules_change(scope, expected_old, prior_chain, cells, atoms, seals, prior, candidate_commit)

    def _check_rules_window(self, scope: str, expected_old: Optional[str], prior_chain: List[str], candidate: str,
                            cells: Dict[bytes, Cell], atoms: Dict[bytes, bytes], prior: Set[bytes]) -> None:
        """§4.1 latch 4b at the gate. While a rules change waits, a commit is admitted only if the waiting rules'
        kernel also accepts the chain with it (at the window's last commit this is the replay of the exact tip they
        take over), and a cell that names the waiting scope only as a veto with its evidence: of the veto schema, its
        `change` the waiting scope and its `cell` a cell born at or before the rotation, to which the old and the new
        rules, each over the chain up to and including the veto's own commit, give different status or Authorized
        bits. A veto says that the change already alters what this chain says about a record it had; read at its own
        commit, a difference that first appears in the window's last commit can still be vetoed there (Codex PR #20
        r1)."""
        if expected_old is None:
            return
        fold = self._evaluate_commit_chain(scope, prior_chain)
        if not fold["waiting"] or not fold["waiting"][2]:
            return
        w_id, w_at, _ = fold["waiting"]
        old_rules, new_rules = cells[fold["active_scope_id"]].slots[2], cells[w_id].slots[2]
        try:
            candidate_deltas = self.chain_deltas(self.commit_chain(candidate))
            kernel_runner(new_rules).run(kernel_facts(scope, candidate_deltas, new_rules)[0])
        except KernelRefusal as e:
            raise VarsError(f"a commit in a rules change's window must be read by the new rules too: {e}") from None
        vschema = veto_schema(scope)[0].id
        born = {cid: i for i, (_, d_cells, _) in enumerate(self.chain_deltas(prior_chain)) for cid in d_cells}
        for cid in sorted(set(cells) - prior):
            c = cells[cid]
            if w_id not in (c.h_payload, *c.slots):
                continue
            if c.h_schema != vschema or len(c.slots) != 2 or c.slots[0] != w_id:
                raise VarsError("a cell that names a waiting rules change is a veto, of the veto schema "
                                "(§4.1 latch 4b)")
            target = c.slots[1]
            if born.get(target, w_at + 1) > w_at:
                raise VarsError("a veto's cell is a record the chain had when the change was decided")
            reads = []
            for rules in (old_rules, new_rules):
                out, reading = self.rules_output(scope, candidate, rules)
                order, n = reading["order"], len(reading["order"])
                i = order.index(target)
                reads.append((out[4 + i], out[4 + n + i]))
            if reads[0] == reads[1]:
                raise VarsError("a veto shows no difference on this chain: both rules give its cell the same bits "
                                "at the veto's commit")

    def _check_rules_change(self, scope: str, expected_old: Optional[str], prior_chain: List[str],
                            cells: Dict[bytes, Cell], atoms: Dict[bytes, bytes], seals: Dict[bytes, Seal],
                            prior: Set[bytes], candidate: str) -> List[Tuple[str, str]]:
        """A rotation whose new scope names other rules than the governing scope is admitted only with exactly one
        rules-change decision in its commit, of one class (§4.3), endorsed by the governing admission quorum, whose
        computations the gate replays here for its class; and the new rules must still decide every earlier rules
        change's counterexample as that change established (d). Returns the evidence refs to write with the
        rotation: `(refs/vars/evidence/<scope>/<decision id>, counterexample commit)` for a counterexample chain."""
        new = set(cells) - prior
        decisions = sorted(cid for cid in new if rules_change_class(scope, cells[cid].h_schema) is not None)
        origin = lambda c: parse_utf8(atoms[c.h_slot_name]).split("/", 1)[0]  # noqa: E731
        rotation = [cells[cid] for cid in new if cells[cid].h_schema == H_SCHEMA["scope"] and origin(cells[cid]) == scope]
        base = None
        if expected_old is not None and rotation:
            base = cells[self._evaluate_commit_chain(scope, prior_chain)["active_scope_id"]]
        if base is None or rotation[0].slots[2] == base.slots[2]:
            if decisions:
                raise VarsError("a rules-change decision comes only with the rotation to the rules it names")
            return []
        if len(decisions) != 1:
            raise VarsError("a rotation to other rules needs exactly one rules-change decision in its commit (§4.3)")
        d = cells[decisions[0]]
        kind = rules_change_class(scope, d.h_schema)
        old, new_rules = base.slots[2], rotation[0].slots[2]
        if RULES[old].encoding == "v2" and RULES[new_rules].encoding == "v1":
            raise VarsError("rules that read references as v1 does cannot read a v2 epoch: no rotation goes there")
        if RULES[new_rules].encoding == "v2" and any(
                RULES[r].encoding == "v1" and r != H_LENS_KERNEL
                for r in {old, *commit_rules(scope, self.chain_deltas(prior_chain))}):
            # Codex review r1 F1: v2 reads a cell as v1 does only if it was born under H_LENS_KERNEL itself
            raise VarsError("v2 reads as v1 only the cells born under H_LENS_KERNEL: a chain with an epoch of other "
                            "rules that read as v1 does cannot rotate to v2")
        # the new rules fold the whole chain once they govern, the rotation commit included: they read it now, or no
        # later commit could be admitted (Codex PR #20 r1: a rotation carrying a cell its new rules refuse froze the
        # chain, the window's check refusing every commit after it)
        try:
            kernel_runner(new_rules).run(kernel_facts(scope, self.chain_deltas(self.commit_chain(candidate)),
                                                      new_rules)[0])
        except KernelRefusal as e:
            raise VarsError(f"the new rules must read the commit that rotates to them: {e}") from None
        f = dict(zip((x.split(":")[0] for x in RULES_CHANGE_CLASSES[kind][1]), d.slots))
        if (f["old_rules"], f["new_rules"]) != (old, new_rules):
            raise VarsError("the rules-change decision names other rules than those the rotation changes")
        if parse_utf8(atoms[f["basis"]]) != expected_old:
            raise VarsError("the rules-change decision's basis is not the chain so far (the rotation's parent)")
        thr, hv = parse_pol1(atoms[base.slots[0]])
        pks = set(parse_hvec(atoms[hv], require_sorted=True))
        endorsers = {s.actor_pubkey for s in seals.values()
                     if s.h_target == d.id and s.h_scope_ctx == base.id and s.actor_pubkey in pks}
        if len(endorsers) < thr:
            raise VarsError("the rules-change decision lacks the governing scope's admission quorum")
        refs: List[Tuple[str, str]] = []
        if kind == "correction":
            refs = self._check_correction(scope, expected_old, old, new_rules, f, atoms, d.id)
        else:
            if RULES[old].encoding != RULES[new_rules].encoding:
                raise VarsError(f"{'an' if kind == 'equivalent' else 'a'} {kind} change keeps the input encoding: its "
                                "evidence is one input of both rules")
            ev = self.rules_change_basis(scope, expected_old, old, new_rules)
            if f["reproduce"] != ev["reproduce"]:
                raise VarsError(f"rules change ({kind}): the decision's reproduce digest differs from the gate's replay")
            if ev["old"] != ev["new"]:
                raise VarsError(f"rules change ({kind}): the new rules do not give the old rules' output over the "
                                "chain so far, byte for byte")
            if kind != "equivalent":
                self._check_refusal(kind, old, new_rules, f, atoms)
        self._check_earlier_changes(scope, prior_chain, new_rules, d.id)
        return refs

    def _check_correction(self, scope: str, basis: str, old: bytes, new_rules: bytes, f: Dict[str, bytes],
                          atoms: Dict[bytes, bytes], decision: bytes) -> List[Tuple[str, str]]:
        """(a)-(c) of a semantic correction (§4.3)."""
        cx_scope, cx_tip = parse_utf8(atoms[f["counterexample_scope"]]), parse_utf8(atoms[f["counterexample"]])
        # the signed field pins the counterexample: a ref, an abbreviation or a revision expression would let its
        # meaning move after admission, so a later replay could disagree with the gate that admitted it
        self.require_evidence_commit(cx_tip, "the rules-change decision's counterexample")
        self.check_chain(cx_scope, cx_tip)
        ev = self.rules_change_evidence(scope, basis, old, new_rules, cx_scope, cx_tip)

        # (a) every status of the chain so far, and its governing scope, reproduced
        if f["reproduce"] != ev["reproduce"]:
            raise VarsError("rules change (a): the decision's reproduce digest differs from the gate's replay")
        o, n = ev["basis"]
        if o["scope"] != n["scope"] or o["status"] != n["status"]:
            raise VarsError("rules change (a): the new rules do not reproduce every status the old rules give")
        # (b) a counterexample: the new rules give the verdict the decision names right, the old rules another
        if f["refutes"] != ev["refutes"]:
            raise VarsError("rules change (b): the decision's refutes digest differs from the gate's replay")
        o, n = ev["counterexample"]
        i, bit, right = (u64_of(f[k], atoms) for k in ("cell", "status", "right"))
        if i >= len(n["order"]) or bit >= len(KERNEL_BITS) or right > 1:
            raise VarsError("rules change (b): the decision names no status of the counterexample")
        cid = n["order"][i]
        if (n["status"][cid] >> bit & 1) != right:
            raise VarsError("rules change (b): the new rules do not give the verdict the decision names right")
        if (o["status"][cid] >> bit & 1) == right:
            raise VarsError("rules change (b): the old rules give that verdict too, so it is no counterexample")
        # (c) latches only grow: no Authorized cell or authorized edge of the old rules is lost, on either log
        if f["latches"] != ev["latches"]:
            raise VarsError("rules change (c): the decision's latches digest differs from the gate's replay")
        for o, n in (ev["basis"], ev["counterexample"]):
            if any(v and not n["auth"][k] for k, v in o["auth"].items()) or \
                    any(v and not n["edges"][k] for k, v in o["edges"].items()):
                raise VarsError("rules change (c): a latch the old rules set is lost under the new rules")
        need = [(cx_scope, cx_tip)] + self.evidence_closure(cx_scope, cx_tip)
        return [(f"refs/vars/evidence/{scope}/{decision.hex()}/{c}", c) for _, c in need]

    def evidence_closure(self, scope: str, tip: str) -> List[Tuple[str, str]]:
        """Every counterexample `(scope, commit)` that replaying the chain up to `tip` needs, transitively: each
        correction on it names one, whose own chain may carry corrections in turn (Codex review r1 F2)."""
        out: List[Tuple[str, str]] = []
        todo = [(scope, tip)]
        while todo:
            sc, t = todo.pop()
            atoms: Dict[bytes, bytes] = {}
            for d_atoms, d_cells, _ in self.chain_deltas(self.commit_chain(t)):
                atoms.update(d_atoms)
                for cid in sorted(d_cells):
                    if rules_change_class(sc, d_cells[cid].h_schema) != "correction":
                        continue
                    f = dict(zip((x.split(":")[0] for x in RULES_CHANGE_FIELDS), d_cells[cid].slots))
                    item = (parse_utf8(atoms[f["counterexample_scope"]]), parse_utf8(atoms[f["counterexample"]]))
                    if item not in out:
                        self.require_evidence_commit(item[1], "a counterexample the counterexample's chain names")
                        out.append(item)
                        todo.append(item)
        return out

    def _check_refusal(self, kind: str, old: bytes, new_rules: bytes, f: Dict[str, bytes],
                       atoms: Dict[bytes, bytes]) -> None:
        """A resource hardening or a validation tightening (§4.3): on the decision's input, under its budget of
        steps, the new rules refuse with the code it names, a resource refusal of theirs for a hardening and any other
        for a tightening; the old rules exhaust the budget or trap (hardening), or give an output (tightening)."""
        budget, code = u64_of(f["budget"], atoms, "budget"), -u64_of(f["refusal"], atoms, "refusal")
        ev = self.rules_change_refusal(old, new_rules, atom_of(f["input"], atoms, "input")[4:], budget)
        if f["refutes"] != ev["refutes"]:
            raise VarsError(f"rules change ({kind}): the decision's refutes digest differs from the gate's replay")
        o, n = ev["old"], ev["new"]
        if n != RulesResult("refusal", code=code):
            raise VarsError(f"rules change ({kind}): the new rules do not refuse the input with E{code} within the "
                            f"budget (they give {n.kind}{' E' + str(n.code) if n.kind == 'refusal' else ''})")
        resource = code in RULES[new_rules].resource_codes
        if kind == "hardening":
            if not resource:
                raise VarsError(f"rules change (hardening): E{code} is not a resource refusal of the new rules")
            if o.kind not in ("exhausted", "fault"):
                raise VarsError(f"rules change (hardening): the old rules give {o.kind} within the budget, so there "
                                "is nothing to harden")
        else:
            if resource:
                raise VarsError(f"rules change (tightening): E{code} is a resource refusal: that is a hardening")
            if o.kind != "output":
                raise VarsError(f"rules change (tightening): the old rules give {o.kind}, not an output, so the new "
                                "refusal tightens nothing")

    def _check_earlier_changes(self, scope: str, prior_chain: List[str], new_rules: bytes, decision: bytes) -> None:
        """(d) Every earlier rules change of this chain is kept: its counterexample gets, under the new rules, the
        result that change established for the rules it introduced. A correction: the named status of the named cell
        (by id) is still right. A hardening or a tightening: the input is still refused with the same code within
        its budget. An implementation-equivalent change has no counterexample."""
        atoms: Dict[bytes, bytes] = {}
        for d_atoms, d_cells, _ in self.chain_deltas(prior_chain):
            atoms.update(d_atoms)
            for cid in sorted(d_cells):
                kind = rules_change_class(scope, d_cells[cid].h_schema)
                if kind is None or kind == "equivalent":
                    continue
                f = dict(zip((x.split(":")[0] for x in RULES_CHANGE_CLASSES[kind][1]), d_cells[cid].slots))
                then = f["new_rules"]
                what = f"(d): the earlier rules change {cid.hex()[:12]}"
                if kind == "correction":
                    cx_scope, cx_tip = parse_utf8(atoms[f["counterexample_scope"]]), parse_utf8(atoms[f["counterexample"]])
                    self.require_evidence_commit(cx_tip, f"{what}: its counterexample")
                    cell = self.rules_output(cx_scope, cx_tip, then)[1]["order"][u64_of(f["cell"], atoms)]
                    bit, right = u64_of(f["status"], atoms), u64_of(f["right"], atoms)
                    try:
                        status = self.rules_output(cx_scope, cx_tip, new_rules)[1]["status"].get(cell)
                    except VarsError as e:
                        raise VarsError(f"{what}: the new rules over its counterexample: {e}") from None
                    if status is None or (status >> bit & 1) != right:
                        raise VarsError(f"{what} is undone: the new rules no longer give its counterexample's verdict")
                else:
                    if RULES[then].encoding != RULES[new_rules].encoding:
                        raise VarsError(f"{what}: its input is encoded for other rules than the new rules read")
                    code = -u64_of(f["refusal"], atoms)
                    got = metered_runner(new_rules).run(atoms[f["input"]][4:], u64_of(f["budget"], atoms))
                    if got != RulesResult("refusal", code=code):
                        raise VarsError(f"{what} is undone: the new rules no longer refuse its input with E{code}")

    def require_evidence_commit(self, name: str, what: str) -> None:
        """`name` is the canonical id of a commit whose whole history is in this repository. A string that has the
        form of a commit id of this repository's object format but whose history is not here is missing evidence
        (`EvidenceMissing`), not a refusal of what names it; any other string is refused."""
        if self.is_commit_id(name):
            got = subprocess.run(["git", "-C", str(self.repo_dir), "rev-list", "--objects", "--quiet", name],
                                 capture_output=True)
            if got.returncode == 0 and not self._cut_by_shallow(name):
                return
        elif not re.fullmatch(f"[0-9a-f]{{{self.oid_hex_len()}}}", name) or subprocess.run(
                ["git", "-C", str(self.repo_dir), "cat-file", "-e", name], capture_output=True).returncode == 0:
            raise VarsError(f"{what} is not a full commit id")  # not an id, or the id of another object
        raise EvidenceMissing(f"{what} {name} is not in this repository with its history: fetch refs/vars/evidence/*")

    def _cut_by_shallow(self, commit: str) -> bool:
        """A shallow clone cuts the history of `commit`: some commit of it is a shallow boundary, whose parents Git
        pretends away. Such a history would replay as a different chain."""
        path = Path(self._git("rev-parse", "--git-path", "shallow").decode().strip())
        path = path if path.is_absolute() else self.repo_dir / path
        if not path.exists():
            return False
        cut = set(path.read_text().split())
        return any(c in cut for c in self._git("rev-list", commit).decode().split())

    def oid_hex_len(self) -> int:
        fmt = self._git("rev-parse", "--show-object-format").decode().strip()
        return 64 if fmt == "sha256" else 40

    def rules_output(self, scope: str, tip: str, rules: bytes) -> Tuple[bytes, Dict[str, object]]:
        """The output of `rules` over the scope's chain up to `tip`, encoded for those rules, and its reading by cell
        id: governing scope, status and Authorized bytes, and edge latches keyed `(w, v, kind)`."""
        deltas = self.chain_deltas(self.commit_chain(tip))
        kernel_input, order = kernel_facts(scope, deltas, rules)
        out = kernel_runner(rules).run(kernel_input)
        cells = {cid: c for _, d_cells, _ in deltas for cid, c in d_cells.items()}
        atoms = {h: raw for d_atoms, _, _ in deltas for h, raw in d_atoms.items()}
        n = len(order)
        flags = iter(out[4 + 2 * n:])
        edges = {}
        for wid in order:
            w = cells[wid]
            for kind, mh in (("invalidates", w.h_invalidates), ("retires", w.h_retires), ("supersedes", w.h_supersedes)):
                for vid in [] if mh == H_EMPTY else parse_hvec(atoms[mh], require_sorted=True):
                    edges[(wid, vid, kind)] = next(flags)
        return out, {"order": order, "scope": order[int.from_bytes(out[:4], "little")],
                     "status": {cid: out[4 + i] for i, cid in enumerate(order)},
                     "auth": {cid: out[4 + n + i] for i, cid in enumerate(order)}, "edges": edges}

    def rules_change_basis(self, scope: str, basis: str, old: bytes, new: bytes) -> Dict[str, object]:
        """The old and the new rules' outputs over the chain up to `basis` and the digest a hardening, tightening or
        equivalent change carries for them: `reproduce` = SHA-256(SHA-256(old output) ‖ SHA-256(new output))."""
        outs = []
        for rules, what in ((old, "the old rules"), (new, "the new rules")):
            try:
                outs.append(self.rules_output(scope, basis, rules)[0])
            except VarsError as e:
                raise VarsError(f"rules change: {what} over the chain so far: {e}") from None
        return {"reproduce": sha256(sha256(outs[0]) + sha256(outs[1])), "old": outs[0], "new": outs[1]}

    def rules_change_refusal(self, old: bytes, new: bytes, kernel_input: bytes, budget: int) -> Dict[str, object]:
        """Both rules on `kernel_input` under `budget` steps (meter.py), and the digest a hardening or tightening
        carries: `refutes` = SHA-256(SHA-256(old result) ‖ SHA-256(new result)), results as `RulesResult.encode`."""
        o, n = metered_runner(old).run(kernel_input, budget), metered_runner(new).run(kernel_input, budget)
        return {"old": o, "new": n, "refutes": sha256(sha256(o.encode()) + sha256(n.encode()))}

    def rules_change_evidence(self, scope: str, basis: str, old: bytes, new: bytes, cx_scope: str,
                              cx_tip: str) -> Dict[str, object]:
        """The computations of a rules-change decision (§4.3): the old and the new rules over the chain up to `basis`
        and over the counterexample chain, and the digests a decision carries for them: each is SHA-256 over the
        SHA-256 of every output its check reads, in the order (old basis, new basis, old counterexample, new
        counterexample). Either rules refusing either log is a refusal of the decision."""
        outs, reads = [], []
        for sc, tip, rules, what in ((scope, basis, old, "the old rules over the chain so far"),
                                     (scope, basis, new, "the new rules over the chain so far"),
                                     (cx_scope, cx_tip, old, "the old rules over the counterexample"),
                                     (cx_scope, cx_tip, new, "the new rules over the counterexample")):
            try:
                out, read = self.rules_output(sc, tip, rules)
            except VarsError as e:
                raise VarsError(f"rules change: {what}: {e}") from None
            outs.append(sha256(out))
            reads.append(read)
        digest = lambda *ix: sha256(b"".join(outs[i] for i in ix))  # noqa: E731
        return {"reproduce": digest(0, 1), "refutes": digest(2, 3), "latches": digest(0, 1, 2, 3),
                "basis": (reads[0], reads[1]), "counterexample": (reads[2], reads[3])}

    # -----------------------------------------------------------------------
    # §4 Commit-Chain Fold & Three-Pass Lensing
    # -----------------------------------------------------------------------
    def projection_digests(self, scope: str, tip: str) -> Tuple[bytes, bytes]:
        """`(sha256(kernel input), sha256(kernel output))` for the scope's chain up to and including `tip`: the
        `input` and `state` a projection at `tip` must carry. Anyone holding the chain can recompute them."""
        deltas = self.chain_deltas(self.commit_chain(tip))
        kernel_input, _ = kernel_facts(scope, deltas)
        return sha256(kernel_input), sha256(kernel_runner(chain_rules(scope, deltas)).run(kernel_input))

    def _evaluate_commit_chain(self, scope: str, commits: List[str]) -> Dict[str, object]:
        """§4.1 fold. The rules kernel decides authority; `_fold_twin` recomputes it in Python and must agree.

        The result for a chain is memoized by its tip commit (which names the whole chain): callers must not mutate
        it. Only a fold that both the kernel and its twin admitted is kept."""
        key = (scope, commits[-1]) if commits else None
        hit = self._fold_memo.get(key) if key else None
        if hit is not None:
            return hit
        deltas = self.chain_deltas(commits)
        try:
            twin, twin_err = self._fold_twin(scope, deltas), None
        except VarsError as e:
            twin, twin_err = None, e
        kernel_input, order = kernel_facts(scope, deltas)
        value_refs, _, rules = chain_refs(scope, deltas)
        if twin_err is None and twin["governing_rules"] != rules:
            raise TwinDivergence("the rules of a commit's epoch: the twin's fold and commit_rules disagree")
        if twin_err is None and -7 in RULES[rules[-1]].resource_codes and len(deltas) > len(kernel_input):
            # the twin of a resource bound (H_LENS_KERNEL_V1B): more commits than input bytes
            twin, twin_err = None, VarsError("the commit log has more commits than its rules input has bytes")
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
        result = {
            **twin,
            **kernel,
            "kernel_input": kernel_input,
            "kernel_order": order,
            "rules": rules[-1],
            "value_refs": value_refs,
            "kernel_status": {cid: {name: bool(status[i] >> b & 1) for b, name in enumerate(KERNEL_BITS)}
                              for i, cid in enumerate(order)},
        }
        if key:
            while len(self._fold_memo) >= 4:
                self._fold_memo.pop(next(iter(self._fold_memo)))
            self._fold_memo[key] = result
        return result

    def _fold_twin(self, scope: str, deltas: List[Delta]) -> Dict[str, object]:
        """The host's differential twin of the kernel fold (§4.1), plus the endorser sets Pass 3 needs.

        It reads each commit's delta once and keeps indexes (seals by target, cells by origin and name, the edges
        and latches still open), so a commit costs what it adds and what its new seals touch, not the history
        before it. Every quantity the per-commit rules read is either fixed at an object's birth (contents, birth
        signers) or changes only through a new seal on that cell or a change of S_base; the open latches are
        re-read on exactly those events, which is when the full recount could change its answer."""
        latched_scope_auth: Set[bytes] = set()
        latched_acc_auth: Set[bytes] = set()
        latched_schema_auth: Set[bytes] = set(STD_SCHEMA_IDS)
        latched_edge_auth: Set[Tuple[bytes, bytes, str]] = set()
        initial_endorsers: Dict[bytes, Set[bytes]] = {}
        cumulative_endorsers: Dict[bytes, Set[bytes]] = {}
        foreign_endorsers_by_scope: Dict[Tuple[bytes, bytes], Set[bytes]] = {}
        self_sealed_foreign_scopes: Set[bytes] = set()
        active_scope_id: Optional[bytes] = None

        atoms: Dict[bytes, bytes] = {}
        cells: Dict[bytes, Cell] = {}
        seals: Dict[bytes, Seal] = {}
        seals_on: Dict[bytes, List[Seal]] = {}  # target cell -> its seals
        foreign_scope_ids: List[bytes] = []  # foreign schema.scope cells not (yet) self-sealed
        # Self-sealed foreign scopes by origin. Sticky: seals are append-only, so a scope stays self-sealed.
        valid_foreign_scopes: Dict[str, List[Tuple[bytes, Set[bytes]]]] = {}
        foreign_by_origin: Dict[str, List[bytes]] = {}  # non-standard foreign cells by origin
        open_cell_latches: Set[bytes] = set()  # local acceptance / custom schema cells not yet latched
        open_edges: Dict[bytes, List[Tuple[str, bytes]]] = {}  # w -> its eviction edges not yet latched
        bound_by_name: Dict[bytes, List[bytes]] = {}  # name -> local non-standard cells bound to it
        latched_sup: Dict[bytes, Set[bytes]] = {}
        any_sup: Dict[bytes, Set[bytes]] = {}
        prev_base: Optional[bytes] = None
        # a rotation admitted at commit idx whose scope does not govern yet, and whether it changes the rules (latch 4b)
        waiting: Optional[Tuple[bytes, int, bool]] = None
        born_at: Dict[bytes, int] = {}  # the commit each cell was born in
        governing_rules: List[bytes] = []  # the rules of each commit's governing scope (cross-checked, commit_rules)

        def waits(base_id: bytes, s_id: bytes) -> bool:
            """Must the rotation from `base_id` to `s_id` wait (§4.1, delayed rotation)? Only under rules with a delay,
            while some key of the base's admission or acceptance policy that the new scope's same policy lacks has
            not sealed the new scope under the base."""
            base_c, s_c = cells[base_id], cells[s_id]
            if len(base_c.slots) < 3:  # a v1 scope: its rules' delay is 0, so nothing it decides waits
                return False
            removed = set()
            for i in (0, 1):
                removed |= pol_quorum(base_c.slots[i])[1] - pol_quorum(s_c.slots[i])[1]
            return not removed <= signers(s_id, base_id, removed)

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

        def signers(cid: bytes, ctx: bytes, allowed_pks: Set[bytes]) -> Set[bytes]:
            return {s.actor_pubkey for s in seals_on.get(cid, ()) if s.h_scope_ctx == ctx and s.actor_pubkey in allowed_pks}

        def sup_reach(src: bytes, adj: Dict[bytes, Set[bytes]]) -> Set[bytes]:
            out: Set[bytes] = set()
            todo = list(adj.get(src, ()))
            while todo:
                nxt = todo.pop()
                if nxt not in out:
                    out.add(nxt)
                    todo.extend(adj.get(nxt, ()))
            return out

        for idx, (d_atoms, d_cells, d_seals) in enumerate(deltas):
            atoms.update(d_atoms)
            cells.update(d_cells)
            seals.update(d_seals)
            for s in d_seals.values():
                seals_on.setdefault(s.h_target, []).append(s)
            new_cids = set(d_cells)
            new_sids = set(d_seals)
            touched = {s.h_target for s in d_seals.values()}  # cells with a new seal in this commit

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
            base_changed = s_base_id != prev_base

            # Index this commit's cells
            for cid in new_cids:
                born_at[cid] = idx
            governing_rules.append(s_base.slots[2] if len(s_base.slots) == 3 else H_LENS_KERNEL)
            new_foreign_cells: List[bytes] = []
            for cid in sorted(new_cids):
                c = cells[cid]
                any_sup[cid] = set(hvec_items(c.h_supersedes))
                if cid in STD_SCHEMA_IDS:
                    continue
                c_orig = cell_origin(c)
                if c_orig == scope:
                    bound_by_name.setdefault(c.h_slot_name, []).append(cid)
                else:
                    foreign_by_origin.setdefault(c_orig, []).append(cid)
                    new_foreign_cells.append(cid)
                if c.h_schema == H_SCHEMA["scope"] and c_orig != scope:
                    foreign_scope_ids.append(cid)

            # Self-sealed foreign scopes present in cas/cells/ (a scope's POL1s are checked when it is born)
            newly_valid: List[Tuple[str, bytes, Set[bytes]]] = []
            for scid in list(foreign_scope_ids):
                if scid not in new_cids and scid not in touched:
                    continue  # nothing it is counted from has changed
                sc = cells[scid]
                f_origin = cell_origin(sc)
                f_thr, f_pks = pol_quorum(sc.slots[0])
                pol_quorum(sc.slots[1])
                if len(signers(scid, scid, f_pks)) >= f_thr:
                    self_sealed_foreign_scopes.add(scid)
                    valid_foreign_scopes.setdefault(f_origin, []).append((scid, f_pks))
                    newly_valid.append((f_origin, scid, f_pks))
                    foreign_scope_ids.remove(scid)

            # foreign endorsements accumulate the same way: a foreign cell's count against each self-sealed scope of
            # its origin is redone when the cell gets a new seal or its origin gets a new self-sealed scope
            recount: Set[Tuple[bytes, bytes]] = set()
            for fcid in new_foreign_cells + [t for t in touched if t in cells and t not in new_cids]:
                fc = cells[fcid]
                if fcid in STD_SCHEMA_IDS or cell_origin(fc) == scope:
                    continue
                recount.update((fcid, sf_id) for sf_id, _ in valid_foreign_scopes.get(cell_origin(fc), []))
            for f_origin, sf_id, _ in newly_valid:
                recount.update((fcid, sf_id) for fcid in foreign_by_origin.get(f_origin, []))
            pks_of_scope = {sf_id: sf_pks for vs in valid_foreign_scopes.values() for sf_id, sf_pks in vs}
            for fcid, sf_id in recount:
                foreign_endorsers_by_scope[(fcid, sf_id)] = signers(fcid, sf_id, pks_of_scope[sf_id])

            # Check #3: Every new local seal must bind to s_base_id and be signed by a roster member
            for sid in sorted(new_sids):
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
            for cid in sorted(new_cids):
                if cid in STD_SCHEMA_IDS:
                    continue
                c = cells[cid]
                c_orig = cell_origin(c)
                if c_orig == scope:
                    # writing a cell, and InitialEndorsers, count roster keys only (a projection's outside witnesses
                    # sign it, they do not write it)
                    roster = adm_pks | (acc_pks if c.h_schema == H_SCHEMA["acceptance"] else set())
                    c_signers = signers(cid, s_base_id, roster)
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
                        f_ends_union |= signers(cid, sf_id, sf_pks)
                    initial_endorsers[cid] = f_ends_union

            # At most one new local schema.scope cell in any transition commit
            pending_next_scope: Optional[bytes] = None
            pending_waits = False
            pending_change = False
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
                    if len(signers(s_next_id, s_base_id, adm_pks)) < adm_thr:
                        raise VarsError("new schema.scope cell lacks admission quorum under active SCOPE")
                    if RULES[s_base.slots[2]].encoding == "v2" and s_next.slots[2] == H_LENS_KERNEL:
                        raise VarsError("a rotation may not go back from v2 rules to v1 (RULES-V2.md §4)")
                    if waiting is not None:
                        raise VarsError("a new scope while a rotation waits (§4.1)")
                    # under rules with the delay a rotation to other rules always waits (latch 4b)
                    pending_change = bool(RULES[s_base.slots[2]].rotation_delay) and s_next.slots[2] != s_base.slots[2]
                    pending_waits = pending_change or waits(s_base_id, s_next_id)
                    pending_next_scope = s_next_id

            # Latch ACCEPTANCE (pinned to a self-sealed foreign scope per §2.5) and custom META_SCHEMA cells. An open
            # latch is re-read when its cell is new, gets a new seal, or S_base changes; nothing else moves it.
            for cid in new_cids:
                c = cells[cid]
                if cell_origin(c) == scope and (
                    (c.h_schema == H_SCHEMA["acceptance"] and cid not in latched_acc_auth)
                    or (c.h_schema == H_META_SCHEMA and cid not in latched_schema_auth)
                ):
                    open_cell_latches.add(cid)
            for cid in sorted(open_cell_latches if base_changed else open_cell_latches & (new_cids | touched)):
                c = cells[cid]
                if c.h_schema == H_SCHEMA["acceptance"]:
                    if c.slots[1] not in self_sealed_foreign_scopes:
                        raise VarsError("ACCEPTANCE foreign_scope_cell is not self-sealed")
                    if len(signers(cid, s_base_id, acc_pks)) >= acc_thr:
                        latched_acc_auth.add(cid)
                        open_cell_latches.discard(cid)
                elif len(signers(cid, s_base_id, adm_pks)) >= adm_thr:
                    latched_schema_auth.add(cid)
                    open_cell_latches.discard(cid)

            # Latch eviction / invalidation edges under s_base (re-read on the same events as above, keyed by w)
            for wid in new_cids:
                w = cells[wid]
                if w.h_schema == H_META_SCHEMA:
                    continue
                edges = [(kind, vid) for kind, mh in (("invalidates", w.h_invalidates), ("retires", w.h_retires),
                                                      ("supersedes", w.h_supersedes)) for vid in hvec_items(mh)]
                if edges:
                    open_edges[wid] = edges
            # a waiting scope supersedes nothing yet: its edge latches when it starts to govern (latch 4a), so the
            # Active local scope stays the governing one
            deferred = {waiting[0]} if waiting is not None else set()
            if pending_next_scope is not None and pending_waits:
                deferred.add(pending_next_scope)
            for wid in list(open_edges if base_changed else (open_edges.keys() & (new_cids | touched))):
                if wid in deferred:
                    continue
                w_ends_adm = signers(wid, s_base_id, adm_pks)
                w_ends_acc = signers(wid, s_base_id, acc_pks)
                still_open: List[Tuple[str, bytes]] = []
                for edge_kind, vid in open_edges[wid]:
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
                        if edge_kind == "supersedes":
                            latched_sup.setdefault(wid, set()).add(vid)
                    else:
                        still_open.append((edge_kind, vid))
                if still_open:
                    open_edges[wid] = still_open
                else:
                    del open_edges[wid]

            # unique binding per H_slot_name, checked after this commit's authorization latch.
            # Every new local cell c (except a scope cell, which has its own single-lineage rule) must reach every
            # other local cell bound to the same name through supersedes edges: c's own first hop may still await
            # co-signatures (c stays inactive until all its supersedes edges latch), every later hop must already be
            # latched. Latches never unlatch and Superseded is transitive in Pass 1, so at most one binding is Active.
            for cid in sorted(new_cids):
                c = cells[cid]
                if cid in STD_SCHEMA_IDS or cell_origin(c) != scope or c.h_schema == H_SCHEMA["scope"]:
                    continue
                peers = sorted(oid for oid in bound_by_name.get(c.h_slot_name, []) if oid != cid)
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

            # End-of-commit scope transition: the new scope governs the next commit, unless it removes keys without
            # their consent under rules with a delay; then it governs after that many more commits, or once every
            # removed key has sealed it (§4.1)
            # A rules change waits its full delay, and a new local cell of its window that references the waiting scope,
            # sealed under S_base by a key of its admission policy, cancels it for good (a veto, latch 4b; the gate
            # admits such a cell only as a veto with its evidence). It is checked before the wait can end.
            if pending_next_scope is not None:
                latched_scope_auth.add(pending_next_scope)
                waiting = (pending_next_scope, idx, pending_change)
            if waiting is not None:
                w_id, w_at, w_change = waiting
                vetoed = w_change and any(
                    w_at < born_at[cid] and cell_origin(c) == scope
                    and w_id in {r for _, r in cell_refs(c, cells, atoms, False)}
                    and signers(cid, s_base_id, adm_pks)
                    for cid, c in cells.items() if cid in born_at)
                if vetoed:
                    open_edges.pop(w_id, None)  # the scope never governs, and its supersedes edge never latches
                    waiting = None
                elif (idx >= w_at + RULES[s_base.slots[2]].rotation_delay
                      or (not w_change and not waits(s_base_id, w_id))):
                    latched_edge_auth.add((w_id, s_base_id, "supersedes"))  # its quorum was checked at admission
                    latched_sup.setdefault(w_id, set()).add(s_base_id)
                    open_edges.pop(w_id, None)
                    active_scope_id, waiting = w_id, None
            prev_base = s_base_id

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
            "governing_rules": governing_rules,
            "waiting": waiting,
        }

    def lens(self, scope: str, at: Optional[str] = None) -> Dict[str, object]:
        """The statuses of every cell at the scope's tip, or at commit `at` (a candidate the gate has checked, for
        `what_if`; no ref names it)."""
        tip = self.ref_commit(scope) if at is None else at
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
            cells, atoms, fold["value_refs"] if RULES[fold["rules"]].encoding == "v2" else None)
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
        # For each contract, decision and question Pass 3 evaluates: its evaluation policy and the keys it counts
        evaluators: Dict[bytes, Tuple[int, Set[bytes]]] = {}
        endorsers: Dict[bytes, Set[bytes]] = {}
        invalidators: Dict[bytes, Set[bytes]] = {}  # evaluators that endorse a live INVALID verdict on the cell

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
            live = active[cid] and not stale[cid]
            # a contract, decision or question that is not live is never Settled, but its endorsements are still
            # counted below, for what-if to say what it would need (`evaluators`, `endorsers`)
            if not live and c.h_schema not in (H_SCHEMA["contract"], H_SCHEMA["decision"], H_SCHEMA["question"]):
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
                            if not cycle_witness_answers(cw, req_comp, exp_out, atoms):
                                continue
                        else:
                            continue
                elif c.h_schema == H_SCHEMA["question"]:
                    if w.h_schema != c.slots[0]:
                        continue
                valid_endorsers |= (witness_endorsers(wid) & p_pks)

            evaluators[cid], endorsers[cid] = (p_thr, set(p_pks)), set(valid_endorsers)
            invalidators[cid] = set()
            if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
                for wid, w in cells.items():  # as the conflict check above reads them: by payload, not by edge
                    if (active.get(wid, False) and not stale.get(wid, False) and w.h_schema == H_SCHEMA["verdict"]
                            and w.h_payload == cid and w.slots[1] == H_VERDICT_INVALID):
                        invalidators[cid] |= witness_endorsers(wid) & p_pks
            is_set = live and len(valid_endorsers) >= p_thr
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
            "evaluators": evaluators,
            "endorsers": endorsers,
            "invalidators": invalidators,
            "parents_of": parents_of,  # the reference graph the rules read in this epoch (v2: typed references)
            "children_of": children_of,
        }

    def what_if(self, scope: str, atoms: Dict[bytes, bytes], cells: List["Cell"], seals: List["Seal"],
                assume: bool = False) -> Dict[str, object]:
        """See `_what_if`. With `assume`, the hypothesis's seals are supposed, not signed: each names a key and carries
        a zero signature, so a reader holding no key of the roster can ask what would follow if those keys sealed it.
        The gate checks everything else as for an admission (keys of the policy, references, replay); the run uses a
        throwaway instance, so no cache of this one ever holds an assumed seal, and its candidate can never be
        admitted, since a zero signature fails every real check. The report says `mode: assumed` in its context."""
        if not assume:
            return self._what_if(scope, atoms, cells, seals, "sealed")
        if not seals or any(x.signature != ZERO_SIGNATURE for x in seals):
            raise VarsError("an assumed hypothesis carries only seals with a zero signature")
        sim = GitVarsRepo(self.repo_dir)
        sim._assumed = frozenset(x.id for x in seals)
        return sim._what_if(scope, atoms, cells, seals, "assumed")

    def _what_if(self, scope: str, atoms: Dict[bytes, bytes], cells: List["Cell"], seals: List["Seal"], mode: str
                 ) -> Dict[str, object]:
        """What would follow if `cells` (a hypothesis: say a cell invalidating a ground, or an INVALID verdict) were
        admitted now. The hypothesis is built as a candidate commit on the tip and checked by the gate exactly as an
        admission would be, but no ref moves: the canonical chain is unchanged. The lens is computed at the tip and at
        the candidate. `lost` is every cell of the chain whose statuses change (each with its bits before and after),
        complete by construction; `held` is every cell of the hypothesis's region that keeps them (a decision still
        Settled through other verdicts, say), the region being the cells it names closed under two steps: a cell
        that relies on a region cell, and the cell a region verdict judges. Each row carries the shortest dependency
        path to it: from a hypothesis cell, or from an earlier cell a hypothesis seal newly seals, through the cells
        a hypothesis cell names, then only from a cell to one that relies on it or to the cell a verdict judges, as
        the rules read references in this epoch. Every step runs from a cell to one whose status may read it, never
        back through a shared ground; the path is a route of dependence, not a sufficient explanation, and it is
        empty when no such route exists (a change the hypothesis causes only through the fold, say).
        A lost row also carries `needs`: the grounds it relies on that no longer stand, and for a decision that lost
        Settled, its threshold, the endorsements still counted and those that fell away. A held row of a decision
        whose counted endorsements change carries them (threshold, before, after): Settled kept with a thinner
        margin is a consequence no status bit shows. `digest` is SHA-256 over the canonical JSON of both lists:
        two readers who agree on the consequences agree on it, whatever chain or hypothesis produced them.
        `transcript` binds the same lists to their context, the mode (`sealed`, or `assumed`: see `what_if`), the
        scope, tip, rules at the tip and at the candidate,
        hypothesis cells, and the (cell, key) of every hypothesis seal: equal transcripts, equal question and
        equal answer."""
        tip = self.ref_commit(scope)
        if tip is None:
            raise VarsError(f"no ref refs/vars/heads/{scope}")
        candidate = self.build_candidate_commit(scope, atoms, cells, seals, parent_commit=tip)
        try:
            self._check_commit(scope, candidate, tip)
        except VarsError:
            raise
        except (KeyError, IndexError, TypeError, ValueError, UnicodeDecodeError) as e:
            raise VarsError(f"malformed hypothesis refused ({type(e).__name__}: {e})") from None
        before, after = self.lens(scope), self.lens(scope, at=candidate)
        if self.ref_commit(scope) != tip:
            raise RuntimeError("what_if moved the scope's ref")
        hyp = {c.id for c in cells}
        acells, aatoms = after["cells"], after["atoms"]
        parents_of, children_of = after["parents_of"], after["children_of"]  # as the rules read references here

        def relies_on(cid: bytes) -> List[bytes]:
            h = acells[cid].h_relies
            return [] if h == H_EMPTY else parse_hvec(aatoms[h], require_sorted=True)

        relied_by: Dict[bytes, Set[bytes]] = {}
        for cid in acells:
            for v in relies_on(cid):
                relied_by.setdefault(v, set()).add(cid)
        targets = set().union(*(parents_of[h] for h in hyp)) - hyp
        judged = lambda v: ({acells[v].h_payload} if acells[v].h_schema == H_SCHEMA["verdict"]
                            and acells[v].h_payload in before["cells"] else set())
        region, todo = set(targets), list(targets)
        while todo:  # to a fixed point: what relies on a region cell, and what a region verdict judges
            u = todo.pop()
            for ch in relied_by.get(u, set()) | judged(u):
                if ch not in region and ch not in hyp:
                    region.add(ch)
                    todo.append(ch)
        bits = ("accepted", "invalidated", "effective", "retired", "superseded", "active", "stale", "settled")
        state = lambda lens, cid: {b: bool(lens[b].get(cid, False)) for b in bits}
        # shortest dependency path: a hypothesis cell to what it names, any cell to what relies on it or to what its
        # verdict judges; never backwards through a shared ground (a reference path either way is not a route of
        # dependence: Gemini review of the 2026-10-23 paper draft, §4.2)
        sealed = {x.h_target for x in seals if x.h_target not in hyp and x.h_target in before["cells"]}
        sources = hyp | sealed
        step = lambda u: (parents_of[u] if u in hyp else set()) | relied_by.get(u, set()) | judged(u)
        dist, prev, todo2 = {h: 0 for h in sources}, {}, deque(sorted(sources))
        while todo2:
            u = todo2.popleft()
            for v in sorted(step(u)):
                if v not in dist:
                    dist[v], prev[v] = dist[u] + 1, u
                    todo2.append(v)

        def path(cid: bytes) -> List[str]:
            if cid not in dist:
                return []  # no chain of references connects it to the hypothesis
            out = [cid]
            while out[-1] in prev:
                out.append(prev[out[-1]])
            return [x.hex() for x in reversed(out)]

        name = lambda cid: parse_utf8(aatoms[acells[cid].h_slot_name])
        standing = lambda cid: (after["active"].get(cid, False) and not after["stale"].get(cid, False)
                                and not after["invalidated"].get(cid, False))

        def needs(cid: bytes, b: Dict[str, bool], a: Dict[str, bool]) -> Dict[str, object]:
            """What the cell would need to regain what it lost: the grounds it relies on that no longer stand (to
            be replaced), and, for a Settled decision, the evaluators whose counted endorsement fell away."""
            out: Dict[str, object] = {}
            fallen = [g.hex() for g in relies_on(cid) if not standing(g)]
            if fallen:
                out["grounds"] = fallen
            if b.get("settled") and not a.get("settled") and cid in after["evaluators"]:
                thr, keys = after["evaluators"][cid]
                now, then = after["endorsers"][cid], before["endorsers"].get(cid, set())
                out["endorsements"] = {"threshold": thr, "standing": sorted(k.hex() for k in now),
                                       "fell_away": sorted(k.hex() for k in then - now)}
            return out

        lost, held = [], []
        for cid in sorted(before["cells"]):  # every changed cell is lost, inside the region or not: complete by construction
            b, a = state(before, cid), state(after, cid)
            if a == b and cid not in region:
                continue
            row = {"cell": cid.hex(), "name": name(cid), "path": path(cid)}
            if a != b:
                lost.append(dict(row, before={k: v for k, v in b.items() if v != a[k]},
                                 after={k: v for k, v in a.items() if v != b[k]}, needs=needs(cid, b, a)))
            else:
                thr_keys = after["evaluators"].get(cid)
                now, then = after["endorsers"].get(cid, set()), before["endorsers"].get(cid, set())
                if thr_keys is not None and now != then:
                    row["endorsements"] = {"threshold": thr_keys[0], "before": len(then), "after": len(now)}
                held.append(row)
        body = {"lost": lost, "held": held}
        canon = lambda o: json.dumps(o, sort_keys=True, separators=(",", ":")).encode()  # noqa: E731
        digest = sha256(canon(body)).hex()
        context = {"mode": mode, "scope": scope, "tip": tip, "rules": [before["rules"].hex(), after["rules"].hex()],
                   "hypothesis": sorted(h.hex() for h in hyp),
                   "seals": sorted([x.h_target.hex(), x.actor_pubkey.hex()] for x in seals)}
        return {"scope": scope, "tip": tip, "hypothesis": sorted(h.hex() for h in hyp), "candidate": candidate,
                **body, "digest": digest, "context": context,
                "transcript": sha256(b"minds.what-if.transcript@1\x00" + canon({"context": context, "digest": digest})).hex()}


# ---------------------------------------------------------------------------
# §4.4 Projection bundles: what a client without the repository holds and checks (checked by verify/minds_verify.py)
# ---------------------------------------------------------------------------
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
        deltas = repo.chain_deltas(repo.commit_chain(tip))
        kernel_input, _ = kernel_facts(scope, deltas)
        bundle["input"] = kernel_input.hex()
        bundle["output"] = kernel_runner(chain_rules(scope, deltas)).run(kernel_input).hex()
    return bundle


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


def _main(argv: List[str]) -> int:
    return _MV.main(argv)


if __name__ == "__main__":
    sys.exit(_main(sys.argv[1:]))

