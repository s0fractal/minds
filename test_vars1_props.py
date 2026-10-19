#!/usr/bin/env python3
"""Property-based invariant suite for VARS-1 (`vars1.py` at f69313a).

Random admission sequences are generated from a seeded `random.Random` (Hypothesis is not installed in this
workspace's Python). A sequence is a *program*: a list of commits, each a list of symbolic ops (genesis, scope
rotation, foreign scope, local/foreign cell with random relies/supersedes/retires/invalidates/attests edges,
same-name rebinding, ACCEPTANCE chains, checkpoints/verdicts, late detached seals). An interpreter turns a program
into real cells and seals, runs every commit through `GitVarsRepo.admit_and_advance`, and on every admitted tip
checks:

  I1  at most one Active local cell per H_slot_name
  I2  Stale equals a from-scratch least fixed point (oracle written from spec §4.2 Pass 2, order-free)
  I3  no Active cell has a supersedes edge that the spec §4.1 fold does not authorize (oracle from the spec);
      I3b additionally compares the whole latched edge set with that oracle;
      I3c compares the acceptance, custom-schema and scope Authorized latches with a spec oracle (latches 1, 2, 4)
  I4  every Settled contract/decision with required_comp has a REPLAYED checkpoint witness that a full replay from
      ComputationRoot reproduces (state bytes, NORMAL_FORM) with term_hash == expected_outcome
  I5  latches (scope, acceptance, schema, edge) never unlatch across commits
  I6  the lens is independent of dict iteration order (shuffled CAS dicts in-process) and of PYTHONHASHSEED
  I7  the scope cell the fold governs with is the unique Active local schema.scope cell
  I0  admit/lens never raise anything but VarsError (a TwinDivergence between the rules kernel and its Python twin
      is such a crash), and an admitted tip's lens never raises
  I8  a fresh run of the rules kernel on the lens's kernel input reproduces its Passes 1-2
  I11 Pass 3 recomputed from the kernel's input and output alone (`pass3_at_tip`, what a client holding a projection
      bundle computes) equals the lens's Settled for every contract and decision without required_comp

Failing programs are shrunk greedily (drop commits, ops, signers, edges) and frozen below as named regression
tests. Run `VARS1_PBT_SEQS=400 python3 test_vars1_props.py` for a longer exploration; the default stays < 2 min.
"""
from __future__ import annotations

import copy
import dataclasses
import json
import os
import random
import struct
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

ROOT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT_DIR))

import sigma_glyph as SG  # noqa: E402
import sigma_resume as SR  # noqa: E402
import vars1 as V  # noqa: E402

SCOPE = "core"
PEERS = ("peerB", "peerC")
# K0..k2: local roster candidates, k3/k4: peer keys, k5: outsider (may enter via rotation). Rosters may overlap.
SKS = [bytes([i + 1]) * 32 for i in range(6)]
PKS = [V.ed25519_pubkey(sk) for sk in SKS]
LOCAL_KEYS = [0, 1, 2]

# ---------------------------------------------------------------------------
# Book I fixtures: an honest computation APPLY(I, K) ->* K, and a computation of I whose "fake" states carry K
# ---------------------------------------------------------------------------
_APP_IK = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=V.H_I, right=V.H_K)
_H_APP = V.sha256(_APP_IK)
_ENV_H = SR.Environment([_H_APP], {_H_APP: _APP_IK})
_ENV_I = SR.Environment([], {})
COMP_ATOMS: Dict[bytes, bytes] = {}


def _put(atoms: Dict[bytes, bytes], raw: bytes) -> bytes:
    h = V.sha256(raw)
    atoms[h] = raw
    return h


_put(COMP_ATOMS, _APP_IK)
COMP = {
    "honest": _put(COMP_ATOMS, V.atom_computation_root(_H_APP, _put(COMP_ATOMS, V.atom_environment([_H_APP])))),
    "fake": _put(COMP_ATOMS, V.atom_computation_root(V.H_I, _put(COMP_ATOMS, V.atom_environment([])))),
}
_d, _i, _s = SR.start(COMP["honest"].hex(), _H_APP)
_PAUSED = SR.advance(_d, _i, _s, _ENV_H, additional_credit=0)
_NF = SR.advance(_PAUSED.checkpoint, _PAUSED.checkpoint_id, _PAUSED.state_bytes, _ENV_H, additional_credit=10)
_d, _i, _s = SR.start(COMP["fake"].hex(), V.H_I)
_I_NF = SR.advance(_d, _i, _s, _ENV_I, additional_credit=0)
_FAKE_K = b"SGS1" + COMP["fake"] + _NF.state_bytes[36:]
BIG = 10_000_001  # one ATP above the verifier ceiling -> NOT_ASSESSED at the gate

# Variant -> (comp, state_bytes, credit_total, spent_total, peak, outcome_text, actions of the transition)
_NF_ACTIONS = _NF.checkpoint["transition_claim"]["actions"]
CKPT_VARIANTS = {
    "h_paused0": ("honest", _PAUSED.state_bytes, 0, 0, _PAUSED.checkpoint["peak_semantic_size"], "PAUSED", 0),
    "h_nf": ("honest", _NF.state_bytes, 10, _NF.checkpoint["spent_total"], _NF.checkpoint["peak_semantic_size"], "NORMAL_FORM", _NF_ACTIONS),
    "h_nf_claims_paused": ("honest", _NF.state_bytes, 10, _NF.checkpoint["spent_total"], _NF.checkpoint["peak_semantic_size"], "PAUSED", _NF_ACTIONS),
    "h_nf_wrong_actions": ("honest", _NF.state_bytes, 10, _NF.checkpoint["spent_total"], _NF.checkpoint["peak_semantic_size"], "NORMAL_FORM", _NF_ACTIONS + 1),
    "i_nf": ("fake", _I_NF.state_bytes, 0, 0, _I_NF.checkpoint["peak_semantic_size"], "NORMAL_FORM", 0),
    "f_big_paused": ("fake", _FAKE_K, BIG, BIG, _NF.checkpoint["peak_semantic_size"], "PAUSED", 0),
    "f_big_nf": ("fake", _FAKE_K, BIG, BIG, _NF.checkpoint["peak_semantic_size"], "NORMAL_FORM", 0),
    "f_small_nf": ("fake", _FAKE_K, 10, 4, _NF.checkpoint["peak_semantic_size"], "NORMAL_FORM", 0),
}
EXP = {"K": V.H_K, "I": V.H_I, "EMPTY": V.H_EMPTY}
STATUS_KEYS = ("accepted", "invalidated", "effective", "retired", "superseded", "active", "stale", "settled", "provisional")


# ---------------------------------------------------------------------------
# Harness repos: memoize read_cas_tree per (immutable) commit; optionally shuffle dict order (I6)
# ---------------------------------------------------------------------------
class MemoRepo(V.GitVarsRepo):
    def __init__(self, repo_dir, shuffle_rng: Optional[random.Random] = None, shared=None):
        super().__init__(repo_dir)
        self._tree_memo = shared if shared is not None else {}
        self._shuffle = shuffle_rng

    def build_candidate_commit(self, scope, atoms, cells, seals, parent_commit=None, extra_tree_entries=None):
        # Speed only: write all new blobs with one `git hash-object` so the parent's per-blob calls hit its cache.
        raws = [r for r in [*atoms.values(), *(c.encode() for c in cells), *(s.encode() for s in seals)]
                if r not in self._oid_by_raw]
        raws = list(dict.fromkeys(raws))
        if raws:
            with tempfile.TemporaryDirectory() as td:
                paths = []
                for n, r in enumerate(raws):
                    p = Path(td) / str(n)
                    p.write_bytes(r)
                    paths.append(str(p))
                oids = self._git("hash-object", "-w", "--stdin-paths",
                                 input_bytes=("\n".join(paths) + "\n").encode()).decode().split()
            for r, oid in zip(raws, oids):
                self._oid_by_raw[r] = oid
                self._blob_by_oid[oid] = r
        return super().build_candidate_commit(scope, atoms, cells, seals, parent_commit, extra_tree_entries)

    def _shuffled(self, dicts):
        out = []
        for d in dicts:
            items = list(d.items())
            if self._shuffle is not None:
                self._shuffle.shuffle(items)
            out.append(dict(items))
        return tuple(out)

    def read_cas_tree(self, commit_oid):
        hit = self._tree_memo.get(commit_oid)
        if hit is None:
            hit = super().read_cas_tree(commit_oid)
            self._tree_memo[commit_oid] = hit
        return self._shuffled(hit)

    def read_commit_delta(self, commit_oid):
        # the fold and the kernel facts read the chain as per-commit deltas: shuffle those too (I6)
        return self._shuffled(super().read_commit_delta(commit_oid))


def lens_digest(lens: dict) -> Dict[str, List[str]]:
    return {k: sorted(cid.hex() for cid, v in lens[k].items() if v) for k in STATUS_KEYS}


def fold_latches(fold: dict) -> Dict[str, Set]:
    return {
        "scope": set(fold["latched_scope_auth"]),
        "acc": set(fold["latched_acc_auth"]),
        "schema": set(fold["latched_schema_auth"]),
        "edge": set(fold["latched_edge_auth"]),
    }


# ---------------------------------------------------------------------------
# Interpreter: program (list of commits of ops) -> real cells/seals -> admit_and_advance
# ---------------------------------------------------------------------------
class Interp:
    def __init__(self, path: Path):
        self.path = path
        subprocess.run(["git", "-C", str(path), "init", "-q"], check=True)
        self.repo = MemoRepo(path)
        self.tip: Optional[str] = None
        self.ids: Dict[str, bytes] = {}  # handle -> cell id
        self.meta: Dict[str, dict] = {}  # handle -> {origin, kind, name, ...}
        self.cell_by_id: Dict[bytes, V.Cell] = {c.id: c for c in V.STD_SCHEMAS.values()}
        self.seals: Dict[bytes, V.Seal] = {}
        self.atoms: Dict[bytes, bytes] = dict(V.STD_SCHEMA_ATOMS)
        self.cur: Optional[str] = None  # handle of the active local scope
        self.history: List[dict] = []  # per admitted commit: scope id at start, cells, seals, new ids
        self.tips: List[str] = []
        self.crashes: List[str] = []

    # -- helpers ------------------------------------------------------------------------------------------
    def _snapshot(self):
        return (self.tip, dict(self.ids), copy.deepcopy(self.meta), dict(self.cell_by_id), dict(self.seals),
                dict(self.atoms), self.cur)

    def _restore(self, snap):
        self.tip, self.ids, self.meta, self.cell_by_id, self.seals, self.atoms, self.cur = snap

    def _hv(self, atoms, ids: List[bytes]) -> bytes:
        return _put(atoms, V.atom_hvec(ids))

    def _pol(self, atoms, thr: int, keys: List[int]) -> bytes:
        return _put(atoms, V.atom_pol1(thr, self._hv(atoms, [PKS[k] for k in keys])))

    def _ref(self, hs: List[str]) -> List[bytes]:
        return sorted({self.ids[h] for h in hs if h in self.ids})

    def roster(self, h: Optional[str] = None) -> Tuple[List[int], List[int]]:
        m = self.meta[h or self.cur]
        return m["adm"], m["acc"]

    # -- one commit -----------------------------------------------------------------------------------------
    def exec_commit(self, ops: List[dict]) -> bool:
        snap = self._snapshot()
        atoms: Dict[bytes, bytes] = {}
        new_cells: List[V.Cell] = []
        new_seals: List[V.Seal] = []
        scope_at_start = self.ids.get(self.cur) if self.cur else None
        next_cur = self.cur
        try:
            for op in ops:
                kind = op["op"]
                if kind in ("genesis", "rotate", "fscope"):
                    origin = SCOPE if kind != "fscope" else op["peer"]
                    adm = op["adm"] if kind != "fscope" else op["keys"]
                    acc = op["acc"] if kind != "fscope" else op["keys"]
                    adm_thr = op["adm_thr"] if kind != "fscope" else op["thr"]
                    acc_thr = op["acc_thr"] if kind != "fscope" else op["thr"]
                    kw = {}
                    sup = self._ref(op.get("edges", {}).get("supersedes", [])) if kind == "fscope" else []
                    if sup:
                        kw = dict(h_supersedes=self._hv(atoms, sup), h_loss=_put(atoms, V.atom_utf8(f"fscope {op['h']}")))
                    if kind == "rotate":
                        if self.cur not in self.ids:
                            continue
                        kw = dict(h_supersedes=self._hv(atoms, [self.ids[self.cur]]),
                                  h_loss=_put(atoms, V.atom_utf8(f"rotate {op['h']}")))
                    payload = origin if kind == "genesis" else f"{origin}#{op['h']}"
                    cell = V.Cell(
                        h_schema=V.H_SCHEMA["scope"],
                        h_slot_name=_put(atoms, V.atom_utf8(f"{origin}/SCOPE")),
                        h_payload=_put(atoms, V.atom_utf8(payload)),
                        slots=(self._pol(atoms, adm_thr, adm), self._pol(atoms, acc_thr, acc), V.H_LENS_KERNEL),
                        **kw,
                    )
                    ctx = cell.id if kind != "rotate" else self.ids[self.cur]
                    for k in op["signers"]:
                        new_seals.append(V.Seal.sign(SKS[k], cell.id, ctx))
                    self._register(op["h"], cell, new_cells, origin=origin, kind="scope", name=f"{origin}/SCOPE",
                                   adm=list(adm), acc=list(acc), adm_thr=adm_thr)
                    if kind == "genesis":
                        atoms.update(COMP_ATOMS)
                    if kind in ("genesis", "rotate"):
                        next_cur = op["h"]
                elif kind == "cell":
                    cell = self._build_cell(op, atoms)
                    if cell is None:
                        continue
                    if op["origin"] == SCOPE:
                        ctx = self.ids.get(self.cur)
                    else:
                        ctx = self.ids.get(op.get("ctx"))
                    if ctx is None:
                        continue
                    for k in op["signers"]:
                        new_seals.append(V.Seal.sign(SKS[k], cell.id, ctx))
                    self._register(op["h"], cell, new_cells, origin=op["origin"], kind=op["kind"], name=op["name"],
                                   **{k: op[k] for k in ("tier", "req", "exp", "pol", "schema") if k in op})
                elif kind == "seal":
                    if op["target"] not in self.ids:
                        continue
                    ctx = self.ids.get(op["ctx"]) if op.get("ctx") else self.ids.get(self.cur)
                    if ctx is None:
                        continue
                    new_seals.append(V.Seal.sign(SKS[op["key"]], self.ids[op["target"]], ctx))
                else:
                    raise ValueError(f"unknown op {kind}")
            if not new_cells and not new_seals:
                self._restore(snap)
                return False
            cells_arg = list(V.STD_SCHEMAS.values()) + new_cells if self.tip is None else new_cells
            atoms_arg = {**V.STD_SCHEMA_ATOMS, **atoms} if self.tip is None else atoms
            cand = self.repo.build_candidate_commit(SCOPE, atoms_arg, cells_arg, new_seals, parent_commit=self.tip)
            self.repo.admit_and_advance(SCOPE, cand, expected_old=self.tip)
        except V.VarsError as e:
            self._restore(snap)
            self.last_reject = str(e)
            return False
        except Exception as e:  # noqa: BLE001  (the gate refused, but not with VarsError: record, treat as rejected)
            self._restore(snap)
            self.crashes.append(f"non-VarsError during admission: {type(e).__name__}: {str(e)[:120]}")
            return False
        for c in new_cells:
            self.cell_by_id[c.id] = c
        for s in new_seals:
            self.seals[s.id] = s
        self.atoms.update(atoms)
        self.cur = next_cur
        self.tip = cand
        self.tips.append(cand)
        self.history.append({
            "scope": scope_at_start if scope_at_start is not None else self.ids[next_cur],
            "cells": dict(self.cell_by_id),
            "seals": list(self.seals.values()),
            "new": {c.id for c in new_cells},
        })
        return True

    def _register(self, h, cell, new_cells, **meta):
        self.ids[h] = cell.id
        self.meta[h] = meta
        self.cell_by_id[cell.id] = cell
        new_cells.append(cell)

    def _build_cell(self, op: dict, atoms) -> Optional[V.Cell]:
        cell = self._build_cell_typed(op, atoms)
        bad = op.get("bad")
        if cell is None or not bad:
            return cell
        # Wrong-typed slot value (the gate checks existence, not the schema's declared slot type)
        val = {"K": V.H_K, "EMPTY": V.H_EMPTY}.get(bad["val"])
        if bad["val"] == "utf8":
            val = _put(atoms, V.atom_utf8("not a typed value"))
        elif bad["val"] == "env":
            val = _put(atoms, V.atom_environment([]))
        elif bad["val"].startswith("cell:"):
            val = self.ids.get(bad["val"][5:])
        if val is None or bad["slot"] >= len(cell.slots):
            return cell
        slots = list(cell.slots)
        slots[bad["slot"]] = val
        kw = {}
        if op["kind"] == "checkpoint" and bad["slot"] == 0:
            kw["h_payload"] = _put(atoms, b"SGS1" + val + _NF.state_bytes[36:])
        return dataclasses.replace(cell, slots=tuple(slots), **kw)

    def _build_cell_typed(self, op: dict, atoms) -> Optional[V.Cell]:
        e = op.get("edges", {})
        kind = op["kind"]
        kw = {}
        for mname in ("relies", "attests", "supersedes", "retires", "invalidates"):
            ids = self._ref(e.get(mname, []))
            if ids:
                kw[f"h_{mname}"] = self._hv(atoms, ids)
        if "h_supersedes" in kw or "h_retires" in kw:
            kw["h_loss"] = _put(atoms, V.atom_utf8(f"loss {op['h']}"))
        name = _put(atoms, V.atom_utf8(op["name"]))
        text = _put(atoms, V.atom_utf8(f"{kind} {op['h']}"))
        if kind == "schema":  # custom schema cell: H_EMPTY payload and edges, one utf8 field
            return V.Cell(h_schema=V.H_META_SCHEMA, h_slot_name=name, h_payload=V.H_EMPTY,
                          slots=(_put(atoms, V.atom_utf8("note:utf8")),))
        if kind == "custom":  # an instance of a custom schema
            if op["schema"] not in self.ids:
                return None
            return V.Cell(h_schema=self.ids[op["schema"]], h_slot_name=name, h_payload=text, slots=(text,), **kw)
        sch = V.H_SCHEMA[kind]
        if kind == "axiom":
            return V.Cell(h_schema=sch, h_slot_name=name, h_payload=text, **kw)
        if kind == "computation":
            return V.Cell(h_schema=sch, h_slot_name=name, h_payload=COMP[op["comp"]], **kw)
        if kind == "checkpoint":
            comp, state, credit, spent, peak, outc, actions = CKPT_VARIANTS[op["variant"]]
            u = lambda n: _put(atoms, V.atom_u64(n))  # noqa: E731
            return V.Cell(h_schema=sch, h_slot_name=name, h_payload=_put(atoms, state),
                          slots=(COMP[comp], u(credit), u(spent), u(peak), _put(atoms, V.atom_utf8(outc)), u(actions)), **kw)
        if kind in ("contract", "question"):
            pol = self._pol(atoms, op["pol"][0], op["pol"][1]) if op.get("pol") else V.H_EMPTY
            if kind == "question":
                return V.Cell(h_schema=sch, h_slot_name=name, h_payload=text, slots=(V.H_SCHEMA["axiom"], pol), **kw)
            tier = V.H_PROVISIONAL if op["tier"] == "provisional" else V.H_OWNER
            req = COMP[op["req"]] if op.get("req") else V.H_EMPTY
            return V.Cell(h_schema=sch, h_slot_name=name, h_payload=text, slots=(tier, req, EXP[op["exp"]], pol), **kw)
        if kind == "verdict":
            if op["target"] not in self.ids:
                return None
            ck = self.ids.get(op.get("ckpt")) or V.H_EMPTY
            code = {"ATTESTED": V.H_ATTESTED, "REPLAYED": V.H_REPLAYED, "INVALID": V.H_VERDICT_INVALID}[op["code"]]
            vid = _put(atoms, V.atom_utf8(SR.VERIFIER_ID if op.get("vid", "sr") == "sr" else "other-verifier"))
            return V.Cell(h_schema=sch, h_slot_name=name, h_payload=self.ids[op["target"]], slots=(ck, code, vid), **kw)
        if kind == "acceptance":
            if op["target"] not in self.ids or op["fscope"] not in self.ids:
                return None
            return V.Cell(h_schema=sch, h_slot_name=name, h_payload=self.ids[op["target"]],
                          slots=(_put(atoms, V.atom_utf8(op["peer"])), self.ids[op["fscope"]]), **kw)
        raise ValueError(kind)


# ---------------------------------------------------------------------------
# Generator: proposes the next commit from the interpreter's current state
# ---------------------------------------------------------------------------
class Gen:
    def __init__(self, rng: random.Random):
        self.r = rng
        self.n = 0
        self.pending: List = []  # follow-up commits of a macro: callables it -> ops, so signers track rotations

    def h(self) -> str:
        self.n += 1
        return f"h{self.n}"

    def subset(self, xs, lo=1):
        xs = list(xs)
        if not xs:
            return []
        k = self.r.randint(min(lo, len(xs)), len(xs))
        return sorted(self.r.sample(xs, k))

    def genesis(self) -> List[dict]:
        adm = self.subset(LOCAL_KEYS)
        acc = self.subset(LOCAL_KEYS)
        adm_thr = self.r.randint(1, len(adm))
        return [{"op": "genesis", "h": self.h(), "adm": adm, "adm_thr": adm_thr, "acc": acc,
                 "acc_thr": self.r.randint(1, len(acc)), "signers": sorted(self.r.sample(adm, adm_thr))}]

    def signers(self, it: Interp, acceptance=False, origin=SCOPE, fscope=None) -> List[int]:
        if origin == SCOPE:
            adm, acc = it.roster()
            pool = sorted(set(adm) | set(acc)) if acceptance else adm
        else:
            pool = it.meta[fscope]["adm"]
        out = self.subset(pool)
        if self.r.random() < 0.05:
            out = sorted(set(out) | {self.r.randrange(len(SKS))})
        return out

    def handles(self, it: Interp, pred=lambda h, m: True) -> List[str]:
        return [h for h, m in it.meta.items() if pred(h, m)]

    def pick(self, xs, p=1.0, k=1):
        if not xs or self.r.random() > p:
            return []
        return self.r.sample(xs, min(k, len(xs)))

    def local_cell(self, it: Interp, kind: Optional[str] = None) -> Optional[dict]:
        r = self.r
        kind = kind or r.choice(["axiom"] * 5 + ["contract"] * 2 + ["verdict"] * 3 + ["computation"] * 2 + ["checkpoint"] * 3
                                + ["question", "acceptance", "acceptance", "schema", "custom"])
        h = self.h()
        if kind == "schema":  # unique name, no edges; signed by a random subset, so late seals may latch it
            return {"op": "cell", "h": h, "origin": SCOPE, "kind": kind, "name": f"{SCOPE}/sch.u{h}", "edges": {},
                    "signers": self.signers(it)}
        op = {"op": "cell", "h": h, "origin": SCOPE, "kind": kind, "edges": {}}
        allh = self.handles(it, lambda hh, m: m["kind"] != "scope")
        same_kind_local = lambda hh, m: m["origin"] == SCOPE and m["kind"] == kind  # noqa: E731
        # Name: shared pool (rebinding pressure) or fresh
        if r.random() < 0.55:
            op["name"] = f"{SCOPE}/{kind}.{r.randint(0, 1)}"
        else:
            op["name"] = f"{SCOPE}/{kind}.u{h}"
        peers_same_name = [hh for hh in self.handles(it, same_kind_local) if it.meta[hh]["name"] == op["name"]]
        any_same_name = [hh for hh, m in it.meta.items() if m["origin"] == SCOPE and m["name"] == op["name"]]
        if any_same_name and not peers_same_name:
            op["name"] = f"{SCOPE}/{kind}.u{h}"
        elif peers_same_name:
            mode = r.random()
            if mode < 0.55:
                op["edges"]["supersedes"] = [peers_same_name[-1]]
            elif mode < 0.75:
                op["edges"]["supersedes"] = [r.choice(peers_same_name)]
            elif mode < 0.9:
                op["edges"]["supersedes"] = list(peers_same_name)
            elif mode < 0.95:
                op["edges"]["retires"] = [r.choice(peers_same_name)]
        op["edges"]["relies"] = self.pick(allh, 0.4, r.randint(1, 2))
        if r.random() < 0.12:
            op["edges"]["retires"] = op["edges"].get("retires", []) + self.pick(allh)
        if r.random() < 0.12:
            op["edges"]["invalidates"] = self.pick(allh)
        if r.random() < 0.08:  # arbitrary same-kind supersedes (cross-name)
            op["edges"]["supersedes"] = op["edges"].get("supersedes", []) + self.pick(self.handles(it, lambda hh, m: m["kind"] == kind))
        if kind == "computation":
            op["comp"] = r.choice(["honest", "fake"])
        elif kind == "checkpoint":
            op["variant"] = r.choice(list(CKPT_VARIANTS))
            comp = CKPT_VARIANTS[op["variant"]][0]
            parents = self.handles(it, lambda hh, m: m["kind"] == "checkpoint")
            if parents and r.random() < 0.5:
                op["edges"]["relies"] = op["edges"]["relies"] + [r.choice(parents)]
            comps = self.handles(it, lambda hh, m: m["kind"] == "computation" and m.get("comp") == comp)
            if comps and r.random() < 0.5:
                op["edges"]["relies"] = op["edges"]["relies"] + [r.choice(comps)]
        elif kind in ("contract", "question"):
            op["pol"] = None
            if r.random() < 0.4:
                adm, _ = it.roster()
                keys = self.subset(adm)
                op["pol"] = [r.randint(1, len(keys)), keys]
            if kind == "contract":
                op["tier"] = r.choice(["provisional", "provisional", "owner"])
                op["req"] = r.choice([None, "honest", "honest", "fake"])
                op["exp"] = r.choice(["K", "K", "I", "EMPTY"])
                if op["req"]:
                    comps = self.handles(it, lambda hh, m: m["kind"] == "computation" and m.get("comp") == op["req"])
                    if not comps and r.random() < 0.9:
                        op["req"] = None
                    elif comps and r.random() < 0.95:
                        op["edges"]["relies"] = op["edges"]["relies"] + [r.choice(comps)]
        elif kind == "verdict":
            targets = self.handles(it, lambda hh, m: m["kind"] in ("contract",) or (m["kind"] != "scope" and r.random() < 0.05))
            if not targets:
                return None
            op["target"] = r.choice(targets)
            op["code"] = r.choice(["ATTESTED", "ATTESTED", "REPLAYED", "REPLAYED", "INVALID"])
            op["vid"] = "sr" if r.random() < 0.85 else "other"
            ckpts = self.handles(it, lambda hh, m: m["kind"] == "checkpoint")
            if op["code"] != "ATTESTED" and ckpts and r.random() < 0.85:
                op["ckpt"] = r.choice(ckpts)
                op["edges"]["relies"] = op["edges"]["relies"] + [op["ckpt"]]
            if it.meta[op["target"]]["kind"] in ("contract", "question") and r.random() < 0.9:
                op["edges"]["attests"] = [op["target"]]
            if op["code"] == "INVALID" and r.random() < 0.6:
                op["edges"]["invalidates"] = [op["target"]]
        elif kind == "custom":
            schemas = self.handles(it, lambda hh, m: m["kind"] == "schema")
            if not schemas:
                return None
            op["schema"] = r.choice(schemas)
        elif kind == "acceptance":
            foreign = self.handles(it, lambda hh, m: m["origin"] != SCOPE and (m["kind"] != "scope" or r.random() < 0.3))
            if not foreign:
                return None
            op["target"] = r.choice(foreign)
            peer = it.meta[op["target"]]["origin"]
            fscopes = self.handles(it, lambda hh, m: m["kind"] == "scope" and m["origin"] == peer)
            if not fscopes:
                return None
            op["peer"] = peer
            op["fscope"] = r.choice(fscopes)
        if kind in ("contract", "question", "checkpoint") and r.random() < 0.06:
            op["bad"] = self.bad_slot(it, kind)
        if kind == "axiom":
            qs = self.handles(it, lambda hh, m: m["kind"] == "question")
            if qs and r.random() < 0.3:
                op["edges"]["attests"] = [r.choice(qs)]
        op["signers"] = self.signers(it, acceptance=(kind == "acceptance"))
        op["edges"] = {k: v for k, v in op["edges"].items() if v}
        return op

    def bad_slot(self, it: Interp, kind: str) -> dict:
        r = self.r
        slot = {"contract": r.choice([0, 3, 3]), "question": r.choice([0, 1]), "checkpoint": 0}[kind]
        cells = [hh for hh, m in it.meta.items() if m["kind"] != "scope"]
        vals = ["K", "utf8", "env"] + ([f"cell:{r.choice(cells)}"] if cells else [])
        return {"slot": slot, "val": r.choice(vals)}

    def foreign_cell(self, it: Interp) -> Optional[dict]:
        r = self.r
        fscopes = self.handles(it, lambda hh, m: m["kind"] == "scope" and m["origin"] != SCOPE)
        if not fscopes:
            return None
        fs = r.choice(fscopes)
        peer = it.meta[fs]["origin"]
        h = self.h()
        kind = r.choice(["axiom"] * 4 + ["verdict", "contract"])
        op = {"op": "cell", "h": h, "origin": peer, "kind": kind, "name": f"{peer}/{kind}.{h}", "ctx": fs, "edges": {}}
        same_peer = self.handles(it, lambda hh, m: m["origin"] == peer and m["kind"] != "scope")
        op["edges"]["relies"] = self.pick(same_peer, 0.6, r.randint(1, 2)) + self.pick(
            self.handles(it, lambda hh, m: m["kind"] != "scope"), 0.15)
        if r.random() < 0.1:
            op["edges"]["invalidates"] = self.pick(self.handles(it, lambda hh, m: m["kind"] != "scope"))
        if kind == "verdict":
            targets = self.handles(it, lambda hh, m: m["kind"] == "contract")
            if not targets:
                return None
            op["target"] = r.choice(targets)
            op["code"] = "ATTESTED"
            op["edges"]["attests"] = [op["target"]]
        if kind == "contract":
            op.update(tier=r.choice(["provisional", "owner"]), req=None, exp="EMPTY", pol=None)
            if r.random() < 0.3:
                op["bad"] = self.bad_slot(it, "contract")
        op["signers"] = self.signers(it, origin=peer, fscope=fs)
        op["edges"] = {k: v for k, v in op["edges"].items() if v}
        return op

    def fscope(self, it: Interp) -> dict:
        r = self.r
        peer = r.choice(PEERS)
        keys = self.subset([3, 4] + ([r.choice(LOCAL_KEYS)] if r.random() < 0.3 else []))
        thr = r.randint(1, len(keys))
        signers = sorted(r.sample(keys, thr if r.random() < 0.9 else max(0, thr - 1)))
        op = {"op": "fscope", "h": self.h(), "peer": peer, "keys": keys, "thr": thr, "signers": signers}
        if r.random() < 0.15:  # a foreign scope cell superseding some scope cell (local or foreign)
            op["edges"] = {"supersedes": self.pick(self.handles(it, lambda hh, m: m["kind"] == "scope"))}
        return op

    def rotate(self, it: Interp) -> dict:
        r = self.r
        adm_now, _ = it.roster()
        thr_now = it.meta[it.cur]["adm_thr"]
        adm = self.subset(LOCAL_KEYS + [5])
        acc = self.subset(LOCAL_KEYS + [5])
        signers = self.subset(adm_now, lo=min(len(adm_now), max(1, thr_now if r.random() < 0.8 else 1)))
        return {"op": "rotate", "h": self.h(), "adm": adm, "adm_thr": r.randint(1, len(adm)), "acc": acc,
                "acc_thr": r.randint(1, len(acc)), "signers": signers}

    def seal(self, it: Interp) -> Optional[dict]:
        r = self.r
        if r.random() < 0.75:
            targets = self.handles(it, lambda hh, m: m["origin"] == SCOPE and m["kind"] != "scope")
            if not targets:
                return None
            t = r.choice(targets)
            adm, acc = it.roster()
            pool = sorted(set(adm) | set(acc)) if it.meta[t]["kind"] == "acceptance" else adm
            return {"op": "seal", "target": t, "key": r.choice(pool), "ctx": None}
        if r.random() < 0.6:  # late foreign co-signature
            targets = self.handles(it, lambda hh, m: m["origin"] != SCOPE and m["kind"] != "scope")
            if not targets:
                return None
            t = r.choice(targets)
            fss = self.handles(it, lambda hh, m: m["kind"] == "scope" and m["origin"] == it.meta[t]["origin"])
            fs = r.choice(fss)
            return {"op": "seal", "target": t, "key": r.choice(it.meta[fs]["adm"]), "ctx": fs}
        # Cross seal: a local roster key endorses a foreign cell (scope cells included) under the local scope
        targets = self.handles(it, lambda hh, m: m["origin"] != SCOPE)
        if not targets:
            return None
        adm, _ = it.roster()
        return {"op": "seal", "target": r.choice(targets), "key": r.choice(adm), "ctx": None}

    def bundle(self, it: Interp) -> List[dict]:
        """computation -> checkpoint lineage -> contract -> REPLAYED/ATTESTED/INVALID verdicts in one commit."""
        r = self.r
        ops: List[dict] = []
        sig = lambda: self.signers(it)  # noqa: E731
        comp = r.choice(["honest", "honest", "fake"])
        comps = self.handles(it, lambda hh, m: m["kind"] == "computation" and m.get("comp") == comp)
        if comps and r.random() < 0.6:
            hc = r.choice(comps)
        else:
            hc = self.h()
            ops.append({"op": "cell", "h": hc, "origin": SCOPE, "kind": "computation", "comp": comp,
                        "name": f"{SCOPE}/computation.u{hc}", "edges": {}, "signers": sig()})
        lineage = {"honest": [["h_nf"], ["h_paused0", "h_nf"], ["h_nf_claims_paused"], ["h_nf_wrong_actions"]],
                   "fake": [["i_nf"], ["f_big_paused", "f_big_nf"], ["f_big_paused", "f_big_nf"], ["f_big_nf"], ["f_small_nf"]]}[comp]
        parent = None
        for variant in r.choice(lineage):
            hk = self.h()
            rel = [hc] + ([parent] if parent else [])
            ops.append({"op": "cell", "h": hk, "origin": SCOPE, "kind": "checkpoint", "variant": variant,
                        "name": f"{SCOPE}/checkpoint.u{hk}", "edges": {"relies": rel}, "signers": sig()})
            parent = hk
        adm, _ = it.roster()
        pol = None
        if r.random() < 0.5:
            keys = self.subset(adm)
            pol = [r.randint(1, len(keys)), keys]
        hk_contract = self.h()
        ops.append({"op": "cell", "h": hk_contract, "origin": SCOPE, "kind": "contract", "tier": r.choice(["provisional", "owner"]),
                    "req": comp, "exp": r.choice(["K", "I"]), "pol": pol, "name": f"{SCOPE}/contract.u{hk_contract}",
                    "edges": {"relies": [hc]}, "signers": sig()})
        for _ in range(r.choice([1, 1, 2])):
            hv = self.h()
            code = r.choice(["REPLAYED", "REPLAYED", "REPLAYED", "INVALID"])
            ops.append({"op": "cell", "h": hv, "origin": SCOPE, "kind": "verdict", "target": hk_contract, "code": code,
                        "ckpt": parent, "vid": "sr", "name": f"{SCOPE}/verdict.u{hv}",
                        "edges": {"relies": [parent], "attests": [hk_contract]},
                        "signers": self.full(adm) if r.random() < 0.6 else sig()})
        return ops

    def attest_bundle(self, it: Interp) -> List[dict]:
        """contract without required_comp -> ATTESTED (sometimes INVALID, sometimes sealed by no policy key)
        verdicts; sometimes a foreign verdict under a peer scope sharing a policy key, accepted directly or through a
        newer cell of its peer, in the same or a later commit (I11 compares a client's Pass 3 with the lens)."""
        r = self.r
        adm, _ = it.roster()
        pol = None
        if r.random() < 0.5:
            keys = self.subset(adm)
            pol = [r.randint(1, len(keys)), keys]
        hc = self.h()
        ops = [{"op": "cell", "h": hc, "origin": SCOPE, "kind": "contract", "tier": r.choice(["provisional", "owner"]),
                "req": None, "exp": "EMPTY", "pol": pol, "name": f"{SCOPE}/contract.u{hc}", "edges": {},
                "signers": self.signers(it)}]
        if r.random() < 0.5:  # a foreign verdict, endorsed under a self-sealed peer scope sharing a policy key
            peer = r.choice(PEERS)
            keys = sorted({r.choice([3, 4]), r.choice(pol[1] if pol else adm)})
            thr = r.randint(1, len(keys))
            hf, hv, ha = self.h(), self.h(), self.h()
            foreign = [
                {"op": "fscope", "h": hf, "peer": peer, "keys": keys, "thr": thr,
                 "signers": sorted(r.sample(keys, thr if r.random() < 0.9 else thr - 1))},
                {"op": "cell", "h": hv, "origin": peer, "kind": "verdict", "target": hc, "code": "ATTESTED",
                 "vid": "sr", "name": f"{peer}/verdict.{hv}", "ctx": hf, "edges": {"attests": [hc]},
                 "signers": self.subset(keys)},
            ]
            target = hv
            if r.random() < 0.4:  # accept a newer cell of the same peer that relies on the verdict (hereditary)
                hy = self.h()
                foreign.append({"op": "cell", "h": hy, "origin": peer, "kind": "axiom", "name": f"{peer}/axiom.{hy}",
                                "ctx": hf, "edges": {"relies": [hv]}, "signers": self.subset(keys)})
                target = hy
            foreign += [
                {"op": "cell", "h": ha, "origin": SCOPE, "kind": "acceptance", "name": f"{SCOPE}/acceptance.{ha}",
                 "target": target, "peer": peer, "fscope": hf, "edges": {},
                 "signers": self.full(sorted(set(it.roster()[1]))) if r.random() < 0.85 else self.signers(it, True)},
            ]
            if r.random() < 0.5:
                ops += foreign
            else:
                self.pending.append(lambda it2, f=foreign: f)
        for _ in range(r.choice([0, 1, 1, 2, 3])):
            hv = self.h()
            ops.append({"op": "cell", "h": hv, "origin": SCOPE, "kind": "verdict", "target": hc,
                        "code": "INVALID" if r.random() < 0.2 else "ATTESTED",
                        "vid": "sr" if r.random() < 0.85 else "other", "name": f"{SCOPE}/verdict.u{hv}",
                        "edges": {"attests": [hc]} if r.random() < 0.9 else {},
                        "signers": self.full(adm) if r.random() < 0.6 else self.signers(it)})
            outside = [k for k in adm if pol and k not in pol[1]]
            if ops[-1]["code"] == "INVALID" and outside and r.random() < 0.6:
                ops[-1]["signers"] = outside  # sealed by no policy key: it must not block
        return ops

    def full(self, keys: List[int]) -> List[int]:
        return sorted(keys)

    def acc_chain(self, it: Interp) -> List[dict]:
        """D <- A0 accepts X0 <- A1 accepts X1 ... (mixed peers, cross-peer relies); later D is withdrawn."""
        r = self.r
        ops: List[dict] = []
        adm, acc = it.roster()
        fs_of: Dict[str, str] = {}
        for peer in PEERS:
            have = self.handles(it, lambda hh, m: m["kind"] == "scope" and m["origin"] == peer)
            if have:
                fs_of[peer] = r.choice(have)
            else:
                f = self.fscope(it)
                f.update(peer=peer, signers=sorted(r.sample(f["keys"], f["thr"])))
                f.pop("edges", None)
                ops.append(f)
                fs_of[peer] = f["h"]
                it_keys = f["keys"]
                fs_of[peer + "#keys"] = it_keys
        hd = self.h()
        ops.append({"op": "cell", "h": hd, "origin": SCOPE, "kind": "axiom", "name": f"{SCOPE}/axiom.d{hd}", "edges": {},
                    "signers": self.subset(adm)})
        prev_x = None
        for i in range(r.randint(3, 6)):
            peer = r.choice(PEERS)
            fs = fs_of[peer]
            keys = fs_of.get(peer + "#keys") or it.meta[fs]["adm"]
            hx = self.h()
            rel = [prev_x] if prev_x and r.random() < 0.6 else []
            ops.append({"op": "cell", "h": hx, "origin": peer, "kind": "axiom", "name": f"{peer}/axiom.{hx}", "ctx": fs,
                        "edges": {"relies": rel} if rel else {}, "signers": self.subset(keys)})
            ha = self.h()
            dep = hd if prev_x is None or r.random() < 0.1 else prev_x
            ops.append({"op": "cell", "h": ha, "origin": SCOPE, "kind": "acceptance", "name": f"{SCOPE}/acceptance.{ha}",
                        "target": hx, "peer": peer, "fscope": fs, "edges": {"relies": [dep]},
                        "signers": self.full(sorted(set(acc))) if r.random() < 0.85 else self.subset(acc)})
            prev_x = hx
        hr = self.h()
        edge = r.choice(["retires", "retires", "invalidates"])
        self.pending.append(lambda it2: [{"op": "cell", "h": hr, "origin": SCOPE, "kind": "axiom", "name": f"{SCOPE}/axiom.w{hr}",
                                          "edges": {edge: [hd]}, "signers": self.full(it2.roster()[0])}])
        return ops

    def rebind_chain(self, it: Interp) -> List[dict]:
        """V1 <- V2 <- V3 (+ maybe V4) under one name, then invalidate or retire one link."""
        r = self.r
        adm, _ = it.roster()
        name = f"{SCOPE}/axiom.c{self.n + 1}"
        hs = [self.h() for _ in range(r.randint(3, 4))]
        first = [{"op": "cell", "h": hs[0], "origin": SCOPE, "kind": "axiom", "name": name, "edges": {}, "signers": self.subset(adm)}]
        author = first[0]["signers"]
        for prev, h in zip(hs, hs[1:]):
            mode = r.random()

            def step(it2, prev=prev, h=h, mode=mode):
                adm2 = it2.roster()[0]
                if mode < 0.55:
                    sg = self.full(adm2)
                elif mode < 0.8:  # pending: one non-author key, then the author (or the rest) co-signs later
                    others = [k for k in adm2 if k not in author] or adm2
                    sg = [r.choice(others)]
                    self.pending.insert(r.randint(0, len(self.pending)), lambda it3: [
                        {"op": "seal", "target": h, "key": k, "ctx": None} for k in self.subset(it3.roster()[0])])
                else:
                    sg = self.subset(adm2)
                return [{"op": "cell", "h": h, "origin": SCOPE, "kind": "axiom", "name": name,
                         "edges": {"supersedes": [prev]}, "signers": sg}]
            self.pending.append(step)
        hx = self.h()
        edge = r.choice(["invalidates", "invalidates", "retires"])
        tgt = r.choice(hs[1:])
        self.pending.append(lambda it2: [{"op": "cell", "h": hx, "origin": SCOPE, "kind": "axiom", "name": f"{SCOPE}/axiom.x{hx}",
                                          "edges": {edge: [tgt]}, "signers": self.full(it2.roster()[0])}])
        return first

    def next_commit(self, it: Interp) -> List[dict]:
        r = self.r
        if self.pending and r.random() < 0.7:
            return self.pending.pop(0)(it)
        x = r.random()
        if x < 0.14:
            return self.bundle(it)
        if x < 0.24:
            return self.acc_chain(it)
        if x < 0.32:
            return self.rebind_chain(it)
        if x < 0.42:
            return self.attest_bundle(it)
        ops: List[dict] = []
        for _ in range(r.choice([1, 1, 2, 2, 3])):
            x = r.random()
            op = None
            if x < 0.45:
                op = self.local_cell(it)
            elif x < 0.6:
                op = self.foreign_cell(it) if r.random() < 0.7 else self.fscope(it)
            elif x < 0.67:
                op = self.fscope(it)
            elif x < 0.87:
                op = self.seal(it)
            elif x < 0.93:
                op = self.rotate(it)
            else:
                op = self.local_cell(it, "acceptance")
            if op is not None:
                ops.append(op)
        if sum(o["op"] == "rotate" for o in ops) > 1:
            ops = [o for o in ops if o["op"] != "rotate"] + [next(o for o in ops if o["op"] == "rotate")]
        return ops


# ---------------------------------------------------------------------------
# Oracles (written from VARS-1-SPEC.md §4, not from vars1.py)
# ---------------------------------------------------------------------------
def _origin(atoms, c: V.Cell) -> str:
    return V.parse_utf8(atoms[c.h_slot_name]).split("/", 1)[0]


def _items(atoms, h: bytes) -> List[bytes]:
    return [] if h == V.H_EMPTY else V.parse_hvec(atoms[h])


def _pol(atoms, h: bytes) -> Tuple[int, Set[bytes]]:
    thr, hv = V.parse_pol1(atoms[h])
    return thr, set(V.parse_hvec(atoms[hv]))


def oracle_edges(it: Interp, foreign_initial: bool = False) -> Set[Tuple[bytes, bytes, str]]:
    """Spec §4.1 latching rule 3 replayed over the interpreter's own commit log.

    Spec §4.1 defines InitialEndorsers(v) for local v only (here: empty for foreign v). `foreign_initial=True` instead
    uses vars1.py's reading (a foreign cell's birth endorsers under self-sealed scopes of its origin); it is used only
    to tell the known divergence class (i3_foreign_birth_signer_gets_local_author_eviction) from any other."""
    atoms = it.atoms
    latched: Set[Tuple[bytes, bytes, str]] = set()
    initial: Dict[bytes, Set[bytes]] = {}
    for rec in it.history:
        cells, s_id = rec["cells"], rec["scope"]
        s = cells[s_id]
        adm, acc = _pol(atoms, s.slots[0]), _pol(atoms, s.slots[1])

        def ends(u: bytes, pks: Set[bytes]) -> Set[bytes]:
            return {x.actor_pubkey for x in rec["seals"] if x.h_target == u and x.h_scope_ctx == s_id and x.actor_pubkey in pks}

        for v in rec["new"]:
            vc = cells[v]
            if v not in V.STD_SCHEMA_IDS and _origin(atoms, vc) == SCOPE:
                initial[v] = ends(v, acc[1] if vc.h_schema == V.H_SCHEMA["acceptance"] else adm[1])
            elif v not in V.STD_SCHEMA_IDS and foreign_initial:
                got: Set[bytes] = set()
                for fid, fc in cells.items():
                    if fc.h_schema != V.H_SCHEMA["scope"] or _origin(atoms, fc) != _origin(atoms, vc):
                        continue
                    fthr, fpks = _pol(atoms, fc.slots[0])
                    selfs = {x.actor_pubkey for x in rec["seals"] if x.h_target == fid and x.h_scope_ctx == fid and x.actor_pubkey in fpks}
                    if len(selfs) >= fthr:
                        got |= {x.actor_pubkey for x in rec["seals"] if x.h_target == v and x.h_scope_ctx == fid and x.actor_pubkey in fpks}
                initial[v] = got
        for wid, w in cells.items():
            if w.h_schema == V.H_META_SCHEMA:
                continue
            for kind, mh in (("invalidates", w.h_invalidates), ("retires", w.h_retires), ("supersedes", w.h_supersedes)):
                for vid in _items(atoms, mh):
                    if (wid, vid, kind) in latched:
                        continue
                    v = cells[vid]
                    sch = v.h_schema
                    if sch == V.H_SCHEMA["scope"] or (sch in (V.H_SCHEMA["contract"], V.H_SCHEMA["decision"]) and v.slots[0] == V.H_OWNER):
                        pol, author = adm, False
                    elif sch == V.H_SCHEMA["acceptance"]:
                        pol, author = acc, False
                    elif sch in (V.H_SCHEMA["contract"], V.H_SCHEMA["decision"]) and v.slots[0] == V.H_PROVISIONAL:
                        pol, author = (_pol(atoms, v.slots[3]) if v.slots[3] != V.H_EMPTY else adm), True
                    elif sch == V.H_SCHEMA["question"]:
                        pol, author = (_pol(atoms, v.slots[1]) if v.slots[1] != V.H_EMPTY else adm), True
                    else:
                        pol, author = adm, True
                    e = ends(wid, acc[1] if sch == V.H_SCHEMA["acceptance"] else adm[1])
                    ok = len(e & pol[1]) >= pol[0]
                    if not ok and kind != "invalidates" and author:
                        ok = bool(e & initial.get(vid, set()))
                    if ok:
                        latched.add((wid, vid, kind))
    return latched


def oracle_auth(it: Interp) -> Dict[str, Set[bytes]]:
    """Spec §4.1 latches 1, 2 and 4 replayed over the interpreter's own commit log (I3c).

    1. a local acceptance cell pinned to a self-sealed foreign scope whose Endorsers_i (seals under S_i by keys of
       S_i's acceptance policy) meet that policy is Authorized; 2. a local custom schema cell whose Endorsers_i (keys
       of S_i's admission policy) meet the admission policy is Authorized; 4. every governing scope is Authorized."""
    atoms = it.atoms
    out: Dict[str, Set[bytes]] = {"acc": set(), "schema": set(V.STD_SCHEMA_IDS), "scope": set()}
    for rec in it.history:
        cells, s_id, seals = rec["cells"], rec["scope"], rec["seals"]
        out["scope"].add(s_id)
        s = cells[s_id]
        adm, acc = _pol(atoms, s.slots[0]), _pol(atoms, s.slots[1])

        def ends(u: bytes, pks: Set[bytes]) -> Set[bytes]:
            return {x.actor_pubkey for x in seals if x.h_target == u and x.h_scope_ctx == s_id and x.actor_pubkey in pks}

        def self_sealed(f: bytes) -> bool:
            fc = cells.get(f)
            if fc is None or fc.h_schema != V.H_SCHEMA["scope"] or _origin(atoms, fc) == SCOPE:
                return False
            thr, pks = _pol(atoms, fc.slots[0])
            return len({x.actor_pubkey for x in seals if x.h_target == f and x.h_scope_ctx == f and x.actor_pubkey in pks}) >= thr

        for cid, c in cells.items():
            if cid in V.STD_SCHEMA_IDS or _origin(atoms, c) != SCOPE:
                continue
            if c.h_schema == V.H_SCHEMA["acceptance"]:
                if self_sealed(c.slots[1]) and len(ends(cid, acc[1])) >= acc[0]:
                    out["acc"].add(cid)
            elif c.h_schema == V.H_META_SCHEMA:
                if len(ends(cid, adm[1])) >= adm[0]:
                    out["schema"].add(cid)
    if it.cur is not None:
        out["scope"].add(it.ids[it.cur])
    return out


def oracle_stale(atoms, cells: Dict[bytes, V.Cell], active: Dict[bytes, bool], latched_acc: Set[bytes]) -> Dict[bytes, bool]:
    """Spec §4.2 Pass 2 least fixed point, computed by chaotic iteration with no round cap and no topological order."""
    refs: Dict[bytes, Set[bytes]] = {}
    for u, c in cells.items():
        out = set()
        for mh in (c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates):
            out.update(_items(atoms, mh))
        out.update(x for x in (c.h_payload, *c.slots) if x in cells)
        out.discard(u)
        refs[u] = out
    children: Dict[bytes, Set[bytes]] = {u: set() for u in cells}
    for u, vs in refs.items():
        for v in vs:
            children[v].add(u)
    origin = {u: _origin(atoms, c) for u, c in cells.items()}
    foreign = {u for u in cells if u not in V.STD_SCHEMA_IDS and origin[u] != SCOPE}
    stale = {u: False for u in cells}
    while True:
        live: Dict[bytes, Set[bytes]] = {u: set() for u in cells}
        changed = True
        while changed:
            changed = False
            for x in foreign:
                new = set(live[x])
                for a in children[x]:
                    ac = cells[a]
                    if (active.get(a) and not stale[a] and ac.h_schema == V.H_SCHEMA["acceptance"]
                            and a in latched_acc and ac.h_payload == x):
                        new.add(ac.slots[1])
                    if origin[a] == origin[x] and a in foreign:
                        new |= live[a]
                if new != live[x]:
                    live[x] = new
                    changed = True
        nxt = {}
        for u, c in cells.items():
            if not active.get(u):
                nxt[u] = False
                continue
            dep = any(not active.get(d) or stale[d] for d in _items(atoms, c.h_relies))
            nxt[u] = dep or (u in foreign and not live[u])
        if nxt == stale:
            return stale
        stale = {u: stale[u] or nxt[u] for u in cells}


def full_replay_term_hash(ck: V.Cell, atoms) -> Optional[bytes]:
    """Replay a checkpoint from its ComputationRoot in one advance (no parent trust). Returns its NF term_hash."""
    try:
        root = json.loads(atoms[ck.slots[0]].decode())
        envd = json.loads(atoms[bytes.fromhex(root["environment_id"])].decode())
        env = SR.Environment([bytes.fromhex(h) for h in envd["hashes"]], atoms)
        doc, sid, sb = SR.start(ck.slots[0].hex(), bytes.fromhex(root["input_term_hash"]))
        spent = V.parse_u64(atoms[ck.slots[2]])
        res = SR.advance(doc, sid, sb, env, spent, SR.G.VERIFIER_LIMITS, root["runtime_semantics_id"])
        if res.outcome != SR.NORMAL_FORM or res.state_bytes != atoms[ck.h_payload] or res.checkpoint["spent_total"] != spent:
            return None
        return V.sgs1_term_hash(res.state_bytes)[1]
    except Exception:  # noqa: BLE001
        return None


# ---------------------------------------------------------------------------
# Invariant checks on one admitted tip
# ---------------------------------------------------------------------------
EXEC_BIN = Path(__file__).resolve().parent / "proofs" / ".lake" / "build" / "bin" / "vars1exec"
_EXEC: Optional[subprocess.Popen] = None


def exec_facts(kernel_input: bytes, kernel_output: bytes) -> Tuple[str, bytes]:
    """The facts line for `vars1exec` (proofs/Vars1/Exec.lean), read only from the kernel's own input and output:
    cell structure from the input, `Authorized` and per-edge authorization from the fold's output. Returns the
    line and the kernel's status bytes."""
    words = lambda off, k=1: struct.unpack_from(f"<{k}I", kernel_input, off)
    off = 0
    C, N, NK, P = words(0, 4); off = 16
    for _ in range(P):
        off += 32
        _thr, m = words(off, 2); off += 8 + 4 * m
    cells = []
    for _ in range(N):
        cid, schema, payload, _name, _loss = (kernel_input[off + 32 * i: off + 32 * (i + 1)] for i in range(5)); off += 160
        origin, _birth, K = words(off, 3); off += 12
        slots = [kernel_input[off + 32 * i: off + 32 * (i + 1)] for i in range(K)]; off += 32 * K
        edges = []
        for _ in range(5):
            (cnt,) = words(off); off += 4
            edges.append(list(words(off, cnt)) if cnt else []); off += 4 * cnt
        cells.append((cid, schema, payload, origin, slots, edges))
    index = {c[0]: i for i, c in enumerate(cells)}
    # `KernelRunner.run` returns the output after its length word: scope index, statuses, Authorized, edge latches
    status = kernel_output[4:4 + N]
    auth = kernel_output[4 + N:4 + 2 * N]
    flags = kernel_output[4 + 2 * N:]
    pos = 0
    parts = [str(N)]
    for i, (cid, schema, payload, origin, slots, edges) in enumerate(cells):
        rel, _att, sup, ret, inv = edges
        latch = {}
        for kind, lst in (("inv", inv), ("ret", ret), ("sup", sup)):
            latch[kind] = [(d, flags[pos + j]) for j, d in enumerate(lst)]
            pos += len(lst)
        is_verdict = schema == V.H_SCHEMA["verdict"]
        pay = index.get(payload)
        refs = sorted({*rel, *edges[1], *sup, *ret, *inv, *(x for x in [pay] if x is not None),
                       *(index[h] for h in slots if h in index)})
        parts += [str(int(origin == 0 or cid in V.STD_SCHEMA_IDS)), str(int(schema == V.H_SCHEMA["acceptance"])),
                  str(int(is_verdict)), str(int(is_verdict and len(slots) > 1 and slots[1] == V.H_VERDICT_INVALID)),
                  str(origin), str(auth[i]), str(0 if pay is None else pay + 1),
                  str(len(rel)), *map(str, rel), str(len(refs)), *map(str, refs)]
        for kind in ("sup", "ret", "inv"):
            parts.append(str(len(latch[kind])))
            for d, a in latch[kind]:
                parts += [str(d), str(a)]
    return " ".join(parts), bytes(status)


def exec_statuses(line: str) -> List[int]:
    global _EXEC
    if _EXEC is None:
        if not EXEC_BIN.exists():
            raise RuntimeError("build the executable lens first: cd proofs && lake build vars1exec")
        _EXEC = subprocess.Popen([str(EXEC_BIN)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    _EXEC.stdin.write(line + "\n")
    _EXEC.stdin.flush()
    out = _EXEC.stdout.readline().strip()
    if out == "E" or not out:
        raise RuntimeError(f"vars1exec rejected the facts line ({out or 'no output'})")
    return [int(x) for x in out.split()]


FOLD_BIN = Path(__file__).resolve().parent / "proofs" / ".lake" / "build" / "bin" / "vars1fold"
_FOLD: Optional[subprocess.Popen] = None


def fold_facts(kernel_input: bytes) -> str:
    """The input line for `vars1fold` (the model's own fold, `proofs/Vars1/Fold.lean`), read only from the kernel's
    input: policies, cell kinds and policy slots, edges, births, and the verified seals with their first commit."""
    words = lambda off, k=1: struct.unpack_from(f"<{k}I", kernel_input, off)
    C, N, NK, P = words(0, 4); off = 16
    pols, pol_ix = [], {}
    for i in range(P):
        pid = kernel_input[off:off + 32]; off += 32
        thr, m = words(off, 2); off += 8
        keys = list(words(off, m)) if m else []; off += 4 * m
        pol_ix[pid] = i
        pols.append((thr, keys))
    codes = {V.H_SCHEMA["scope"]: 1, V.H_SCHEMA["acceptance"]: 2, V.H_SCHEMA["contract"]: 3,
             V.H_SCHEMA["decision"]: 4, V.H_SCHEMA["question"]: 5, V.H_SCHEMA["verdict"]: 6, V.H_META_SCHEMA: 7}
    cells, g = [], None
    for i in range(N):
        cid, schema = kernel_input[off:off + 32], kernel_input[off + 32:off + 64]; off += 160
        origin, birth, K = words(off, 3); off += 12
        slots = [kernel_input[off + 32 * j: off + 32 * (j + 1)] for j in range(K)]; off += 32 * K
        edges = []
        for _ in range(5):
            (cnt,) = words(off); off += 4
            edges.append(list(words(off, cnt)) if cnt else []); off += 4 * cnt
        code = codes.get(schema, 0)
        pol = lambda h: 0 if h == V.H_EMPTY or h not in pol_ix else pol_ix[h] + 1
        owner = code in (3, 4) and slots[0] == V.H_OWNER
        custom = pol(slots[3]) if code in (3, 4) else pol(slots[1]) if code == 5 else 0
        p0, p1 = (pol(slots[0]), pol(slots[1])) if code == 1 else (0, 0)
        if code == 1 and origin == 0 and birth == 0:
            g = i
        cells.append([code, int(origin == 0), int(cid in V.STD_SCHEMA_IDS), birth, int(owner), custom, p0, p1,
                      edges[2], edges[3], edges[4]])
    (S,) = words(off); off += 4
    seals = [words(off + 16 * j, 4) for j in range(S)]
    parts = [N, P, C, S, g]
    for thr, keys in pols:
        parts += [thr, len(keys), *keys]
    for c in cells:
        parts += c[:8]
        for lst in c[8:]:
            parts += [len(lst), *lst]
    for t in seals:
        parts += list(t)
    return " ".join(map(str, parts))


def model_fold(line: str) -> List[int]:
    global _FOLD
    if _FOLD is None:
        if not FOLD_BIN.exists():
            raise RuntimeError("build the model fold first: cd proofs && lake build vars1fold")
        _FOLD = subprocess.Popen([str(FOLD_BIN)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    _FOLD.stdin.write(line + "\n")
    _FOLD.stdin.flush()
    out = _FOLD.stdout.readline().strip()
    if out == "E" or not out:
        raise RuntimeError(f"vars1fold rejected the facts line ({out or 'no output'})")
    return [int(x) for x in out.split()]


_RUNNER: Optional["V.KernelRunner"] = None


def kernel_runner() -> "V.KernelRunner":
    global _RUNNER
    if _RUNNER is None:
        _RUNNER = V.KernelRunner()
    return _RUNNER


def check_tip(it: Interp, prev_latches: Optional[Dict[str, Set]], rng: random.Random, shuffles: int = 1):
    """Return (violations, latches). violations: list of (invariant_id, detail)."""
    out: List[Tuple[str, str]] = []
    try:
        fold = it.repo._evaluate_commit_chain(SCOPE, it.repo.commit_chain(it.tip))
        lens = it.repo.lens(SCOPE)
    except V.VarsError as e:
        return [("I0", f"lens/fold raised VarsError on an admitted tip: {e}")], prev_latches
    except Exception as e:  # noqa: BLE001
        return [("I0", f"lens/fold crashed: {type(e).__name__}: {e}")], prev_latches
    cells, atoms, active = lens["cells"], lens["atoms"], lens["active"]

    # I8: a fresh run of the rules kernel (kernel/lens.wasm) reproduces the lens's Passes 1-2
    try:
        for cid, bits in kernel_runner().statuses(lens).items():
            bad = [n for n, v in bits.items() if lens[n][cid] != v]
            if bad:
                out.append(("I8", f"kernel disagrees on {bad} of {cid.hex()[:10]}"))
                break
    except V.VarsError as e:
        out.append(("I8", str(e)))

    # I9: the proved executable lens (proofs/Vars1/Exec.lean, compiled) computes the kernel's own status bytes
    # from the kernel's input and its fold's authority output
    raw = kernel_runner().run(lens["kernel_input"])
    line, kstatus = exec_facts(lens["kernel_input"], raw)
    estatus = exec_statuses(line)
    # I10: the model's own fold (proofs/Vars1/Fold.lean, compiled) reproduces the kernel's scope, Authorized bits and
    # edge authorizations from the kernel's input
    n = len(kstatus)
    mfold = model_fold(fold_facts(lens["kernel_input"]))
    kfold = [int.from_bytes(raw[:4], "little"), *raw[4 + n:4 + 2 * n], *raw[4 + 2 * n:]]
    if mfold != kfold:
        i = next((i for i, (a, b) in enumerate(zip(mfold, kfold)) if a != b), min(len(mfold), len(kfold)))
        what = "scope" if i == 0 else f"Authorized of cell {i - 1}" if i <= n else f"edge latch {i - 1 - n}"
        out.append(("I10", f"model fold disagrees with the kernel on {what}: model={mfold[i:i+1]} kernel={kfold[i:i+1]}"))
    if list(kstatus) != estatus:
        i = next(i for i, (a, b) in enumerate(zip(kstatus, estatus)) if a != b)
        out.append(("I9", f"Lean exec disagrees with the kernel at cell {i}: kernel={kstatus[i]} exec={estatus[i]}"))

    # I11: a client's Pass 3 from the kernel input and output alone equals the lens's Settled
    try:
        ki = V.parse_kernel_input(lens["kernel_input"])
        for i, kcell in enumerate(ki["cells"]):
            c = cells[kcell["id"]]
            if c.h_schema not in (V.H_SCHEMA["contract"], V.H_SCHEMA["decision"]) or c.slots[1] != V.H_EMPTY:
                continue
            got = V.pass3_at_tip(ki, raw, i)[0]
            if got != lens["settled"][kcell["id"]]:
                out.append(("I11", f"client Pass 3 says {got}, lens Settled {lens['settled'][kcell['id']]} "
                                   f"for {kcell['id'].hex()[:10]}"))
                break
    except V.VarsError as e:
        out.append(("I11", f"client Pass 3 raised: {e}"))

    # I1
    by_name: Dict[bytes, List[bytes]] = {}
    for cid, c in cells.items():
        if cid not in V.STD_SCHEMA_IDS and _origin(atoms, c) == SCOPE and active[cid]:
            by_name.setdefault(c.h_slot_name, []).append(cid)
    for nm, cids in by_name.items():
        if len(cids) > 1:
            out.append(("I1", f"{len(cids)} Active bindings of {V.parse_utf8(atoms[nm])!r}: {[x.hex()[:10] for x in cids]}"))

    # I2
    st = oracle_stale(atoms, cells, active, set(fold["latched_acc_auth"]))
    diff = sorted(cid.hex()[:10] + ("+" if st[cid] else "-") for cid in cells if st[cid] != lens["stale"][cid])
    if diff:
        out.append(("I2", f"Stale differs from the LFP oracle (+ oracle Stale, - oracle fresh): {diff}"))

    # I3 / I3b
    oe = oracle_edges(it)
    le = set(fold["latched_edge_auth"])
    oe_f = oracle_edges(it, foreign_initial=True) if oe != le else oe
    known_tag = " [explained by foreign InitialEndorsers]"
    for cid in cells:
        if active[cid]:
            for vid in _items(atoms, cells[cid].h_supersedes):
                if (cid, vid, "supersedes") not in oe:
                    tag = known_tag if (cid, vid, "supersedes") in oe_f and oe_f == le else ""
                    out.append(("I3", f"Active {cid.hex()[:10]} supersedes {vid.hex()[:10]} without spec authorization{tag}"))
    if oe != le:
        fmt = lambda s: sorted(f"{w.hex()[:8]}-{k[:3]}->{v.hex()[:8]}" for w, v, k in s)  # noqa: E731
        tag = known_tag if oe_f == le else ""
        out.append(("I3b", f"latched edges != spec oracle; impl-only {fmt(le - oe)} oracle-only {fmt(oe - le)}{tag}"))

    # I3c: acceptance, custom-schema and scope latches equal the spec oracle
    oa = oracle_auth(it)
    for k, fk in (("acc", "latched_acc_auth"), ("schema", "latched_schema_auth"), ("scope", "latched_scope_auth")):
        got = set(fold[fk])
        if got != oa[k]:
            fmt = lambda xs: sorted(x.hex()[:10] for x in xs)  # noqa: E731
            out.append(("I3c", f"{k} latches != spec oracle; impl-only {fmt(got - oa[k])} oracle-only {fmt(oa[k] - got)}"))

    # I4
    for cid, c in cells.items():
        if not lens["settled"].get(cid) or c.h_schema not in (V.H_SCHEMA["contract"], V.H_SCHEMA["decision"]):
            continue
        req, exp = c.slots[1], c.slots[2]
        if req == V.H_EMPTY:
            continue
        ok = False
        for wid, w in cells.items():
            if (w.h_schema == V.H_SCHEMA["verdict"] and w.h_payload == cid and cid in _items(atoms, w.h_attests)
                    and w.slots[1] == V.H_REPLAYED and active[wid] and not lens["stale"][wid] and w.slots[0] in cells):
                ck = cells[w.slots[0]]
                if (ck.h_schema == V.H_SCHEMA["checkpoint"] and ck.slots[0] == req and active[w.slots[0]]
                        and not lens["stale"][w.slots[0]] and full_replay_term_hash(ck, atoms) == exp):
                    ok = True
        if not ok:
            out.append(("I4", f"Settled {cid.hex()[:10]} has no fully-replayable REPLAYED witness with term_hash == expected"))

    # I7: the scope the fold governs with is the one Active local scope cell
    act_scopes = [cid for cid, c in cells.items() if c.h_schema == V.H_SCHEMA["scope"] and _origin(atoms, c) == SCOPE and active[cid]]
    if act_scopes != [fold["active_scope_id"]]:
        out.append(("I7", f"fold governs with {fold['active_scope_id'].hex()[:10]} but Active local scopes are "
                          f"{[x.hex()[:10] for x in act_scopes]}"))

    # I5
    latches = fold_latches(fold)
    if prev_latches is not None:
        for k, prev in prev_latches.items():
            lost = prev - latches[k]
            if lost:
                out.append(("I5", f"{len(lost)} {k} latch(es) unlatched"))

    # I6 (in-process dict order)
    base = lens_digest(lens)
    for _ in range(shuffles):
        srepo = MemoRepo(it.path, shuffle_rng=random.Random(rng.random()), shared=it.repo._tree_memo)
        try:
            other = lens_digest(srepo.lens(SCOPE))
        except Exception as e:  # noqa: BLE001
            out.append(("I6", f"lens under shuffled dict order raised {type(e).__name__}: {e}"))
            break
        if other != base:
            d = {k: (sorted(set(base[k]) ^ set(other[k]))) for k in STATUS_KEYS if base[k] != other[k]}
            out.append(("I6", f"lens depends on dict order: {d}"))
            break
    return out, latches


# ---------------------------------------------------------------------------
# Runner + shrinker
# ---------------------------------------------------------------------------
def run_program(program: List[List[dict]], seed: int = 0, shuffles: int = 1, stop_at_first: bool = True):
    """Execute `program`; check invariants on each admitted tip. Returns (violations, interp, tmpdir)."""
    tmp = tempfile.TemporaryDirectory()
    it = Interp(Path(tmp.name))
    rng = random.Random(seed ^ 0x5EED)
    prev = None
    viols: List[Tuple[int, str, str]] = []
    for i, ops in enumerate(program):
        admitted = it.exec_commit(ops)
        viols += [(i, "I0", c) for c in it.crashes]
        it.crashes.clear()
        if not admitted:
            continue
        vs, prev = check_tip(it, prev, rng, shuffles)
        viols += [(i, a, b) for a, b in vs]
        if viols and stop_at_first:
            break
    return viols, it, tmp


def generate(seed: int, n_commits: int, shuffles: int = 1):
    """Generate a program interleaved with execution; stop at the first violation."""
    rng = random.Random(seed)
    g = Gen(rng)
    tmp = tempfile.TemporaryDirectory()
    it = Interp(Path(tmp.name))
    program: List[List[dict]] = []
    ops = g.genesis()
    if not it.exec_commit(ops):
        tmp.cleanup()
        raise AssertionError(f"seed {seed}: generated genesis rejected: {ops}")
    program.append(ops)
    prev = None
    crng = random.Random(seed ^ 0x5EED)
    vs, prev = check_tip(it, prev, crng, shuffles)
    if vs:
        return program, vs, it, tmp
    soft: List[Tuple[str, str]] = []
    for _ in range(n_commits):
        ops = g.next_commit(it)
        if not ops:
            continue
        admitted = it.exec_commit(ops)
        if it.crashes:  # keep exploring past a gate crash; the failing commit joins the program for shrinking
            if not soft:
                program.append(ops)
                return_soft_at = len(program)
            soft += [("I0", c) for c in it.crashes]
            it.crashes.clear()
        if not admitted:
            continue
        program.append(ops)
        vs, prev = check_tip(it, prev, crng, shuffles)
        if vs:
            return program, soft + vs, it, tmp
    if soft:  # shrink the gate crash on the prefix that produced it
        return program[:return_soft_at], soft, it, tmp
    return program, [], it, tmp


def _fails_with(program, inv: str) -> bool:
    viols, _, tmp = run_program(program, shuffles=3 if inv == "I6" else 0)
    tmp.cleanup()
    return any(v[1] == inv for v in viols)


def shrink(program: List[List[dict]], inv: str, budget: int = 400) -> List[List[dict]]:
    """Greedy delta-debugging: drop commits, ops, then list elements (signers, edges), keeping `inv` failing."""
    best = copy.deepcopy(program)
    tries = 0

    def attempt(cand) -> bool:
        nonlocal best, tries
        tries += 1
        if tries > budget:
            return False
        if _fails_with(cand, inv):
            best = cand
            return True
        return False

    progress = True
    while progress and tries <= budget:
        progress = False
        for i in range(len(best) - 1, 0, -1):  # keep genesis
            if i < len(best) and attempt(best[:i] + best[i + 1:]):
                progress = True
        for i in range(len(best) - 1, -1, -1):
            for j in range(len(best[i]) - 1, -1, -1):
                if i < len(best) and j < len(best[i]) and len(best[i]) > 1:
                    cand = copy.deepcopy(best)
                    del cand[i][j]
                    if attempt(cand):
                        progress = True
        for i in range(len(best)):
            for j in range(len(best[i])):
                op = best[i][j]
                lists = [("signers", None)] + [("edges", k) for k in op.get("edges", {})]
                for field, sub in lists:
                    seq = op.get(field, []) if sub is None else op["edges"].get(sub, [])
                    for x in range(len(seq) - 1, -1, -1):
                        cand = copy.deepcopy(best)
                        tgt = cand[i][j][field] if sub is None else cand[i][j]["edges"][sub]
                        del tgt[x]
                        if attempt(cand):
                            progress = True
                            op = best[i][j]
    return best


def hashseed_digests(repo_dir: Path, seeds=(0, 1, 2)) -> List[str]:
    outs = []
    for s in seeds:
        res = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--lens-digest", str(repo_dir)],
            env={**os.environ, "PYTHONHASHSEED": str(s)}, capture_output=True, text=True, check=False,
        )
        outs.append(res.stdout.strip() if res.returncode == 0 else f"ERR {res.stderr.strip()[-300:]}")
    return outs


# ---------------------------------------------------------------------------
# Shrunk regression programs found by the generator (each FAILS on vars1.py @ f69313a; see report)
# ---------------------------------------------------------------------------
REGRESSIONS: Dict[str, Tuple[str, List[List[dict]]]] = {
    # I7: A foreign schema.scope cell may list the local governing scope in H_supersedes (the gate's rule only asks that a scope be superseded by *a* scope). One local cross-seal plus an ACCEPTANCE of that foreign scope latches the edge, so Pass 1 marks the governing scope Superseded while the fold keeps governing with it: the lens shows no Active local scope.
    'i7_foreign_scope_supersedes_governing_scope': ('I7',
        [[{'op': 'genesis', 'h': 'h1', 'adm': [0], 'adm_thr': 1, 'acc': [0], 'acc_thr': 1, 'signers': [0]}],
         [{'op': 'fscope',
           'h': 'h2',
           'peer': 'peerB',
           'keys': [3],
           'thr': 1,
           'signers': [3],
           'edges': {'supersedes': ['h1']}},
          {'op': 'seal', 'target': 'h2', 'key': 0, 'ctx': None},
          {'op': 'cell',
           'h': 'h3',
           'origin': 'core',
           'kind': 'acceptance',
           'name': 'core/acceptance.0',
           'target': 'h2',
           'peer': 'peerB',
           'fscope': 'h2',
           'edges': {},
           'signers': [0]}]]),
    # I3: A key in both the local roster (2-of-2) and peerB's scope signs a peerB cell, then alone signs a local cell superseding it. vars1.py stores foreign birth endorsers as InitialEndorsers, so AuthorCanEvict latches the edge; spec §4.1 defines InitialEndorsers for local cells only, so the 2-of-2 policy should be needed.
    'i3_foreign_birth_signer_gets_local_author_eviction': ('I3',
        [[{'op': 'genesis', 'h': 'h1', 'adm': [1, 2], 'adm_thr': 2, 'acc': [2], 'acc_thr': 1, 'signers': [1, 2]}],
         [{'op': 'fscope', 'h': 'h2', 'peer': 'peerB', 'keys': [2, 3], 'thr': 1, 'signers': [3]},
          {'op': 'cell',
           'h': 'h3',
           'origin': 'peerB',
           'kind': 'axiom',
           'name': 'peerB/axiom.h3',
           'ctx': 'h2',
           'edges': {},
           'signers': [2]}],
         [{'op': 'cell',
           'h': 'h5',
           'origin': 'core',
           'kind': 'axiom',
           'name': 'core/axiom.0',
           'edges': {'supersedes': ['h3']},
           'signers': [2]}]]),
    # I0: Slot types are not checked. A foreign contract whose evaluator_policy slot is an intrinsic hash (H_K) is admitted; once ACCEPTED, every lens() call at that tip raises KeyError in Pass 3.
    'i0_foreign_contract_untyped_policy_breaks_lens': ('I0',
        [[{'op': 'genesis', 'h': 'h1', 'adm': [0], 'adm_thr': 1, 'acc': [0], 'acc_thr': 1, 'signers': [0]}],
         [{'op': 'fscope', 'h': 'h2', 'peer': 'peerB', 'keys': [3], 'thr': 1, 'signers': [3]},
          {'op': 'cell',
           'h': 'h3',
           'origin': 'peerB',
           'kind': 'contract',
           'name': 'peerB/contract.h3',
           'ctx': 'h2',
           'tier': 'provisional',
           'req': None,
           'exp': 'EMPTY',
           'pol': None,
           'edges': {},
           'signers': [],
           'bad': {'slot': 3, 'val': 'K'}},
          {'op': 'cell',
           'h': 'h4',
           'origin': 'core',
           'kind': 'acceptance',
           'name': 'core/acceptance.0',
           'target': 'h3',
           'peer': 'peerB',
           'fscope': 'h2',
           'edges': {},
           'signers': [0]}]]),
    # I0: As above with a UTF8 atom in evaluator_policy: admitted, then lens() raises VarsError('invalid POL1 atom') at every call on that tip.
    'i0_foreign_contract_non_pol1_policy_breaks_lens': ('I0',
        [[{'op': 'genesis', 'h': 'h1', 'adm': [0], 'adm_thr': 1, 'acc': [0], 'acc_thr': 1, 'signers': [0]}],
         [{'op': 'fscope', 'h': 'h2', 'peer': 'peerB', 'keys': [3], 'thr': 1, 'signers': [3]},
          {'op': 'cell',
           'h': 'h3',
           'origin': 'peerB',
           'kind': 'contract',
           'name': 'peerB/contract.h3',
           'ctx': 'h2',
           'tier': 'provisional',
           'req': None,
           'exp': 'EMPTY',
           'pol': None,
           'edges': {},
           'signers': [],
           'bad': {'slot': 3, 'val': 'utf8'}},
          {'op': 'cell',
           'h': 'h4',
           'origin': 'core',
           'kind': 'acceptance',
           'name': 'core/acceptance.0',
           'target': 'h3',
           'peer': 'peerB',
           'fscope': 'h2',
           'edges': {},
           'signers': [0]}]]),
    # I0: A local contract with an intrinsic hash in evaluator_policy makes the gate raise KeyError instead of VarsError.
    'i0_local_contract_untyped_policy_keyerror_at_gate': ('I0',
        [[{'op': 'genesis', 'h': 'h1', 'adm': [0], 'adm_thr': 1, 'acc': [0], 'acc_thr': 1, 'signers': [0]}],
         [{'op': 'cell',
           'h': 'h2',
           'origin': 'core',
           'kind': 'contract',
           'name': 'core/contract.x',
           'tier': 'provisional',
           'req': None,
           'exp': 'EMPTY',
           'pol': None,
           'edges': {},
           'signers': [0],
           'bad': {'slot': 3, 'val': 'K'}}]]),
    # I0: A checkpoint whose computation_id is a UTF8 atom (and whose SGS1 state carries the same id) makes the gate raise json.JSONDecodeError instead of VarsError; it fires in Check #4, before any seal is checked, so an unsigned commit triggers it.
    'i0_checkpoint_non_root_computation_id_jsondecodeerror_at_gate': ('I0',
        [[{'op': 'genesis', 'h': 'h1', 'adm': [0], 'adm_thr': 1, 'acc': [0], 'acc_thr': 1, 'signers': [0]}],
         [{'op': 'cell',
           'h': 'h2',
           'origin': 'core',
           'kind': 'checkpoint',
           'name': 'core/checkpoint.x',
           'variant': 'h_nf',
           'edges': {},
           'signers': [],
           'bad': {'slot': 0, 'val': 'utf8'}}]]),
}

# Violation classes already frozen as regressions above: (invariant, regex on the detail). The random test fails
# Only on violations matching none of these, so a new class is never hidden behind a known one.
KNOWN_SIGNATURES: List[Tuple[str, str]] = []  # every frozen class is fixed; any hit is a new violation


def is_known(inv: str, detail: str) -> bool:
    return any(inv == k and re.search(rx, detail) for k, rx in KNOWN_SIGNATURES)


class TestVars1Properties(unittest.TestCase):
    N_SEQS = int(os.environ.get("VARS1_PBT_SEQS", "36"))
    N_COMMITS = int(os.environ.get("VARS1_PBT_COMMITS", "10"))
    SEED0 = int(os.environ.get("VARS1_PBT_SEED", "1"))

    def test_random_admission_sequences(self) -> None:
        """I0..I11 on every admitted tip of N seeded random sequences (+ PYTHONHASHSEED check on a sample)."""
        found: Dict[str, List[str]] = {}
        known_hits: Dict[str, int] = {}
        admitted_total = 0
        sample_repos = []
        for seed in range(self.SEED0, self.SEED0 + self.N_SEQS):
            program, vs, it, tmp = generate(seed, self.N_COMMITS)
            admitted_total += len(program)
            for inv, detail in vs:
                if is_known(inv, detail):
                    known_hits[inv] = known_hits.get(inv, 0) + 1
                else:
                    found.setdefault(inv, []).append(f"seed {seed}: {detail}")
            if len(sample_repos) < 3 and len(program) >= 6 and not vs:
                sample_repos.append((seed, tmp))
            else:
                tmp.cleanup()
        for seed, tmp in sample_repos:
            ds = hashseed_digests(Path(tmp.name))
            if len(set(ds)) != 1:
                found.setdefault("I6", []).append(f"seed {seed}: lens differs across PYTHONHASHSEED 0/1/2")
            tmp.cleanup()
        if known_hits:
            print(f"\n  known (frozen) violation classes hit: {known_hits}", file=sys.stderr)
        self.assertGreater(admitted_total, self.N_SEQS * 3, "generator admits too few commits to be meaningful")
        self.assertEqual(found, {}, "new invariant violations (shrink with VARS1_PBT_SHRINK=1)")


def _make_regression(name: str, inv: str, program):
    def test(self) -> None:
        viols, _, tmp = run_program(program, shuffles=3 if inv == "I6" else 0)
        tmp.cleanup()
        self.assertEqual(viols, [], f"{name}: {inv} or another invariant violated")
    test.__name__ = f"test_regression_{name}"
    test.__doc__ = f"{inv}: shrunk counterexample {name}"
    return test


def _install_regressions() -> None:
    for name, (inv, program) in REGRESSIONS.items():
        # These shrunk counterexamples must now hold their invariant.
        setattr(TestVars1Properties, f"test_regression_{name}", _make_regression(name, inv, program))


def _lens_digest_main(repo_dir: str) -> None:
    repo = V.GitVarsRepo(repo_dir)
    print(json.dumps(lens_digest(repo.lens(SCOPE)), sort_keys=True))


def _explore_main() -> None:
    """VARS1_PBT_SHRINK=1: run seeds, shrink the first violation per invariant, print programs as JSON."""
    n = int(os.environ.get("VARS1_PBT_SEQS", "200"))
    seed0 = int(os.environ.get("VARS1_PBT_SEED", "1"))
    commits = int(os.environ.get("VARS1_PBT_COMMITS", "10"))
    seen: Dict[str, int] = {}
    for seed in range(seed0, seed0 + n):
        program, vs, _, tmp = generate(seed, commits)
        tmp.cleanup()
        firsts = {}
        for inv, detail in vs:
            firsts.setdefault(("known " if is_known(inv, detail) else "") + inv, (inv, detail))
        for key, (inv, detail) in firsts.items():
            seen[key] = seen.get(key, 0) + 1
            if seen[key] > int(os.environ.get("VARS1_PBT_PER_INV", "2")) or key.startswith("known"):
                continue
            small = shrink(program, inv)
            viols, _, t2 = run_program(small, shuffles=3 if inv == "I6" else 0)
            t2.cleanup()
            print(json.dumps({"seed": seed, "inv": inv, "detail": detail,
                              "shrunk_detail": [v[2] for v in viols if v[1] == inv][:1],
                              "program": small}), flush=True)
    print(json.dumps({"summary": seen}), flush=True)


_install_regressions()

if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--lens-digest":
        _lens_digest_main(sys.argv[2])
    elif os.environ.get("VARS1_PBT_SHRINK"):
        _explore_main()
    else:
        unittest.main(verbosity=2)
