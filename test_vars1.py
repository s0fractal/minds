#!/usr/bin/env python3
"""Conformance suite for `vars1.py` (VARS-1-SPEC.md).

Every fold and `lens()` runs the rules kernel (`kernel/lens.wasm`) and its Python twin, which must agree bit for bit;
every `lens()` is also re-run on a separate kernel instance.
Covers golden vectors, the gate's rejections, the local compute/checkpoint/verdict loop, rebinding and rollback,
foreign import and acceptance, scope rotation without retroactivity, replay trust, and all Ed25519 vectors of
`vectors/verify-sig.json` (from primitives, see vectors/SOURCE).
"""
from __future__ import annotations

import dataclasses
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT_DIR))

import sigma_glyph as SG  # noqa: E402
import sigma_resume as SR  # noqa: E402
import vars1 as V  # noqa: E402


class KernelCheckedRepo(V.GitVarsRepo):
    """Every lens() is re-run on a separate instance of the rules it names (kernel/lens.wasm, or kernel2/lens2.wasm
    for a v2 epoch): Passes 1-2 must reproduce."""

    runners: "dict[bytes, V.KernelRunner]" = {}

    def lens(self, scope: str):
        out = super().lens(scope)
        if out["rules"] not in KernelCheckedRepo.runners:
            KernelCheckedRepo.runners[out["rules"]] = V.KernelRunner(out["rules"])
        for cid, bits in KernelCheckedRepo.runners[out["rules"]].statuses(out).items():
            for name, val in bits.items():
                if out[name][cid] != val:
                    raise AssertionError(f"kernel disagrees on {name} of {cid.hex()[:12]}: python={out[name][cid]} wasm={val}")
        return out


class TestVars1Conformance(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.repo_path = Path(self.tmp.name)
        subprocess.run(["git", "-C", str(self.repo_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(self.repo_path), "config", "user.name", "vars-test"], check=True)
        subprocess.run(["git", "-C", str(self.repo_path), "config", "user.email", "vars@test.local"], check=True)
        self.repo = KernelCheckedRepo(self.repo_path)

        # Deterministic Ed25519 keys for actors k1, k2, peerB
        self.sk1 = b"\x01" * 32
        self.pk1 = V.ed25519_pubkey(self.sk1)
        self.sk2 = b"\x02" * 32
        self.pk2 = V.ed25519_pubkey(self.sk2)
        self.sk_peer = b"\x03" * 32
        self.pk_peer = V.ed25519_pubkey(self.sk_peer)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def _put_atom(self, atoms: dict[bytes, bytes], raw: bytes) -> bytes:
        h = V.sha256(raw)
        atoms[h] = raw
        return h

    def _bootstrap_genesis(
        self, scope: str = "core", adm_threshold: int = 1, acc_threshold: int = 2
    ) -> tuple[str, V.Cell, dict[bytes, bytes]]:
        atoms = dict(V.STD_SCHEMA_ATOMS)
        cells = list(V.STD_SCHEMAS.values())

        h_pks = self._put_atom(atoms, V.atom_hvec([self.pk1, self.pk2]))
        h_adm_pol = self._put_atom(atoms, V.atom_pol1(adm_threshold, h_pks))
        h_acc_pol = self._put_atom(atoms, V.atom_pol1(acc_threshold, h_pks))
        h_rules = V.H_LENS_KERNEL
        h_scope_str = self._put_atom(atoms, V.atom_utf8(scope))
        h_scope_slot = self._put_atom(atoms, V.atom_utf8(f"{scope}/SCOPE"))

        s0 = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=h_scope_slot,
            h_payload=h_scope_str,
            slots=(h_adm_pol, h_acc_pol, h_rules),
        )
        cells.append(s0)
        seals = [V.Seal.sign(self.sk1, s0.id, s0.id)]
        if adm_threshold >= 2:
            seals.append(V.Seal.sign(self.sk2, s0.id, s0.id))
        c0 = self.repo.build_candidate_commit(scope, atoms, cells, seals, parent_commit=None)
        self.repo.admit_and_advance(scope, c0, expected_old=None)
        return c0, s0, atoms

    def test_01_golden_test_vectors(self) -> None:
        self.assertEqual(V.H_EMPTY.hex(), "f7607964cdb9f811072ded78efc20c622f54483eb7b101da5605329dc908872e")
        self.assertEqual(V.H_META_SCHEMA.hex(), "7f0f250c08d367c8f2ba2c3b700f1a9bacbb44c240dade81c5c39c9ea7f9f15e")
        self.assertEqual(V.H_ZERO.hex(), "bd8ce1f0a5c552141dc052a9b66a200003a1b34dbf947dea1c1e32b9969cfe3c")
        self.assertEqual(V.H_ATTESTED.hex(), "7e5f2fdf987cac883a0453016a9541553d700e3a6f3a807839f22d5ca07b802c")
        self.assertEqual(V.H_LENS_KERNEL.hex(), "874e714dd14e6d7c144a4c377ae649f4124ea3788b17fa1ff86cf1be8a168ecb")
        self.assertEqual(V.sha256((ROOT_DIR / "kernel" / "lens.wasm").read_bytes()), V.H_LENS_KERNEL)
        # The spec's schema table and intrinsic constants are the code's, digit for digit
        spec = (ROOT_DIR / "VARS-1-SPEC.md").read_text(encoding="utf-8")
        rows = dict(re.findall(r"^\| ([a-z_]+) \|[^\n]*\| `([0-9a-f]{64})` \|$", spec, re.M))
        self.assertEqual({k: rows.get(k) for k in V.H_SCHEMA}, {k: h.hex() for k, h in V.H_SCHEMA.items()})
        consts = dict(re.findall(r"^\| `(H_[A-Z_]+)` \|[^\n]*\| `([0-9a-f]{64})` \|$", spec, re.M))
        self.assertEqual({k: getattr(V, k).hex() for k in consts}, consts)
        self.assertIn(V.H_LENS_KERNEL.hex(), spec)
        self.assertEqual(
            V.H_SCHEMA["axiom"].hex(),
            "aaf70509e078bf1f833492eb82a116e4122232d424cf1668c05a9dd25855dcda",
        )

        # Golden POL1 vector
        pk_ones = b"\x11" * 32
        hvec_ones = V.atom_hvec([pk_ones])
        h_hvec_ones = V.sha256(hvec_ones)
        self.assertEqual(h_hvec_ones.hex(), "15baf6a69e23659232b311b8a21e4887679b7227e7a03dd6c44f8d5dfaa7c272")
        pol_ones = V.atom_pol1(1, h_hvec_ones)
        self.assertEqual(
            V.sha256(pol_ones).hex(),
            "3f1aa0efab0a4dea5ba6047f83f992ec7e60d44b84cd0577abf77446d17dfd93",
        )

        # Golden Environment & ComputationRoot bit-identity with sigma_resume.py
        env_raw = V.atom_environment([])
        env_id = V.sha256(env_raw)
        self.assertEqual(env_id.hex(), "ee0093e760094c3f2d459b2c1ed1f95c4fbfb2a93288a0e0cadeb7903b1ec857")
        sr_env = SR.Environment([], {})
        self.assertEqual(env_id.hex(), sr_env.environment_id)

        root_raw = V.atom_computation_root(V.H_I, env_id)
        comp_id = V.sha256(root_raw)
        self.assertEqual(comp_id.hex(), "495465d6705698e69733b0c65e40c84d920d648d559ead629770e007b8c6cf2b")
        _, sr_cid = SR.root(V.H_I, sr_env)
        self.assertEqual(comp_id.hex(), sr_cid)

    def test_02_local_loop_rebinding_rollback_import_rotation(self) -> None:
        c0, s0, _ = self._bootstrap_genesis("core")

        # --- Step 1: S1 Local Loop (Term `APPLY(I, K)` reduces to `K` in 2 steps costing 4 ATP) ---
        app_ik_bytes = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=V.H_I, right=V.H_K)
        h_app_ik = V.sha256(app_ik_bytes)
        sr_env = SR.Environment([h_app_ik], {h_app_ik: app_ik_bytes})
        _, cid_hex = SR.root(h_app_ik, sr_env)
        comp_id = bytes.fromhex(cid_hex)

        atoms1: dict[bytes, bytes] = {}
        self._put_atom(atoms1, app_ik_bytes)
        h_env = self._put_atom(atoms1, V.atom_environment([h_app_ik]))
        h_root = self._put_atom(atoms1, V.atom_computation_root(h_app_ik, h_env))
        self.assertEqual(h_root, comp_id)

        v1 = V.Cell(
            h_schema=V.H_SCHEMA["computation"],
            h_slot_name=self._put_atom(atoms1, V.atom_utf8("core/comp.v1")),
            h_payload=comp_id,
        )
        h_rel_v1 = self._put_atom(atoms1, V.atom_hvec([v1.id]))
        k1 = V.Cell(
            h_schema=V.H_SCHEMA["contract"],
            h_slot_name=self._put_atom(atoms1, V.atom_utf8("core/contract.k1")),
            h_payload=self._put_atom(atoms1, V.atom_utf8("APPLY(I, K) must reduce to K")),
            h_relies=h_rel_v1,
            slots=(
                self._put_atom(atoms1, V.atom_utf8("provisional")),
                comp_id,
                V.H_K,
                V.H_EMPTY,
            ),
        )

        ckpt0_doc, ckpt0_id, sb0 = SR.start(cid_hex, h_app_ik)
        res_paused = SR.advance(ckpt0_doc, ckpt0_id, sb0, sr_env, additional_credit=0)
        self.assertEqual(res_paused.outcome, SR.PAUSED)
        h_sb_paused = self._put_atom(atoms1, res_paused.state_bytes)

        ckpt1 = V.Cell(
            h_schema=V.H_SCHEMA["checkpoint"],
            h_slot_name=self._put_atom(atoms1, V.atom_utf8("core/ckpt.1")),
            h_payload=h_sb_paused,
            h_relies=h_rel_v1,
            slots=(
                comp_id,
                self._put_atom(atoms1, V.atom_u64(0)),
                self._put_atom(atoms1, V.atom_u64(0)),
                self._put_atom(atoms1, V.atom_u64(res_paused.checkpoint["peak_semantic_size"])),
                self._put_atom(atoms1, V.atom_utf8("PAUSED")),
                self._put_atom(atoms1, V.atom_u64(0)),
            ),
        )
        seals1 = [
            V.Seal.sign(self.sk1, v1.id, s0.id),
            V.Seal.sign(self.sk1, k1.id, s0.id),
            V.Seal.sign(self.sk1, ckpt1.id, s0.id),
        ]
        c1 = self.repo.build_candidate_commit("core", atoms1, [v1, k1, ckpt1], seals1, parent_commit=c0)
        self.repo.admit_and_advance("core", c1, expected_old=c0)

        lens1 = self.repo.lens("core")
        self.assertTrue(lens1["provisional"][k1.id])
        self.assertFalse(lens1["settled"][k1.id])

        # Advance sigma_resume with credit = 10 -> reaches NORMAL_FORM = H_K!
        res_nf = SR.advance(res_paused.checkpoint, res_paused.checkpoint_id, res_paused.state_bytes, sr_env, additional_credit=10)
        self.assertEqual(res_nf.outcome, SR.NORMAL_FORM)
        _, nf_term_hash = V.sgs1_term_hash(res_nf.state_bytes)
        self.assertEqual(nf_term_hash, V.H_K)

        atoms2: dict[bytes, bytes] = {}
        h_sb_nf = self._put_atom(atoms2, res_nf.state_bytes)
        ckpt2 = V.Cell(
            h_schema=V.H_SCHEMA["checkpoint"],
            h_slot_name=self._put_atom(atoms2, V.atom_utf8("core/ckpt.2")),
            h_payload=h_sb_nf,
            h_relies=self._put_atom(atoms2, V.atom_hvec([v1.id, ckpt1.id])),
            slots=(
                comp_id,
                self._put_atom(atoms2, V.atom_u64(10)),
                self._put_atom(atoms2, V.atom_u64(res_nf.checkpoint["spent_total"])),
                self._put_atom(atoms2, V.atom_u64(res_nf.checkpoint["peak_semantic_size"])),
                self._put_atom(atoms2, V.atom_utf8("NORMAL_FORM")),
                self._put_atom(atoms2, V.atom_u64(res_nf.checkpoint["transition_claim"]["actions"])),
            ),
        )
        verdict1 = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms2, V.atom_utf8("core/verdict.k1")),
            h_payload=k1.id,
            h_relies=self._put_atom(atoms2, V.atom_hvec([ckpt2.id])),
            h_attests=self._put_atom(atoms2, V.atom_hvec([k1.id])),
            slots=(
                ckpt2.id,
                self._put_atom(atoms2, V.atom_utf8("REPLAYED")),
                self._put_atom(atoms2, V.atom_utf8(SR.VERIFIER_ID)),
            ),
        )
        seals2 = [
            V.Seal.sign(self.sk1, ckpt2.id, s0.id),
            V.Seal.sign(self.sk1, verdict1.id, s0.id),
        ]
        c2 = self.repo.build_candidate_commit("core", atoms2, [ckpt2, verdict1], seals2, parent_commit=c1)
        self.repo.admit_and_advance("core", c2, expected_old=c1)

        lens2 = self.repo.lens("core")
        self.assertTrue(lens2["settled"][k1.id], "K1 must be Settled after REPLAYED verdict on NORMAL_FORM==H_K")
        self.assertFalse(lens2["provisional"][k1.id])

        # --- Step 2: Chained Supersession (`V3 supersedes V2 supersedes V1`) ---
        atoms3: dict[bytes, bytes] = {}
        v2 = V.Cell(
            h_schema=V.H_SCHEMA["computation"],
            h_slot_name=self._put_atom(atoms3, V.atom_utf8("core/comp.v1")),
            h_payload=comp_id,
            h_supersedes=self._put_atom(atoms3, V.atom_hvec([v1.id])),
            h_loss=self._put_atom(atoms3, V.atom_utf8("replaced V1 with V2")),
        )
        v3 = V.Cell(
            h_schema=V.H_SCHEMA["computation"],
            h_slot_name=self._put_atom(atoms3, V.atom_utf8("core/comp.v1")),
            h_payload=comp_id,
            h_supersedes=self._put_atom(atoms3, V.atom_hvec([v2.id])),
            h_loss=self._put_atom(atoms3, V.atom_utf8("replaced V2 with V3")),
        )
        seals3 = [
            V.Seal.sign(self.sk1, v2.id, s0.id),
            V.Seal.sign(self.sk1, v3.id, s0.id),
        ]
        c3 = self.repo.build_candidate_commit("core", atoms3, [v2, v3], seals3, parent_commit=c2)
        self.repo.admit_and_advance("core", c3, expected_old=c2)

        lens3 = self.repo.lens("core")
        self.assertTrue(lens3["superseded"][v1.id], "V1 must remain Superseded when V3 supersedes V2")
        self.assertTrue(lens3["superseded"][v2.id])
        self.assertTrue(lens3["active"][v3.id])
        self.assertFalse(lens3["active"][v1.id], "V1 must NOT resurrect!")
        self.assertTrue(lens3["stale"][k1.id], "K1 relying on superseded V1 must become Stale")

        # --- Step 4: Counterexample Verdict invalidating V3 -> V2 returns to Active, V1 stays Superseded ---
        atoms4: dict[bytes, bytes] = {}
        verdict_inv = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms4, V.atom_utf8("core/verdict.inv.v3")),
            h_payload=v3.id,
            h_invalidates=self._put_atom(atoms4, V.atom_hvec([v3.id])),
            slots=(
                V.H_EMPTY,
                self._put_atom(atoms4, V.atom_utf8("INVALID")),
                self._put_atom(atoms4, V.atom_utf8(SR.VERIFIER_ID)),
            ),
        )
        c4 = self.repo.build_candidate_commit(
            "core", atoms4, [verdict_inv], [V.Seal.sign(self.sk1, verdict_inv.id, s0.id)], parent_commit=c3
        )
        self.repo.admit_and_advance("core", c4, expected_old=c3)

        lens4 = self.repo.lens("core")
        self.assertTrue(lens4["invalidated"][v3.id])
        self.assertFalse(lens4["active"][v3.id])
        self.assertTrue(lens4["active"][v2.id], "V2 must return to Active when V3 is Invalidated")
        self.assertTrue(lens4["superseded"][v1.id], "V1 must stay Superseded by V2")

        # --- Step 3: S2 Foreign Import (with self-sealed foreign SCOPE) & 2-of-2 Detached Seal Quorum ---
        atoms5: dict[bytes, bytes] = {}
        h_peer_pks = self._put_atom(atoms5, V.atom_hvec([self.pk_peer]))
        h_peer_pol = self._put_atom(atoms5, V.atom_pol1(1, h_peer_pks))
        s_peer = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms5, V.atom_utf8("peerB/SCOPE")),
            h_payload=self._put_atom(atoms5, V.atom_utf8("peerB")),
            slots=(h_peer_pol, h_peer_pol, V.H_LENS_KERNEL),
        )
        seal_s_peer = V.Seal.sign(self.sk_peer, s_peer.id, s_peer.id)
        foreign_ax = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=self._put_atom(atoms5, V.atom_utf8("peerB/foreign.axiom")),
            h_payload=self._put_atom(atoms5, V.atom_utf8("Foreign theorem from peerB")),
        )
        foreign_seal = V.Seal.sign(self.sk_peer, foreign_ax.id, s_peer.id)
        acc_cell = V.Cell(
            h_schema=V.H_SCHEMA["acceptance"],
            h_slot_name=self._put_atom(atoms5, V.atom_utf8("core/accept.peerB")),
            h_payload=foreign_ax.id,
            slots=(self._put_atom(atoms5, V.atom_utf8("peerB")), s_peer.id),
        )
        # First commit with only 1 seal (sk1) on acc_cell -> threshold is 2, so NOT yet Accepted!
        seal_acc_1 = V.Seal.sign(self.sk1, acc_cell.id, s0.id)
        c5 = self.repo.build_candidate_commit(
            "core", atoms5, [s_peer, foreign_ax, acc_cell], [seal_s_peer, foreign_seal, seal_acc_1], parent_commit=c4
        )
        self.repo.admit_and_advance("core", c5, expected_old=c4)

        lens5 = self.repo.lens("core")
        self.assertFalse(lens5["accepted"][foreign_ax.id], "1-of-2 acceptance seal must not accept foreign cell")
        self.assertFalse(lens5["active"][foreign_ax.id])

        # Second signer (sk2) adds detached SEAL on the EXACT SAME acc_cell.id!
        seal_acc_2 = V.Seal.sign(self.sk2, acc_cell.id, s0.id)
        c6 = self.repo.build_candidate_commit("core", {}, [], [seal_acc_2], parent_commit=c5)
        self.repo.admit_and_advance("core", c6, expected_old=c5)

        lens6 = self.repo.lens("core")
        self.assertTrue(lens6["accepted"][foreign_ax.id], "2-of-2 detached seals on acc_cell must accept foreign cell")
        self.assertTrue(lens6["active"][foreign_ax.id])
        self.assertFalse(lens6["stale"][foreign_ax.id])

        # --- Step 5: Non-Retroactive Scope Rotation ---
        atoms7: dict[bytes, bytes] = {}
        h_pks_only1 = self._put_atom(atoms7, V.atom_hvec([self.pk1]))
        h_pol_only1 = self._put_atom(atoms7, V.atom_pol1(1, h_pks_only1))
        s1 = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms7, V.atom_utf8("core/SCOPE")),
            h_payload=self._put_atom(atoms7, V.atom_utf8("core")),
            h_supersedes=self._put_atom(atoms7, V.atom_hvec([s0.id])),
            h_loss=self._put_atom(atoms7, V.atom_utf8("rotated out pk2")),
            slots=(h_pol_only1, h_pol_only1, V.H_LENS_KERNEL),
        )
        c7 = self.repo.build_candidate_commit(
            "core", atoms7, [s1], [V.Seal.sign(self.sk1, s1.id, s0.id)], parent_commit=c6
        )
        self.repo.admit_and_advance("core", c7, expected_old=c6)

        lens7 = self.repo.lens("core")
        self.assertTrue(
            lens7["accepted"][foreign_ax.id],
            "rotating pk2 out in S1 must NOT retroactively dissolve acceptance latched under S0",
        )
        self.assertTrue(lens7["active"][s1.id])
        self.assertTrue(lens7["superseded"][s0.id])

        # Verify pk2 can no longer sign new transitions under S1
        atoms8: dict[bytes, bytes] = {}
        bad_ax = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=self._put_atom(atoms8, V.atom_utf8("core/bad.axiom")),
            h_payload=self._put_atom(atoms8, V.atom_utf8("signed by rotated-out pk2")),
        )
        c8_bad = self.repo.build_candidate_commit(
            "core", atoms8, [bad_ax], [V.Seal.sign(self.sk2, bad_ax.id, s1.id)], parent_commit=c7
        )
        with self.assertRaisesRegex(V.VarsError, "Local seal signer not in active SCOPE policy"):
            self.repo.admit_and_advance("core", c8_bad, expected_old=c7)

    def test_03_gate_rejects_malformed_commits(self) -> None:
        c0, s0, _ = self._bootstrap_genesis("core")

        # Mutant : Replace a 100644 CAS blob with a 120000 symlink (typechange `T`)
        hx = s0.id.hex()
        c_symlink = self.repo.build_candidate_commit(
            "core",
            {},
            [],
            [],
            parent_commit=c0,
            extra_tree_entries=[("120000", "blob", f"cas/cells/{hx[:2]}/{hx[2:]}", b"/etc/passwd")],
        )
        with self.assertRaisesRegex(V.VarsError, "Check #2 failed"):
            self.repo.admit_and_advance("core", c_symlink, expected_old=c0)

        # Mutant : Add a cell referencing a non-existent payload atom hash
        atoms_m2: dict[bytes, bytes] = {}
        h_slot = self._put_atom(atoms_m2, V.atom_utf8("core/missing.payload"))
        missing_atom_h = b"\x99" * 32
        cell_m2 = V.Cell(h_schema=V.H_SCHEMA["axiom"], h_slot_name=h_slot, h_payload=missing_atom_h)
        c_m2 = self.repo.build_candidate_commit(
            "core", atoms_m2, [cell_m2], [V.Seal.sign(self.sk1, cell_m2.id, s0.id)], parent_commit=c0
        )
        with self.assertRaisesRegex(V.VarsError, "Check #4 failed: H_payload missing"):
            self.repo.admit_and_advance("core", c_m2, expected_old=c0)

        # Mutant : UTF8 atom with leading/trailing whitespace must be refused
        with self.assertRaisesRegex(V.VarsError, "leading or trailing ASCII whitespace"):
            V.atom_utf8("untrimmed\n")

        # Mutant : VERDICT with H_EMPTY checkpoint claiming H_REPLAYED must be refused
        atoms_m4: dict[bytes, bytes] = {}
        ax = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=self._put_atom(atoms_m4, V.atom_utf8("core/ax.1")),
            h_payload=self._put_atom(atoms_m4, V.atom_utf8("axiom statement")),
        )
        bad_verdict = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms_m4, V.atom_utf8("core/verdict.bad")),
            h_payload=ax.id,
            slots=(
                V.H_EMPTY,
                self._put_atom(atoms_m4, V.atom_utf8("REPLAYED")),
                self._put_atom(atoms_m4, V.atom_utf8("verifier-1")),
            ),
        )
        c_m4 = self.repo.build_candidate_commit(
            "core",
            atoms_m4,
            [ax, bad_verdict],
            [V.Seal.sign(self.sk1, ax.id, s0.id), V.Seal.sign(self.sk1, bad_verdict.id, s0.id)],
            parent_commit=c0,
        )
        with self.assertRaisesRegex(V.VarsError, "VERDICT with H_EMPTY checkpoint must use H_ATTESTED"):
            self.repo.admit_and_advance("core", c_m4, expected_old=c0)

        # Mutant : Compare-and-swap failure when expected_old is stale
        with self.assertRaisesRegex(V.VarsError, "CAS ref mismatch"):
            self.repo.admit_and_advance("core", c0, expected_old="0" * 40)

    def test_04_scope_epochs_forged_checkpoints_foreign_scopes(self) -> None:
        """Scope epochs, forged checkpoints, unsealed schemas, edge typing, stale acceptance, foreign scopes."""
        # Bootstrap scope `gov` with 2-of-2 admission policy {pk1, pk2} and 1-of-2 acceptance policy
        c0, s0, _ = self._bootstrap_genesis("gov", adm_threshold=2, acc_threshold=1)

        # --- Double SCOPE rotation in a single commit must be atomically rejected ---
        atoms_cv2: dict[bytes, bytes] = {}
        h_pks1 = self._put_atom(atoms_cv2, V.atom_hvec([self.pk1]))
        h_pol1 = self._put_atom(atoms_cv2, V.atom_pol1(1, h_pks1))
        h_sup_s0 = self._put_atom(atoms_cv2, V.atom_hvec([s0.id]))
        s_fork1 = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms_cv2, V.atom_utf8("gov/SCOPE")),
            h_payload=self._put_atom(atoms_cv2, V.atom_utf8("gov")),
            h_supersedes=h_sup_s0,
            h_loss=self._put_atom(atoms_cv2, V.atom_utf8("fork rotation 1")),
            slots=(h_pol1, h_pol1, V.H_LENS_KERNEL),
        )
        s_fork2 = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms_cv2, V.atom_utf8("gov/SCOPE")),
            h_payload=self._put_atom(atoms_cv2, V.atom_utf8("gov")),
            h_supersedes=h_sup_s0,
            h_loss=self._put_atom(atoms_cv2, V.atom_utf8("fork rotation 2")),
            slots=(h_pol1, h_pol1, V.H_LENS_KERNEL),
        )
        c_cv2 = self.repo.build_candidate_commit(
            "gov",
            atoms_cv2,
            [s_fork1, s_fork2],
            [
                V.Seal.sign(self.sk1, s_fork1.id, s0.id),
                V.Seal.sign(self.sk2, s_fork1.id, s0.id),
                V.Seal.sign(self.sk1, s_fork2.id, s0.id),
                V.Seal.sign(self.sk2, s_fork2.id, s0.id),
            ],
            parent_commit=c0,
        )
        with self.assertRaisesRegex(V.VarsError, "multiple local schema.scope cells"):
            self.repo.admit_and_advance("gov", c_cv2, expected_old=c0)

        # --- Old partial signature must NOT gain retroactive quorum after scope rotation ---
        atoms_t1: dict[bytes, bytes] = {}
        v_owner = V.Cell(
            h_schema=V.H_SCHEMA["contract"],
            h_slot_name=self._put_atom(atoms_t1, V.atom_utf8("gov/contract.owner")),
            h_payload=self._put_atom(atoms_t1, V.atom_utf8("Owner contract V")),
            slots=(V.H_OWNER, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY),
        )
        w_replace = V.Cell(
            h_schema=V.H_SCHEMA["contract"],
            h_slot_name=self._put_atom(atoms_t1, V.atom_utf8("gov/contract.owner")),
            h_payload=self._put_atom(atoms_t1, V.atom_utf8("Replacement contract W")),
            h_supersedes=self._put_atom(atoms_t1, V.atom_hvec([v_owner.id])),
            h_loss=self._put_atom(atoms_t1, V.atom_utf8("attempt to replace V with only 1-of-2 seal")),
            slots=(V.H_OWNER, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY),
        )
        # In T1 under S0 (2-of-2), W only gets 1 seal (from sk1), which is < 2!
        c_t1 = self.repo.build_candidate_commit(
            "gov",
            atoms_t1,
            [v_owner, w_replace],
            [
                V.Seal.sign(self.sk1, v_owner.id, s0.id),
                V.Seal.sign(self.sk2, v_owner.id, s0.id),
                V.Seal.sign(self.sk1, w_replace.id, s0.id),
            ],
            parent_commit=c0,
        )
        self.repo.admit_and_advance("gov", c_t1, expected_old=c0)
        lens_t1 = self.repo.lens("gov")
        self.assertTrue(lens_t1["active"][v_owner.id], "V must remain Active under S0 (W has only 1-of-2 seal)")
        self.assertFalse(lens_t1["superseded"][v_owner.id])

        # In T2, legitimately rotate S0 -> S1 (1-of-1 {pk1}) with both sk1 and sk2 seals
        c_t2 = self.repo.build_candidate_commit(
            "gov",
            atoms_cv2,
            [s_fork1],
            [V.Seal.sign(self.sk1, s_fork1.id, s0.id), V.Seal.sign(self.sk2, s_fork1.id, s0.id)],
            parent_commit=c_t1,
        )
        self.repo.admit_and_advance("gov", c_t2, expected_old=c_t1)

        # In T3 under S1 (1-of-1 {pk1}), add a benign axiom and verify W's old S0 seal did NOT retroactively supersede V!
        atoms_t3: dict[bytes, bytes] = {}
        benign_ax = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=self._put_atom(atoms_t3, V.atom_utf8("gov/benign")),
            h_payload=self._put_atom(atoms_t3, V.atom_utf8("benign")),
        )
        c_t3 = self.repo.build_candidate_commit(
            "gov", atoms_t3, [benign_ax], [V.Seal.sign(self.sk1, benign_ax.id, s_fork1.id)], parent_commit=c_t2
        )
        self.repo.admit_and_advance("gov", c_t3, expected_old=c_t2)

        lens_t3 = self.repo.lens("gov")
        self.assertTrue(
            lens_t3["active"][v_owner.id],
            "old SEAL(W, S0, sk1) must NOT gain retroactive quorum when S1 lowers threshold to 1-of-1!",
        )
        self.assertFalse(lens_t3["superseded"][v_owner.id])

        # --- Forged terminal CHECKPOINT claiming K for ComputationRoot(I) must be rejected ---
        atoms_cv4: dict[bytes, bytes] = {}
        h_env_empty = self._put_atom(atoms_cv4, V.atom_environment([]))
        h_root_i = self._put_atom(atoms_cv4, V.atom_computation_root(V.H_I, h_env_empty))
        # Forged SGS1 state claiming computation_id = h_root_i, but encoding term K instead of I!
        forged_sgs1 = b"SGS1" + h_root_i + b"L" + V.sha256(b"K")
        h_forged_sgs1 = self._put_atom(atoms_cv4, forged_sgs1)
        forged_ckpt = V.Cell(
            h_schema=V.H_SCHEMA["checkpoint"],
            h_slot_name=self._put_atom(atoms_cv4, V.atom_utf8("gov/ckpt.forged")),
            h_payload=h_forged_sgs1,
            slots=(
                h_root_i,
                self._put_atom(atoms_cv4, V.atom_u64(0)),
                self._put_atom(atoms_cv4, V.atom_u64(0)),
                self._put_atom(atoms_cv4, V.atom_u64(1)),
                self._put_atom(atoms_cv4, V.atom_utf8("NORMAL_FORM")),
                self._put_atom(atoms_cv4, V.atom_u64(0)),
            ),
        )
        c_cv4 = self.repo.build_candidate_commit(
            "gov",
            atoms_cv4,
            [forged_ckpt],
            [V.Seal.sign(self.sk1, forged_ckpt.id, s_fork1.id)],
            parent_commit=c_t3,
        )
        with self.assertRaisesRegex(V.VarsError, "forged checkpoint state_bytes"):
            self.repo.admit_and_advance("gov", c_cv4, expected_old=c_t3)

        # --- Unsealed custom META_SCHEMA cell must be rejected ---
        atoms_cv5: dict[bytes, bytes] = {}
        custom_schema = V.Cell(
            h_schema=V.H_META_SCHEMA,
            h_slot_name=self._put_atom(atoms_cv5, V.atom_utf8("gov/schema.custom")),
            h_payload=V.H_EMPTY,
            slots=(self._put_atom(atoms_cv5, V.atom_utf8("custom_field:utf8")),),
        )
        c_cv5_unsealed = self.repo.build_candidate_commit(
            "gov", atoms_cv5, [custom_schema], [], parent_commit=c_t3
        )
        with self.assertRaisesRegex(V.VarsError, "New local cell .* lacks a valid Seal"):
            self.repo.admit_and_advance("gov", c_cv5_unsealed, expected_old=c_t3)

        # --- Atom in H_relies HVEC or cross-schema H_supersedes must be rejected ---
        atoms_cv6: dict[bytes, bytes] = {}
        bad_relies_cell = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=self._put_atom(atoms_cv6, V.atom_utf8("gov/bad.relies")),
            h_payload=self._put_atom(atoms_cv6, V.atom_utf8("relies on Atom H_I")),
            h_relies=self._put_atom(atoms_cv6, V.atom_hvec([V.H_I])),
        )
        c_cv6 = self.repo.build_candidate_commit(
            "gov",
            atoms_cv6,
            [bad_relies_cell],
            [V.Seal.sign(self.sk1, bad_relies_cell.id, s_fork1.id)],
            parent_commit=c_t3,
        )
        with self.assertRaisesRegex(V.VarsError, "relies references non-Cell"):
            self.repo.admit_and_advance("gov", c_cv6, expected_old=c_t3)

        # --- Stale ACCEPTANCE must propagate Stale to imported foreign witness & revoke Settled ---
        atoms_cv7: dict[bytes, bytes] = {}
        h_peer_pks = self._put_atom(atoms_cv7, V.atom_hvec([self.pk_peer]))
        h_peer_pol = self._put_atom(atoms_cv7, V.atom_pol1(1, h_peer_pks))
        s_peer = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms_cv7, V.atom_utf8("peerB/SCOPE")),
            h_payload=self._put_atom(atoms_cv7, V.atom_utf8("peerB")),
            slots=(h_peer_pol, h_peer_pol, V.H_LENS_KERNEL),
        )
        d_precond = V.Cell(
            h_schema=V.H_SCHEMA["decision"],
            h_slot_name=self._put_atom(atoms_cv7, V.atom_utf8("gov/dec.trust.peerB")),
            h_payload=self._put_atom(atoms_cv7, V.atom_utf8("Trust peerB auditors")),
            slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY),
        )
        q_local = V.Cell(
            h_schema=V.H_SCHEMA["question"],
            h_slot_name=self._put_atom(atoms_cv7, V.atom_utf8("gov/q.1")),
            h_payload=self._put_atom(atoms_cv7, V.atom_utf8("Is peerB theorem valid?")),
            slots=(V.H_SCHEMA["axiom"], h_peer_pol),
        )
        # Note: requires local question's evaluator policy pubkeys to be subset of local scope roster,
        # So let's use H_EMPTY (defaulting to local scope roster pk1) and have foreign_witness signed by pk1 in peerB
        h_peer_pks_pk1 = self._put_atom(atoms_cv7, V.atom_hvec([self.pk1]))
        h_peer_pol_pk1 = self._put_atom(atoms_cv7, V.atom_pol1(1, h_peer_pks_pk1))
        s_peer = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms_cv7, V.atom_utf8("peerB/SCOPE")),
            h_payload=self._put_atom(atoms_cv7, V.atom_utf8("peerB")),
            slots=(h_peer_pol_pk1, h_peer_pol_pk1, V.H_LENS_KERNEL),
        )
        q_local = V.Cell(
            h_schema=V.H_SCHEMA["question"],
            h_slot_name=self._put_atom(atoms_cv7, V.atom_utf8("gov/q.1")),
            h_payload=self._put_atom(atoms_cv7, V.atom_utf8("Is peerB theorem valid?")),
            slots=(V.H_SCHEMA["axiom"], V.H_EMPTY),
        )
        x_foreign_witness = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=self._put_atom(atoms_cv7, V.atom_utf8("peerB/witness.ax")),
            h_payload=self._put_atom(atoms_cv7, V.atom_utf8("Foreign proof answering q_local")),
            h_attests=self._put_atom(atoms_cv7, V.atom_hvec([q_local.id])),
        )
        acc_bridge = V.Cell(
            h_schema=V.H_SCHEMA["acceptance"],
            h_slot_name=self._put_atom(atoms_cv7, V.atom_utf8("gov/accept.witness")),
            h_payload=x_foreign_witness.id,
            h_relies=self._put_atom(atoms_cv7, V.atom_hvec([d_precond.id])),
            slots=(self._put_atom(atoms_cv7, V.atom_utf8("peerB")), s_peer.id),
        )
        c_cv7_1 = self.repo.build_candidate_commit(
            "gov",
            atoms_cv7,
            [s_peer, d_precond, q_local, x_foreign_witness, acc_bridge],
            [
                V.Seal.sign(self.sk1, s_peer.id, s_peer.id),
                V.Seal.sign(self.sk1, d_precond.id, s_fork1.id),
                V.Seal.sign(self.sk1, q_local.id, s_fork1.id),
                V.Seal.sign(self.sk1, x_foreign_witness.id, s_peer.id),
                V.Seal.sign(self.sk1, acc_bridge.id, s_fork1.id),
            ],
            parent_commit=c_t3,
        )
        self.repo.admit_and_advance("gov", c_cv7_1, expected_old=c_t3)
        lens_cv7_1 = self.repo.lens("gov")
        self.assertTrue(lens_cv7_1["settled"][q_local.id], "q_local should initially be Settled via foreign witness")

        # Now retire d_precond -> acc_bridge becomes Stale -> x_foreign_witness becomes Stale -> q_local is NO LONGER Settled!
        atoms_cv7_2: dict[bytes, bytes] = {}
        ret_d = V.Cell(
            h_schema=V.H_SCHEMA["decision"],
            h_slot_name=self._put_atom(atoms_cv7_2, V.atom_utf8("gov/retire.trust")),
            h_payload=self._put_atom(atoms_cv7_2, V.atom_utf8("Revoke trust in peerB")),
            h_retires=self._put_atom(atoms_cv7_2, V.atom_hvec([d_precond.id])),
            h_loss=self._put_atom(atoms_cv7_2, V.atom_utf8("peerB audit lapsed")),
            slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY),
        )
        c_cv7_2 = self.repo.build_candidate_commit(
            "gov",
            atoms_cv7_2,
            [ret_d],
            [V.Seal.sign(self.sk1, ret_d.id, s_fork1.id)],
            parent_commit=c_cv7_1,
        )
        self.repo.admit_and_advance("gov", c_cv7_2, expected_old=c_cv7_1)
        lens_cv7_2 = self.repo.lens("gov")
        self.assertTrue(lens_cv7_2["stale"][acc_bridge.id], "ACCEPTANCE cell must be Stale after d_precond retired")
        self.assertTrue(lens_cv7_2["stale"][x_foreign_witness.id], "foreign witness must become Stale when ACCEPTANCE is Stale")
        self.assertFalse(lens_cv7_2["settled"][q_local.id], "q_local must lose Settled status when foreign witness becomes Stale")

    def test_05_signatures_names_dependencies_verdicts_acceptance(self) -> None:
        """Signature vectors, slot names, dependencies, replay ceiling, contradictory verdicts, acceptance boundaries."""
        # --- 1. Run all 34 Ed25519 vectors in `vectors/verify-sig.json` ---
        vectors_path = ROOT_DIR / "vectors" / "verify-sig.json"
        doc = json.loads(vectors_path.read_text(encoding="utf-8"))
        self.assertEqual(len(doc["vectors"]), 50)
        ed25519_vecs = [v for v in doc["vectors"] if "alg" not in v["input"]]
        self.assertEqual(len(ed25519_vecs), 34)
        for vec in ed25519_vecs:
            vid = vec["id"]
            inp = vec["input"]
            expected_valid = vec["expect"]["valid"]
            pk_raw = bytes.fromhex(inp["key"])
            sig_raw = bytes.fromhex(inp["sig"])
            msg = b"warrant-sig-v1:" + bytes.fromhex(inp["warrant_id"])
            actual = V.ed25519_verify(pk_raw, msg, sig_raw)
            self.assertEqual(actual, expected_valid, f"verify-sig vector {vid} ({vec.get('why')}) mismatch")

        # Also check RFC 8032 §7.1 Test 1 & Test 2 roundtrip
        rfc_sk1 = bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
        rfc_pk1 = bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
        rfc_sig1 = bytes.fromhex(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155"
            "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
        )
        self.assertEqual(V.ed25519_pubkey(rfc_sk1), rfc_pk1)
        self.assertEqual(V.ed25519_sign(rfc_sk1, b""), rfc_sig1)
        self.assertTrue(V.ed25519_verify(rfc_pk1, b"", rfc_sig1))

        # Verify POL1 containing a weak public key is rejected
        weak_pk = bytes.fromhex("0100000000000000000000000000000000000000000000000000000000000000")
        self.assertTrue(V.weak_public_key(weak_pk))

        # Bootstrap scope `core` with 1-of-2 admission policy and 2-of-2 acceptance policy
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=1, acc_threshold=2)

        # --- 2. Reserved `core/schema.*` namespace and unsafe slot names ---
        with self.assertRaisesRegex(V.VarsError, "slot name"):
            V.validate_slot_name("core/../escape")
        with self.assertRaisesRegex(V.VarsError, "slot name"):
            V.validate_slot_name("core/bad.lock/cell")

        atoms_cv9: dict[bytes, bytes] = {}
        fake_schema = V.Cell(
            h_schema=V.H_META_SCHEMA,
            h_slot_name=self._put_atom(atoms_cv9, V.atom_utf8("core/schema.forged")),
            h_payload=V.H_EMPTY,
            slots=(self._put_atom(atoms_cv9, V.atom_utf8("x:utf8")),),
        )
        c_cv9 = self.repo.build_candidate_commit(
            "core", atoms_cv9, [fake_schema], [V.Seal.sign(self.sk1, fake_schema.id, s0.id)], parent_commit=c0
        )
        with self.assertRaisesRegex(V.VarsError, "slot name 'core/schema.forged' is reserved"):
            self.repo.admit_and_advance("core", c_cv9, expected_old=c0)

        # --- 3. Duplicate unlinked local cells for the same `H_slot_name` must be rejected ---
        atoms_cv8: dict[bytes, bytes] = {}
        h_dup_slot = self._put_atom(atoms_cv8, V.atom_utf8("core/dup.axiom"))
        dup1 = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=h_dup_slot,
            h_payload=self._put_atom(atoms_cv8, V.atom_utf8("Claim A")),
        )
        dup2 = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=h_dup_slot,
            h_payload=self._put_atom(atoms_cv8, V.atom_utf8("Claim B")),
        )
        c_cv8 = self.repo.build_candidate_commit(
            "core",
            atoms_cv8,
            [dup1, dup2],
            [V.Seal.sign(self.sk1, dup1.id, s0.id), V.Seal.sign(self.sk1, dup2.id, s0.id)],
            parent_commit=c0,
        )
        with self.assertRaisesRegex(V.VarsError, "duplicate unlinked binding for slot"):
            self.repo.admit_and_advance("core", c_cv8, expected_old=c0)

        # --- 4. Contract without `schema.computation` in `H_relies` or Verdict without checkpoint in `H_relies` ---
        app_ik_bytes = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=V.H_I, right=V.H_K)
        h_app_ik = V.sha256(app_ik_bytes)
        sr_env = SR.Environment([h_app_ik], {h_app_ik: app_ik_bytes})
        _, cid_hex = SR.root(h_app_ik, sr_env)
        comp_id = bytes.fromhex(cid_hex)

        atoms_cv7: dict[bytes, bytes] = {}
        self._put_atom(atoms_cv7, app_ik_bytes)
        h_env = self._put_atom(atoms_cv7, V.atom_environment([h_app_ik]))
        self._put_atom(atoms_cv7, V.atom_computation_root(h_app_ik, h_env))
        k_no_relies = V.Cell(
            h_schema=V.H_SCHEMA["contract"],
            h_slot_name=self._put_atom(atoms_cv7, V.atom_utf8("core/contract.norelies")),
            h_payload=self._put_atom(atoms_cv7, V.atom_utf8("Missing H_relies to computation")),
            h_relies=V.H_EMPTY,
            slots=(V.H_PROVISIONAL, comp_id, V.H_K, V.H_EMPTY),
        )
        c_cv7_bad = self.repo.build_candidate_commit(
            "core", atoms_cv7, [k_no_relies], [V.Seal.sign(self.sk1, k_no_relies.id, s0.id)], parent_commit=c0
        )
        with self.assertRaisesRegex(V.VarsError, "contract/decision with non-empty required_comp"):
            self.repo.admit_and_advance("core", c_cv7_bad, expected_old=c0)

        # --- 5. Incremental checkpoint replay, gate ceiling (`NOT_ASSESSED`), and contradictory verdicts ---
        atoms_s22: dict[bytes, bytes] = {}
        self._put_atom(atoms_s22, app_ik_bytes)
        h_env = self._put_atom(atoms_s22, V.atom_environment([h_app_ik]))
        self._put_atom(atoms_s22, V.atom_computation_root(h_app_ik, h_env))
        comp_cell = V.Cell(
            h_schema=V.H_SCHEMA["computation"],
            h_slot_name=self._put_atom(atoms_s22, V.atom_utf8("core/comp.s22")),
            h_payload=comp_id,
        )
        h_rel_comp = self._put_atom(atoms_s22, V.atom_hvec([comp_cell.id]))
        k_s22 = V.Cell(
            h_schema=V.H_SCHEMA["contract"],
            h_slot_name=self._put_atom(atoms_s22, V.atom_utf8("core/contract.s22")),
            h_payload=self._put_atom(atoms_s22, V.atom_utf8("APPLY(I,K) -> K")),
            h_relies=h_rel_comp,
            slots=(V.H_PROVISIONAL, comp_id, V.H_K, V.H_EMPTY),
        )
        ckpt0_doc, ckpt0_id, sb0 = SR.start(cid_hex, h_app_ik)
        res_nf = SR.advance(ckpt0_doc, ckpt0_id, sb0, sr_env, additional_credit=10)
        h_sb_nf = self._put_atom(atoms_s22, res_nf.state_bytes)
        ckpt_nf = V.Cell(
            h_schema=V.H_SCHEMA["checkpoint"],
            h_slot_name=self._put_atom(atoms_s22, V.atom_utf8("core/ckpt.s22")),
            h_payload=h_sb_nf,
            h_relies=h_rel_comp,
            slots=(
                comp_id,
                self._put_atom(atoms_s22, V.atom_u64(10)),
                self._put_atom(atoms_s22, V.atom_u64(res_nf.checkpoint["spent_total"])),
                self._put_atom(atoms_s22, V.atom_u64(res_nf.checkpoint["peak_semantic_size"])),
                self._put_atom(atoms_s22, V.atom_utf8("NORMAL_FORM")),
                self._put_atom(atoms_s22, V.atom_u64(res_nf.checkpoint["transition_claim"]["actions"])),
            ),
        )
        # Verify gate_mode=True with max_atp=1 (below delta_spent=4) returns "NOT_ASSESSED" instead of "INVALID"!
        status_ceiling = V.verify_checkpoint_replay(
            ckpt_nf,
            {**V.STD_SCHEMA_ATOMS, **atoms_s22},
            {comp_cell.id: comp_cell},
            max_atp=1,
            gate_mode=True,
        )
        self.assertEqual(status_ceiling, "NOT_ASSESSED")

        verdict_ok = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms_s22, V.atom_utf8("core/verdict.ok")),
            h_payload=k_s22.id,
            h_relies=self._put_atom(atoms_s22, V.atom_hvec([ckpt_nf.id])),
            h_attests=self._put_atom(atoms_s22, V.atom_hvec([k_s22.id])),
            slots=(
                ckpt_nf.id,
                V.H_REPLAYED,
                self._put_atom(atoms_s22, V.atom_utf8(SR.VERIFIER_ID)),
            ),
        )
        c_s22 = self.repo.build_candidate_commit(
            "core",
            atoms_s22,
            [comp_cell, k_s22, ckpt_nf, verdict_ok],
            [
                V.Seal.sign(self.sk1, comp_cell.id, s0.id),
                V.Seal.sign(self.sk1, k_s22.id, s0.id),
                V.Seal.sign(self.sk1, ckpt_nf.id, s0.id),
                V.Seal.sign(self.sk1, verdict_ok.id, s0.id),
            ],
            parent_commit=c0,
        )
        self.repo.admit_and_advance("core", c_s22, expected_old=c0)
        self.assertTrue(self.repo.lens("core")["settled"][k_s22.id])

        # Second evaluator sk2 publishes a contradictory `INVALID` verdict for `k_s22` under the same `verifier_id` -> blocks `Settled`!
        atoms_cv6_v: dict[bytes, bytes] = {}
        verdict_contradict = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms_cv6_v, V.atom_utf8("core/verdict.contradict")),
            h_payload=k_s22.id,
            h_relies=self._put_atom(atoms_cv6_v, V.atom_hvec([ckpt_nf.id])),
            h_attests=self._put_atom(atoms_cv6_v, V.atom_hvec([k_s22.id])),
            slots=(
                ckpt_nf.id,
                V.H_VERDICT_INVALID,
                self._put_atom(atoms_cv6_v, V.atom_utf8(SR.VERIFIER_ID)),
            ),
        )
        c_cv6_v = self.repo.build_candidate_commit(
            "core",
            atoms_cv6_v,
            [verdict_contradict],
            [V.Seal.sign(self.sk2, verdict_contradict.id, s0.id)],
            parent_commit=c_s22,
        )
        self.repo.admit_and_advance("core", c_cv6_v, expected_old=c_s22)
        lens_cv6_v = self.repo.lens("core")
        self.assertFalse(
            lens_cv6_v["settled"][k_s22.id],
            "contradictory active INVALID verdict under same verifier_id must block Settled",
        )
        self.assertTrue(lens_cv6_v["provisional"][k_s22.id])

        # --- 6. Pinned foreign scope, non-evictable 2-of-2 ACCEPTANCE, no cross-scope hereditary leak ---
        atoms_f: dict[bytes, bytes] = {}
        h_peer_pks = self._put_atom(atoms_f, V.atom_hvec([self.pk_peer]))
        h_peer_pol = self._put_atom(atoms_f, V.atom_pol1(1, h_peer_pks))
        s_peer_b = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms_f, V.atom_utf8("peerB/SCOPE")),
            h_payload=self._put_atom(atoms_f, V.atom_utf8("peerB")),
            slots=(h_peer_pol, h_peer_pol, V.H_LENS_KERNEL),
        )
        s_peer_c = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms_f, V.atom_utf8("peerC/SCOPE")),
            h_payload=self._put_atom(atoms_f, V.atom_utf8("peerC")),
            slots=(h_peer_pol, h_peer_pol, V.H_LENS_KERNEL),
        )
        cell_c = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=self._put_atom(atoms_f, V.atom_utf8("peerC/ax.c")),
            h_payload=self._put_atom(atoms_f, V.atom_utf8("Unaccepted claim from third scope peerC")),
        )
        cell_b = V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=self._put_atom(atoms_f, V.atom_utf8("peerB/ax.b")),
            h_payload=self._put_atom(atoms_f, V.atom_utf8("Claim from peerB relying on peerC")),
            h_relies=self._put_atom(atoms_f, V.atom_hvec([cell_c.id])),
        )
        acc_b = V.Cell(
            h_schema=V.H_SCHEMA["acceptance"],
            h_slot_name=self._put_atom(atoms_f, V.atom_utf8("core/accept.b")),
            h_payload=cell_b.id,
            slots=(self._put_atom(atoms_f, V.atom_utf8("peerB")), s_peer_b.id),
        )
        c_f1 = self.repo.build_candidate_commit(
            "core",
            atoms_f,
            [s_peer_b, s_peer_c, cell_c, cell_b, acc_b],
            [
                V.Seal.sign(self.sk_peer, s_peer_b.id, s_peer_b.id),
                V.Seal.sign(self.sk_peer, s_peer_c.id, s_peer_c.id),
                V.Seal.sign(self.sk_peer, cell_c.id, s_peer_c.id),
                V.Seal.sign(self.sk_peer, cell_b.id, s_peer_b.id),
                V.Seal.sign(self.sk1, acc_b.id, s0.id),
                V.Seal.sign(self.sk2, acc_b.id, s0.id),
            ],
            parent_commit=c_cv6_v,
        )
        self.repo.admit_and_advance("core", c_f1, expected_old=c_cv6_v)
        lens_f1 = self.repo.lens("core")
        self.assertTrue(lens_f1["accepted"][cell_b.id])
        self.assertFalse(
            lens_f1["accepted"][cell_c.id],
            "accepting peerB's cell_b must NOT hereditarily accept peerC's cell_c without a peerC ACCEPTANCE!",
        )
        self.assertTrue(
            lens_f1["stale"][cell_b.id],
            "cell_b must be Stale because its cross-scope dependency cell_c is not Active",
        )

        # Single co-signer `sk1` attempts to unilaterally retire 2-of-2 `acc_b` (when acc_threshold=2)
        atoms_cv12: dict[bytes, bytes] = {}
        retire_acc_b = V.Cell(
            h_schema=V.H_SCHEMA["decision"],
            h_slot_name=self._put_atom(atoms_cv12, V.atom_utf8("core/retire.acc.b")),
            h_payload=self._put_atom(atoms_cv12, V.atom_utf8("Unilateral attempt to retire 2-of-2 acceptance")),
            h_retires=self._put_atom(atoms_cv12, V.atom_hvec([acc_b.id])),
            h_loss=self._put_atom(atoms_cv12, V.atom_utf8("try evicting with 1 signature")),
            slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY),
        )
        c_cv12 = self.repo.build_candidate_commit(
            "core",
            atoms_cv12,
            [retire_acc_b],
            [V.Seal.sign(self.sk1, retire_acc_b.id, s0.id)],
            parent_commit=c_f1,
        )
        self.repo.admit_and_advance("core", c_cv12, expected_old=c_f1)
        lens_cv12 = self.repo.lens("core")
        self.assertFalse(
            lens_cv12["retired"][acc_b.id],
            "1-of-2 signer must NOT be able to unilaterally retire a 2-of-2 ACCEPTANCE cell!",
        )
        self.assertTrue(lens_cv12["active"][acc_b.id])


    # ------------------------------------------------------------------------------------------
    # Helpers for compact scenarios
    # ------------------------------------------------------------------------------------------
    def _admit(self, atoms: dict[bytes, bytes], cells: list, seals: list, parent: str) -> str:
        c = self.repo.build_candidate_commit("core", atoms, cells, seals, parent_commit=parent)
        self.repo.admit_and_advance("core", c, expected_old=parent)
        return c

    def _hv(self, atoms: dict[bytes, bytes], ids: list[bytes]) -> bytes:
        return self._put_atom(atoms, V.atom_hvec(ids))

    def _axiom(self, atoms: dict[bytes, bytes], name: str, text: str, **edges: list[bytes]) -> V.Cell:
        kw = {f"h_{k}": self._hv(atoms, v) for k, v in edges.items()}
        if "h_supersedes" in kw or "h_retires" in kw:
            kw["h_loss"] = self._put_atom(atoms, V.atom_utf8(f"loss: {name}"))
        return V.Cell(
            h_schema=V.H_SCHEMA["axiom"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8(name)),
            h_payload=self._put_atom(atoms, V.atom_utf8(text)),
            **kw,
        )

    def test_06_stale_reaches_fixed_point_on_deep_acceptance_chain(self) -> None:
        """Pass 2 must iterate to the least fixed point, not a fixed 3 rounds.

        D <- A0 accepts X0;  X0 <- A1 accepts X1;  ...  X(n-2) <- A(n-1) accepts X(n-1).
        Each hop through an ACCEPTANCE costs one round; a 5-link chain needs 6.
        """
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=1, acc_threshold=1)
        atoms: dict[bytes, bytes] = {}
        h_peer_pol = self._put_atom(atoms, V.atom_pol1(1, self._hv(atoms, [self.pk_peer])))
        s_peer = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8("peerB/SCOPE")),
            h_payload=self._put_atom(atoms, V.atom_utf8("peerB")),
            slots=(h_peer_pol, h_peer_pol, V.H_LENS_KERNEL),
        )
        d = self._axiom(atoms, "core/dep.d", "local dependency D")
        n = 5
        xs = [self._axiom(atoms, f"peerB/x{i}", f"foreign claim X{i}") for i in range(n)]
        accs = []
        for i in range(n):
            dep = d.id if i == 0 else xs[i - 1].id
            accs.append(
                V.Cell(
                    h_schema=V.H_SCHEMA["acceptance"],
                    h_slot_name=self._put_atom(atoms, V.atom_utf8(f"core/accept.x{i}")),
                    h_payload=xs[i].id,
                    h_relies=self._hv(atoms, [dep]),
                    slots=(self._put_atom(atoms, V.atom_utf8("peerB")), s_peer.id),
                )
            )
        seals = [V.Seal.sign(self.sk_peer, s_peer.id, s_peer.id), V.Seal.sign(self.sk1, d.id, s0.id)]
        seals += [V.Seal.sign(self.sk_peer, x.id, s_peer.id) for x in xs]
        seals += [V.Seal.sign(self.sk1, a.id, s0.id) for a in accs]
        c1 = self._admit(atoms, [s_peer, d, *xs, *accs], seals, c0)

        lens1 = self.repo.lens("core")
        for x in xs:
            self.assertTrue(lens1["active"][x.id] and not lens1["stale"][x.id] and lens1["settled"][x.id])

        atoms2: dict[bytes, bytes] = {}
        retire_d = self._axiom(atoms2, "core/retire.d", "withdraw D", retires=[d.id])
        self._admit(atoms2, [retire_d], [V.Seal.sign(self.sk1, retire_d.id, s0.id)], c1)

        lens2 = self.repo.lens("core")
        self.assertTrue(lens2["retired"][d.id])
        for i in range(n):
            self.assertTrue(lens2["stale"][accs[i].id], f"ACCEPTANCE A{i} must be Stale")
            self.assertTrue(lens2["stale"][xs[i].id], f"foreign X{i} must be Stale (its only acceptance is Stale)")
            self.assertFalse(lens2["settled"][xs[i].id], f"foreign X{i} must not stay Settled")

    def test_07_slot_rebinding_requires_authorized_supersedes_chain(self) -> None:
        """An unauthorized or unrelated eviction edge does not license a second binding of a name, and
        invalidating the middle of V3 -> V2 -> V1 must not resurrect V1 next to V3."""
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=2, acc_threshold=2)
        atoms1: dict[bytes, bytes] = {}
        v1 = self._axiom(atoms1, "core/value", "old")
        c1 = self._admit(atoms1, [v1], [V.Seal.sign(self.sk1, v1.id, s0.id)], c0)

        # (a) V2 rebinding, plus an unrelated R "invalidating" V1 with 1 of 2 required signatures
        atoms_a: dict[bytes, bytes] = {}
        v2_a = self._axiom(atoms_a, "core/value", "new")
        r = self._axiom(atoms_a, "core/unrelated", "rumour", invalidates=[v1.id])
        c_a = self.repo.build_candidate_commit(
            "core", atoms_a, [v2_a, r],
            [V.Seal.sign(self.sk1, v2_a.id, s0.id), V.Seal.sign(self.sk1, r.id, s0.id)],
            parent_commit=c1,
        )
        with self.assertRaisesRegex(V.VarsError, "duplicate unlinked binding|does not reach the prior binding"):
            self.repo.admit_and_advance("core", c_a, expected_old=c1)

        # (a2) A retires-only link is not a rebinding: retirement is not transitive, so it cannot keep a name unique
        atoms_a2: dict[bytes, bytes] = {}
        v2_a2 = self._axiom(atoms_a2, "core/value", "new-a2", retires=[v1.id])
        c_a2 = self.repo.build_candidate_commit(
            "core", atoms_a2, [v2_a2], [V.Seal.sign(self.sk1, v2_a2.id, s0.id)], parent_commit=c1
        )
        with self.assertRaisesRegex(V.VarsError, "does not reach the prior binding"):
            self.repo.admit_and_advance("core", c_a2, expected_old=c1)

        # (b) Pending rebinding: V2 supersedes V1 but only sk2 signs (not V1's author, no 2-of-2 quorum).
        #     Admitted, yet V2 stays inactive until the edge is authorized; V1 remains the one binding.
        atoms_b: dict[bytes, bytes] = {}
        v2 = self._axiom(atoms_b, "core/value", "new", supersedes=[v1.id])
        c2 = self._admit(atoms_b, [v2], [V.Seal.sign(self.sk2, v2.id, s0.id)], c1)
        lens2 = self.repo.lens("core")
        self.assertEqual([cid for cid in (v1.id, v2.id) if lens2["active"][cid]], [v1.id])

        # (c) V1's author co-signs V2 later: the supersedes edge latches and the rebinding completes
        c2b = self._admit({}, [], [V.Seal.sign(self.sk1, v2.id, s0.id)], c2)
        lens2b = self.repo.lens("core")
        self.assertTrue(lens2b["active"][v2.id])
        self.assertTrue(lens2b["superseded"][v1.id])

        # (d) : V3 supersedes V2 (chain, 2-of-2), then V2 is invalidated by a 2-of-2 counterexample
        atoms_d: dict[bytes, bytes] = {}
        v3 = self._axiom(atoms_d, "core/value", "newer", supersedes=[v2.id])
        c3 = self._admit(atoms_d, [v3], [V.Seal.sign(self.sk1, v3.id, s0.id), V.Seal.sign(self.sk2, v3.id, s0.id)], c2b)
        atoms_e: dict[bytes, bytes] = {}
        x = self._axiom(atoms_e, "core/counterexample.v2", "V2 was false", invalidates=[v2.id])
        self._admit(atoms_e, [x], [V.Seal.sign(self.sk1, x.id, s0.id), V.Seal.sign(self.sk2, x.id, s0.id)], c3)
        lens4 = self.repo.lens("core")
        self.assertTrue(lens4["invalidated"][v2.id])
        self.assertTrue(lens4["active"][v3.id])
        self.assertFalse(lens4["active"][v1.id], "V1 must not resurrect beside V3 when the middle V2 is invalidated")
        same_name_active = [cid for cid in (v1.id, v2.id, v3.id) if lens4["active"][cid]]
        self.assertEqual(same_name_active, [v3.id], "exactly one Active binding of core/value")

    def test_08_late_cosign_on_verdict_counts_and_grants_no_author_rights(self) -> None:
        """A detached SEAL added after a VERDICT's birth counts toward its witness quorum,
        exactly as late seals already count for ACCEPTANCE latches and eviction edges."""
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=2, acc_threshold=2)
        atoms1: dict[bytes, bytes] = {}
        k = V.Cell(
            h_schema=V.H_SCHEMA["contract"],
            h_slot_name=self._put_atom(atoms1, V.atom_utf8("core/contract.k")),
            h_payload=self._put_atom(atoms1, V.atom_utf8("claim needing 2-of-2 attestation")),
            slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY),
        )
        w = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms1, V.atom_utf8("core/verdict.w")),
            h_payload=k.id,
            h_attests=self._hv(atoms1, [k.id]),
            slots=(V.H_EMPTY, V.H_ATTESTED, self._put_atom(atoms1, V.atom_utf8(SR.VERIFIER_ID))),
        )
        c1 = self._admit(atoms1, [k, w], [V.Seal.sign(self.sk1, k.id, s0.id), V.Seal.sign(self.sk1, w.id, s0.id)], c0)
        self.assertTrue(self.repo.lens("core")["provisional"][k.id])

        c2 = self._admit({}, [], [V.Seal.sign(self.sk2, w.id, s0.id)], c1)
        lens2 = self.repo.lens("core")
        self.assertTrue(lens2["settled"][k.id], "late co-signature by sk2 must complete the 2-of-2 witness quorum")

        # Guard: the late co-signer is not an author of W, so it cannot retire W alone
        atoms3: dict[bytes, bytes] = {}
        r = self._axiom(atoms3, "core/retire.w", "sk2 tries to retire W alone", retires=[w.id])
        self._admit(atoms3, [r], [V.Seal.sign(self.sk2, r.id, s0.id)], c2)
        lens3 = self.repo.lens("core")
        self.assertFalse(lens3["retired"][w.id], "a late co-signer must not gain AuthorCanEvict rights")
        self.assertTrue(lens3["settled"][k.id])

    def test_09_unassessed_parent_cannot_root_a_replayed_child(self) -> None:
        """ReplayVerified(P1) => ReplayVerified(P0). A NOT_ASSESSED parent carrying a fabricated
        state must not become the trusted start of a REPLAYED child."""
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=1, acc_threshold=2)
        atoms: dict[bytes, bytes] = {}
        # The task: input term I under an empty environment. Its true normal form is I itself.
        h_env = self._put_atom(atoms, V.atom_environment([]))
        comp_id = self._put_atom(atoms, V.atom_computation_root(V.H_I, h_env))
        # The lie: a terminal state whose term is K, made by swapping comp_id into an honest K state.
        app_ik = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=V.H_I, right=V.H_K)
        h_app_ik = V.sha256(app_ik)
        env_ik = SR.Environment([h_app_ik], {h_app_ik: app_ik})
        _, cid_ik = SR.root(h_app_ik, env_ik)
        doc0, id0, sb0 = SR.start(cid_ik, h_app_ik)
        honest = SR.advance(doc0, id0, sb0, env_ik, additional_credit=10)
        fake_state = b"SGS1" + comp_id + honest.state_bytes[36:]
        self.assertEqual(V.sgs1_term_hash(fake_state)[1], V.H_K)
        h_fake = self._put_atom(atoms, fake_state)
        peak = self._put_atom(atoms, V.atom_u64(honest.checkpoint["peak_semantic_size"]))
        big = self._put_atom(atoms, V.atom_u64(10_000_001))  # one ATP above the verifier ceiling
        zero = self._put_atom(atoms, V.atom_u64(0))

        comp = V.Cell(
            h_schema=V.H_SCHEMA["computation"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8("core/comp.fake")),
            h_payload=comp_id,
        )
        p0 = V.Cell(
            h_schema=V.H_SCHEMA["checkpoint"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8("core/ckpt.p0")),
            h_payload=h_fake,
            h_relies=self._hv(atoms, [comp.id]),
            slots=(comp_id, big, big, peak, self._put_atom(atoms, V.atom_utf8("PAUSED")), zero),
        )
        p1 = V.Cell(
            h_schema=V.H_SCHEMA["checkpoint"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8("core/ckpt.p1")),
            h_payload=h_fake,
            h_relies=self._hv(atoms, [comp.id, p0.id]),
            slots=(comp_id, big, big, peak, self._put_atom(atoms, V.atom_utf8("NORMAL_FORM")), zero),
        )
        k = V.Cell(
            h_schema=V.H_SCHEMA["contract"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8("core/contract.fake")),
            h_payload=self._put_atom(atoms, V.atom_utf8("I reduces to K")),
            h_relies=self._hv(atoms, [comp.id]),
            slots=(V.H_PROVISIONAL, comp_id, V.H_K, V.H_EMPTY),
        )
        w = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8("core/verdict.fake")),
            h_payload=k.id,
            h_relies=self._hv(atoms, [p1.id]),
            h_attests=self._hv(atoms, [k.id]),
            slots=(p1.id, V.H_REPLAYED, self._put_atom(atoms, V.atom_utf8(SR.VERIFIER_ID))),
        )
        cells = [comp, p0, p1, k, w]
        self._admit(atoms, cells, [V.Seal.sign(self.sk1, c.id, s0.id) for c in cells], c0)

        all_atoms = {**V.STD_SCHEMA_ATOMS, **atoms}
        all_cells = {c.id: c for c in cells}
        self.assertEqual(V.verify_checkpoint_replay(p0, all_atoms, all_cells, gate_mode=True), "NOT_ASSESSED")
        self.assertEqual(
            V.verify_checkpoint_replay(p1, all_atoms, all_cells, gate_mode=True),
            "NOT_ASSESSED",
            "a child replayed from a NOT_ASSESSED parent is itself NOT_ASSESSED",
        )
        with self.assertRaisesRegex(V.VarsError, "not replay-verified"):
            V.verify_checkpoint_replay(p1, all_atoms, all_cells, gate_mode=False)
        lens = self.repo.lens("core")
        self.assertFalse(lens["settled"][k.id], "Settled must not rest on a fabricated computation history")
        self.assertTrue(lens["provisional"][k.id])


    def test_10_scope_cells_use_the_reserved_scope_name(self) -> None:
        """Lean stage-1 finding: Rule 6 exempts scope cells, so a rotation could take the name of an Active
        binding and leave two Active cells with one H_slot_name. `<origin>/SCOPE` is now reserved both ways."""
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=1, acc_threshold=1)
        atoms1: dict[bytes, bytes] = {}
        v1 = self._axiom(atoms1, "core/value", "a binding")
        c1 = self._admit(atoms1, [v1], [V.Seal.sign(self.sk1, v1.id, s0.id)], c0)

        atoms2: dict[bytes, bytes] = {}
        h_pol = self._put_atom(atoms2, V.atom_pol1(1, self._hv(atoms2, [self.pk1, self.pk2])))
        s1 = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms2, V.atom_utf8("core/value")),
            h_payload=self._put_atom(atoms2, V.atom_utf8("core")),
            h_supersedes=self._hv(atoms2, [s0.id]),
            h_loss=self._put_atom(atoms2, V.atom_utf8("rotation squatting core/value")),
            slots=(h_pol, h_pol, V.H_LENS_KERNEL),
        )
        c2 = self.repo.build_candidate_commit("core", atoms2, [s1], [V.Seal.sign(self.sk1, s1.id, s0.id)], parent_commit=c1)
        with self.assertRaisesRegex(V.VarsError, "reserved scope name"):
            self.repo.admit_and_advance("core", c2, expected_old=c1)

        atoms3: dict[bytes, bytes] = {}
        squat = self._axiom(atoms3, "core/SCOPE", "a non-scope cell squatting the scope name")
        c3 = self.repo.build_candidate_commit("core", atoms3, [squat], [V.Seal.sign(self.sk1, squat.id, s0.id)], parent_commit=c1)
        with self.assertRaisesRegex(V.VarsError, "reserved scope name"):
            self.repo.admit_and_advance("core", c3, expected_old=c1)

    # ------------------------------------------------------------------------------------------
    # Rules decided by the kernel (§4.3): one scenario per fold refusal and per Pol_i row
    # ------------------------------------------------------------------------------------------
    def _genesis(self, adm: list[bytes], adm_thr: int, acc: list[bytes], acc_thr: int, signers: list[bytes],
                 scope: str = "core") -> tuple[str, V.Cell]:
        atoms = dict(V.STD_SCHEMA_ATOMS)
        s0 = V.Cell(
            h_schema=V.H_SCHEMA["scope"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8(f"{scope}/SCOPE")),
            h_payload=self._put_atom(atoms, V.atom_utf8(scope)),
            slots=(self._pol(atoms, adm_thr, adm), self._pol(atoms, acc_thr, acc), V.H_LENS_KERNEL),
        )
        c = self.repo.build_candidate_commit(scope, atoms, [*V.STD_SCHEMAS.values(), s0],
                                             [V.Seal.sign(sk, s0.id, s0.id) for sk in signers], parent_commit=None)
        self.repo.admit_and_advance(scope, c, expected_old=None)
        return c, s0

    def _pol(self, atoms: dict[bytes, bytes], thr: int, pks: list[bytes]) -> bytes:
        return self._put_atom(atoms, V.atom_pol1(thr, self._hv(atoms, sorted(pks))))

    def _refused(self, code: int, atoms: dict[bytes, bytes], cells: list, seals: list, parent: str) -> None:
        c = self.repo.build_candidate_commit("core", atoms, cells, seals, parent_commit=parent)
        with self.assertRaisesRegex(V.VarsError, rf"rules kernel E{code}:"):
            self.repo.admit_and_advance("core", c, expected_old=parent)

    def _scope_cell(self, atoms: dict[bytes, bytes], origin: str, payload: str, adm: tuple[int, list[bytes]],
                    **kw) -> V.Cell:
        pol = self._pol(atoms, *adm)
        return V.Cell(h_schema=V.H_SCHEMA["scope"], h_slot_name=self._put_atom(atoms, V.atom_utf8(f"{origin}/SCOPE")),
                      h_payload=self._put_atom(atoms, V.atom_utf8(payload)), slots=(pol, pol, V.H_LENS_KERNEL), **kw)

    def _contract(self, atoms: dict[bytes, bytes], name: str, tier: bytes, pol: bytes = V.H_EMPTY, **edges) -> V.Cell:
        kw = {f"h_{k}": self._hv(atoms, v) for k, v in edges.items()}
        if "h_supersedes" in kw:
            kw["h_loss"] = self._put_atom(atoms, V.atom_utf8(f"loss: {name}"))
        return V.Cell(h_schema=V.H_SCHEMA["contract"], h_slot_name=self._put_atom(atoms, V.atom_utf8(name)),
                      h_payload=self._put_atom(atoms, V.atom_utf8(f"statement {name}")),
                      slots=(tier, V.H_EMPTY, V.H_EMPTY, pol), **kw)

    def test_11_fold_refusals_are_decided_by_the_kernel(self) -> None:
        sk4 = b"\x04" * 32
        pk4 = V.ed25519_pubkey(sk4)
        # adm 1-of-{pk1}, acc 1-of-{pk2}: pk2 may seal only acceptance cells
        c0, s0 = self._genesis([self.pk1], 1, [self.pk2], 1, [self.sk1])

        a: dict[bytes, bytes] = {}
        ax = self._axiom(a, "core/ax", "sealed by an acceptance-only key")
        self._refused(-13, a, [ax], [V.Seal.sign(self.sk2, ax.id, s0.id)], c0)

        a = {}
        con = self._contract(a, "core/c", V.H_PROVISIONAL, self._pol(a, 1, [self.pk1, pk4]))
        self._refused(-16, a, [con], [V.Seal.sign(self.sk1, con.id, s0.id)], c0)

        # peerB: a self-sealed scope and one of its cells
        a = {}
        fb = self._scope_cell(a, "peerB", "peerB", (1, [self.pk_peer]))
        fx = self._axiom(a, "peerB/x", "a peerB fact")
        c1 = self._admit(a, [fb, fx], [V.Seal.sign(self.sk_peer, fb.id, fb.id), V.Seal.sign(self.sk_peer, fx.id, fb.id)], c0)
        self._refused(-14, {}, [], [V.Seal.sign(sk4, fx.id, s0.id)], c1)  # cross-seal by an outsider

        # peerC's scope needs 2-of-{peer, pk4} and carries one self-seal: its cells have no self-sealed scope
        a = {}
        fc = self._scope_cell(a, "peerC", "peerC", (2, [self.pk_peer, pk4]))
        fy = self._axiom(a, "peerC/y", "a peerC fact")
        self._refused(-17, a, [fc, fy], [V.Seal.sign(self.sk_peer, fc.id, fc.id), V.Seal.sign(self.sk_peer, fy.id, fc.id)], c1)

        # an acceptance pinned to a second, unsealed peerB scope
        a = {}
        fb2 = self._scope_cell(a, "peerB", "peerB#2", (1, [self.pk_peer]))
        acc = V.Cell(h_schema=V.H_SCHEMA["acceptance"], h_slot_name=self._put_atom(a, V.atom_utf8("core/acc")),
                     h_payload=fx.id, slots=(self._put_atom(a, V.atom_utf8("peerB")), fb2.id))
        self._refused(-21, a, [fb2, acc], [V.Seal.sign(self.sk2, acc.id, s0.id)], c1)

        # a rotation that also retires a cell
        a = {}
        rot = self._scope_cell(a, "core", "core#bad", (1, [self.pk1]), h_supersedes=self._hv(a, [s0.id]),
                               h_retires=self._hv(a, [fx.id]), h_loss=self._put_atom(a, V.atom_utf8("rotation")))
        self._refused(-19, a, [rot], [V.Seal.sign(self.sk1, rot.id, s0.id)], c1)

        # after a rotation, a seal under the old scope
        a = {}
        s1 = self._scope_cell(a, "core", "core#1", (1, [self.pk1]), h_supersedes=self._hv(a, [s0.id]),
                              h_loss=self._put_atom(a, V.atom_utf8("rotation")))
        c2 = self._admit(a, [s1], [V.Seal.sign(self.sk1, s1.id, s0.id)], c1)
        a = {}
        ax = self._axiom(a, "core/late", "sealed under the superseded scope")
        self._refused(-12, a, [ax], [V.Seal.sign(self.sk1, ax.id, s0.id)], c2)

    def test_12_quorum_refusals_at_genesis_and_rotation(self) -> None:
        atoms = dict(V.STD_SCHEMA_ATOMS)
        g = self._scope_cell(atoms, "gov", "gov", (2, [self.pk1, self.pk2]))
        c = self.repo.build_candidate_commit("gov", atoms, [*V.STD_SCHEMAS.values(), g],
                                             [V.Seal.sign(self.sk1, g.id, g.id)], parent_commit=None)
        with self.assertRaisesRegex(V.VarsError, r"rules kernel E-11:"):
            self.repo.admit_and_advance("gov", c, expected_old=None)

        c0, s0 = self._genesis([self.pk1, self.pk2], 2, [self.pk1, self.pk2], 1, [self.sk1, self.sk2])
        a: dict[bytes, bytes] = {}
        s1 = self._scope_cell(a, "core", "core#1", (1, [self.pk1]), h_supersedes=self._hv(a, [s0.id]),
                              h_loss=self._put_atom(a, V.atom_utf8("rotation")))
        self._refused(-20, a, [s1], [V.Seal.sign(self.sk1, s1.id, s0.id)], c0)

    def test_13_governing_policy_rows(self) -> None:
        """Pol_i(v): a provisional contract or question is evicted under its evaluator policy; an owner contract only
        under the admission quorum, never by its author; an ATTESTED verdict never invalidates."""
        c0, s0 = self._genesis([self.pk1, self.pk2], 2, [self.pk1, self.pk2], 1, [self.sk1, self.sk2])
        a: dict[bytes, bytes] = {}
        pol2 = self._pol(a, 1, [self.pk2])
        v_con = self._contract(a, "core/c", V.H_PROVISIONAL, pol2)
        q_text = self._put_atom(a, V.atom_utf8("a question"))
        v_q = V.Cell(h_schema=V.H_SCHEMA["question"], h_slot_name=self._put_atom(a, V.atom_utf8("core/q")),
                     h_payload=q_text, slots=(V.H_SCHEMA["axiom"], pol2))
        v_own = self._contract(a, "core/o", V.H_OWNER)
        target = self._contract(a, "core/t", V.H_PROVISIONAL)
        c1 = self._admit(a, [v_con, v_q, v_own, target],
                         [V.Seal.sign(self.sk1, x.id, s0.id) for x in (v_con, v_q, v_own)]
                         + [V.Seal.sign(sk, target.id, s0.id) for sk in (self.sk1, self.sk2)], c0)

        a = {}
        w_con = self._contract(a, "core/c", V.H_PROVISIONAL, pol2, supersedes=[v_con.id])
        w_q = V.Cell(h_schema=V.H_SCHEMA["question"], h_slot_name=v_q.h_slot_name, h_payload=self._put_atom(a, V.atom_utf8("q2")),
                     slots=(V.H_SCHEMA["axiom"], pol2), h_supersedes=self._hv(a, [v_q.id]),
                     h_loss=self._put_atom(a, V.atom_utf8("loss: q")))
        w_own = self._contract(a, "core/o", V.H_OWNER, supersedes=[v_own.id])
        vid = self._put_atom(a, V.atom_utf8("a verifier"))
        attested = V.Cell(h_schema=V.H_SCHEMA["verdict"], h_slot_name=self._put_atom(a, V.atom_utf8("core/v")),
                          h_payload=target.id, slots=(V.H_EMPTY, V.H_ATTESTED, vid),
                          h_attests=self._hv(a, [target.id]), h_invalidates=self._hv(a, [target.id]))
        self._admit(a, [w_con, w_q, w_own, attested],
                    [V.Seal.sign(self.sk2, w_con.id, s0.id), V.Seal.sign(self.sk2, w_q.id, s0.id),
                     V.Seal.sign(self.sk1, w_own.id, s0.id)]
                    + [V.Seal.sign(sk, attested.id, s0.id) for sk in (self.sk1, self.sk2)], c1)
        lens = self.repo.lens("core")
        self.assertTrue(lens["superseded"][v_con.id] and lens["active"][w_con.id], "evaluator policy 1-of-{pk2} evicts")
        self.assertTrue(lens["superseded"][v_q.id] and lens["active"][w_q.id], "question evaluator policy evicts")
        self.assertFalse(lens["superseded"][v_own.id] or lens["active"][w_own.id], "owner tier: author alone cannot evict")
        self.assertTrue(lens["effective"][target.id], "an ATTESTED verdict's invalidates edge has no effect")


    def test_40_projection_is_recomputed_at_the_gate_and_settled_by_witnesses(self) -> None:
        """A projection Π = (tip, rules, input, state) is admitted only if the gate's own recomputation of the rules
        at `tip` gives the same input and state digests; it is Settled once its witness policy has signed it."""
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=2, acc_threshold=2)
        atoms1: dict[bytes, bytes] = {}
        ax = self._axiom(atoms1, "core/fact", "a fact")
        c1 = self._admit(atoms1, [ax], [V.Seal.sign(self.sk1, ax.id, s0.id)], c0)

        h_in, h_state = self.repo.projection_digests("core", c1)
        self.assertEqual(len(h_in), 32)
        self.assertEqual(len(h_state), 32)

        def projection(atoms: dict[bytes, bytes], name: str, tip: str, state: bytes) -> V.Cell:
            return V.Cell(
                h_schema=V.H_SCHEMA["projection"],
                h_slot_name=self._put_atom(atoms, V.atom_utf8(name)),
                h_payload=V.H_EMPTY,
                slots=(
                    self._put_atom(atoms, V.atom_utf8(tip)),
                    V.H_LENS_KERNEL,
                    h_in,
                    state,
                    self._put_atom(atoms, V.atom_pol1(2, self._hv(atoms, [self.pk1, self.pk2]))),
                ),
            )

        # A false state digest is refused: the gate recomputes it
        atoms_bad: dict[bytes, bytes] = {}
        bad = projection(atoms_bad, "core/projection.bad", c1, bytes(32))
        c_bad = self.repo.build_candidate_commit("core", atoms_bad, [bad], [V.Seal.sign(self.sk1, bad.id, s0.id)], parent_commit=c1)
        with self.assertRaisesRegex(V.VarsError, "projection"):
            self.repo.admit_and_advance("core", c_bad, expected_old=c1)

        # A tip outside the chain is refused
        atoms_off: dict[bytes, bytes] = {}
        off = projection(atoms_off, "core/projection.off", "0" * 40, h_state)
        c_off = self.repo.build_candidate_commit("core", atoms_off, [off], [V.Seal.sign(self.sk1, off.id, s0.id)], parent_commit=c1)
        with self.assertRaisesRegex(V.VarsError, "projection"):
            self.repo.admit_and_advance("core", c_off, expected_old=c1)

        # The true projection is admitted; one witness of 2-of-2 leaves it Provisional, the second settles it
        atoms2: dict[bytes, bytes] = {}
        good = projection(atoms2, "core/projection.c1", c1, h_state)
        c2 = self._admit(atoms2, [good], [V.Seal.sign(self.sk1, good.id, s0.id)], c1)
        self.assertTrue(self.repo.lens("core")["provisional"][good.id])
        self._admit({}, [], [V.Seal.sign(self.sk2, good.id, s0.id)], c2)
        self.assertTrue(self.repo.lens("core")["settled"][good.id])


    def _projection(self, atoms: dict[bytes, bytes], name: str, tip: str, witnesses: list[bytes], thr: int,
                    **edges: list[bytes]) -> V.Cell:
        h_in, h_state = self.repo.projection_digests("core", tip)
        kw = {f"h_{k}": self._hv(atoms, v) for k, v in edges.items()}
        return V.Cell(
            h_schema=V.H_SCHEMA["projection"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8(name)),
            h_payload=V.H_EMPTY,
            slots=(self._put_atom(atoms, V.atom_utf8(tip)), V.H_LENS_KERNEL, h_in, h_state,
                   self._put_atom(atoms, V.atom_pol1(thr, self._hv(atoms, witnesses)))),
            **kw,
        )

    def test_41_witness_outside_the_roster_signs_a_projection(self) -> None:
        """A projection's witnesses need not be in the scope's roster: a key of its witness_policy may seal that
        projection, and only that projection. Writing it still needs a roster seal."""
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=1, acc_threshold=1)
        atoms1: dict[bytes, bytes] = {}
        ax = self._axiom(atoms1, "core/fact", "a fact")
        c1 = self._admit(atoms1, [ax], [V.Seal.sign(self.sk1, ax.id, s0.id)], c0)

        # Only the outside witness signs: refused, nobody in the roster wrote it
        atoms_w: dict[bytes, bytes] = {}
        lone = self._projection(atoms_w, "core/projection.lone", c1, [self.pk_peer], 1)
        c_lone = self.repo.build_candidate_commit("core", atoms_w, [lone], [V.Seal.sign(self.sk_peer, lone.id, s0.id)], parent_commit=c1)
        with self.assertRaises(V.VarsError):
            self.repo.admit_and_advance("core", c_lone, expected_old=c1)

        # A roster key writes it and the outside witness signs it: admitted and Settled by the witness alone
        atoms2: dict[bytes, bytes] = {}
        proj = self._projection(atoms2, "core/projection.c1", c1, [self.pk_peer], 1)
        c2 = self._admit(atoms2, [proj], [V.Seal.sign(self.sk1, proj.id, s0.id), V.Seal.sign(self.sk_peer, proj.id, s0.id)], c1)
        self.assertTrue(self.repo.lens("core")["settled"][proj.id])

        # The witness key has no other power: it cannot seal an ordinary local cell
        atoms3: dict[bytes, bytes] = {}
        other = self._axiom(atoms3, "core/other", "not a projection")
        c3 = self.repo.build_candidate_commit("core", atoms3, [other],
                                              [V.Seal.sign(self.sk1, other.id, s0.id), V.Seal.sign(self.sk_peer, other.id, s0.id)], parent_commit=c2)
        with self.assertRaises(V.VarsError):
            self.repo.admit_and_advance("core", c3, expected_old=c2)

    def test_42_projections_are_immutable_historical_facts(self) -> None:
        """A projection states the rules' result at an earlier commit and the gate has recomputed it, so nothing can
        evict it and it has no edges: its Settled status is exactly its witness quorum, which a client can check."""
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=1, acc_threshold=1)
        atoms1: dict[bytes, bytes] = {}
        ax = self._axiom(atoms1, "core/fact", "a fact")
        c1 = self._admit(atoms1, [ax], [V.Seal.sign(self.sk1, ax.id, s0.id)], c0)
        atoms2: dict[bytes, bytes] = {}
        proj = self._projection(atoms2, "core/projection.c1", c1, [self.pk1], 1)
        c2 = self._admit(atoms2, [proj], [V.Seal.sign(self.sk1, proj.id, s0.id)], c1)
        self.assertTrue(self.repo.lens("core")["settled"][proj.id])

        for kind in ("invalidates", "retires"):
            atoms3: dict[bytes, bytes] = {}
            x = self._axiom(atoms3, f"core/evict.{kind}", "try to evict the projection", **{kind: [proj.id]})
            c3 = self.repo.build_candidate_commit("core", atoms3, [x], [V.Seal.sign(self.sk1, x.id, s0.id)], parent_commit=c2)
            with self.assertRaisesRegex(V.VarsError, "projection"):
                self.repo.admit_and_advance("core", c3, expected_old=c2)

        atoms4: dict[bytes, bytes] = {}
        with_edge = self._projection(atoms4, "core/projection.edge", c1, [self.pk1], 1, relies=[ax.id])
        c4 = self.repo.build_candidate_commit("core", atoms4, [with_edge], [V.Seal.sign(self.sk1, with_edge.id, s0.id)], parent_commit=c2)
        with self.assertRaisesRegex(V.VarsError, "projection"):
            self.repo.admit_and_advance("core", c4, expected_old=c2)


    def test_14_light_client_verifies_a_projection_bundle_without_the_repository(self) -> None:
        """A client holding only a projection bundle checks its witness seals, and, given the kernel's input and
        output bytes, checks them against the projection and reads the statuses by cell id."""
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=1, acc_threshold=1)
        atoms1: dict[bytes, bytes] = {}
        ax = self._axiom(atoms1, "core/fact", "a fact")
        c1 = self._admit(atoms1, [ax], [V.Seal.sign(self.sk1, ax.id, s0.id)], c0)
        atoms2: dict[bytes, bytes] = {}
        proj = self._projection(atoms2, "core/projection.c1", c1, [self.pk1, self.pk_peer], 2)
        c2 = self._admit(atoms2, [proj], [V.Seal.sign(self.sk1, proj.id, s0.id)], c1)

        one = V.export_projection(self.repo, "core", proj.id)
        r1 = V.verify_projection(json.loads(json.dumps(one)))
        self.assertFalse(r1["witnessed"], "1 of 2 witnesses has signed")
        self.assertEqual(r1["tip"], c1)

        self._admit({}, [], [V.Seal.sign(self.sk_peer, proj.id, s0.id)], c2)
        bundle = json.loads(json.dumps(V.export_projection(self.repo, "core", proj.id)))
        r2 = V.verify_projection(bundle)
        self.assertTrue(r2["witnessed"])
        self.assertTrue(r2["data_ok"])
        self.assertTrue(r2["statuses"][ax.id.hex()]["active"], "the fact is Active at the projection's tip")
        self.assertEqual(r2["scope"], s0.id.hex())

        # Tampering is an error, never a quieter answer
        bad_out = dict(bundle, output=bundle["output"][:-2] + ("00" if bundle["output"][-2:] != "00" else "01"))
        with self.assertRaisesRegex(V.VarsError, "state"):
            V.verify_projection(bad_out)
        other = V.Seal.sign(self.sk_peer, ax.id, s0.id).encode().hex()
        with self.assertRaisesRegex(V.VarsError, "seal"):
            V.verify_projection(dict(bundle, seals=bundle["seals"] + [other]))

        # The same check from the command line, with no repository
        path = Path(self.tmp.name) / "bundle.json"
        path.write_text(json.dumps(bundle))
        out = subprocess.run([sys.executable, str(ROOT_DIR / "vars1.py"), "inspect-projection", str(path)],
                             capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertTrue(json.loads(out.stdout)["witnessed"])


    def test_15_minds_governs_itself(self) -> None:
        """tools/minds_chain.py on a scratch repository: genesis, two releases, each a Settled decision attested by
        the maintainer plus a witnessed projection of the chain that a client verifies from a bundle."""
        import importlib.util
        spec = importlib.util.spec_from_file_location("minds_chain", ROOT_DIR / "tools" / "minds_chain.py")
        mc = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mc)
        sk = b"\x07" * 32
        mc.init(self.repo_path, sk)
        c1, ids1 = mc.release(self.repo_path, sk, "a" * 40, ["test_vars1 OK"])
        c2, ids2 = mc.release(self.repo_path, sk, "b" * 40, ["test_vars1 OK", "lake build OK"])
        rows = {r["name"]: r for r in mc.show(self.repo_path)}
        self.assertTrue(rows["minds/release/aaaaaaaaaaaa"]["settled"])
        self.assertIn("main@" + "b" * 40, rows["minds/release/bbbbbbbbbbbb"]["statement"])
        self.assertTrue(all(r["settled"] for r in rows.values()))
        bundle = V.export_projection(V.GitVarsRepo(self.repo_path), "minds", ids2["projection"])
        r = V.verify_projection(json.loads(json.dumps(bundle)))
        self.assertTrue(r["witnessed"] and r["data_ok"])
        self.assertEqual(r["tip"], c1)
        self.assertTrue(r["statuses"][ids1["decision"].hex()]["active"])
        with self.assertRaises(V.VarsError):
            mc.init(self.repo_path, sk)


    def test_16_light_client_verifies_a_release_attestation(self) -> None:
        """A client holding only an attestation bundle recomputes Pass 3 for a decision: maintainer-attested, not
        contradicted, and — with a later projection — Active and not Stale at that projection's tip."""
        import importlib.util
        spec = importlib.util.spec_from_file_location("minds_chain", ROOT_DIR / "tools" / "minds_chain.py")
        mc = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mc)
        sk = b"\x07" * 32
        mc.init(self.repo_path, sk)
        c1, ids1 = mc.release(self.repo_path, sk, "a" * 40, ["test_vars1 OK"])
        c2, ids2 = mc.release(self.repo_path, sk, "b" * 40, ["test_vars1 OK"])  # its projection's tip is c1
        repo = V.GitVarsRepo(self.repo_path)

        bundle = json.loads(json.dumps(V.export_attestation(repo, "minds", ids1["decision"], ids2["projection"])))
        r = V.verify_attestation(bundle)
        self.assertTrue(r["attested"])
        self.assertIn("main@" + "a" * 40, r["statement"])
        self.assertEqual(r["authors"], [V.ed25519_pubkey(sk).hex()])
        self.assertEqual(r["tip"], c1)
        self.assertTrue(r["active_at_tip"])
        self.assertEqual(r["evidence"], "complete_at_tip")
        self.assertTrue(r["attested_at_tip"])
        self.assertTrue(r["accepted"])
        self.assertTrue(repo.lens("minds")["settled"][ids1["decision"]], "the bundle agrees with the full lens")

        # Without the maintainer's seal on the verdict there is no attestation; a stranger's seal does not count
        verdict_id = ids1["verdict"].hex()
        def seals_on(b, cid_hex):
            return [x for x in b["seals"] if V.Seal.decode(bytes.fromhex(x)).h_target.hex() == cid_hex]
        stripped = dict(bundle, seals=[x for x in bundle["seals"] if x not in seals_on(bundle, verdict_id)])
        self.assertFalse(V.verify_attestation(stripped)["attested"])
        scope_id = V.Cell.decode(bytes.fromhex(bundle["scope"])).id
        stranger = V.Seal.sign(b"\x09" * 32, ids1["verdict"], scope_id).encode().hex()
        self.assertFalse(V.verify_attestation(dict(stripped, seals=stripped["seals"] + [stranger]))["attested"])

        # A verdict about another cell, or a seal on an unrelated cell, is a refusal
        other = V.Cell.decode(bytes.fromhex(V.export_attestation(repo, "minds", ids2["decision"])["verdicts"][0]))
        with self.assertRaisesRegex(V.VarsError, "verdict"):
            V.verify_attestation(dict(bundle, verdicts=bundle["verdicts"] + [other.encode().hex()]))

        # A contradicting INVALID verdict by the maintainer, under the same verifier, withdraws the attestation
        atoms: dict[bytes, bytes] = {}
        d1 = ids1["decision"]
        bad = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8("minds/release/aaaaaaaaaaaa/contradicted")),
            h_payload=d1,
            h_attests=self._hv(atoms, [d1]),
            slots=(V.H_EMPTY, V.H_VERDICT_INVALID, self._put_atom(atoms, V.atom_utf8("minds-maintainer"))),
        )
        tip = repo.ref_commit("minds")
        c3 = repo.build_candidate_commit("minds", atoms, [bad], [V.Seal.sign(sk, bad.id, scope_id)], parent_commit=tip)
        repo.admit_and_advance("minds", c3, expected_old=tip)
        r3 = V.verify_attestation(json.loads(json.dumps(V.export_attestation(repo, "minds", d1))))
        self.assertFalse(r3["attested"], "a contradicting INVALID verdict blocks the attestation, as in Pass 3")

        path = Path(self.tmp.name) / "attestation.json"
        path.write_text(json.dumps(bundle))
        out = subprocess.run([sys.executable, str(ROOT_DIR / "vars1.py"), "inspect-attestation", str(path)],
                             capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)

    def _minds_chain(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location("minds_chain", ROOT_DIR / "tools" / "minds_chain.py")
        mc = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mc)
        return mc

    def test_17_attestation_evidence_is_complete_at_the_projection_tip(self) -> None:
        """A supplier cannot hide a verdict or a seal the projection's tip holds; acceptance needs a witnessed
        projection; without one the result is only what the supplied evidence supports (Monday F34, F35)."""
        mc = self._minds_chain()
        sk = b"\x07" * 32
        mc.init(self.repo_path, sk)
        _, ids1 = mc.release(self.repo_path, sk, "a" * 40, ["test_vars1 OK"])
        repo = V.GitVarsRepo(self.repo_path)
        d1 = ids1["decision"]
        scope_id = mc.governing_scope(repo)
        atoms: dict[bytes, bytes] = {}
        bad = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8("minds/release/aaaaaaaaaaaa/contradicted")),
            h_payload=d1,
            h_attests=self._hv(atoms, [d1]),
            slots=(V.H_EMPTY, V.H_VERDICT_INVALID, self._put_atom(atoms, V.atom_utf8("minds-maintainer"))),
        )
        tip = repo.ref_commit("minds")
        c_bad = repo.build_candidate_commit("minds", atoms, [bad], [V.Seal.sign(sk, bad.id, scope_id)], parent_commit=tip)
        repo.admit_and_advance("minds", c_bad, expected_old=tip)
        _, ids2 = mc.release(self.repo_path, sk, "b" * 40, ["test_vars1 OK"])  # its projection's tip holds `bad`

        bundle = json.loads(json.dumps(V.export_attestation(repo, "minds", d1, ids2["projection"])))
        r = V.verify_attestation(bundle)
        self.assertEqual((r["evidence"], r["attested"], r["attested_at_tip"], r["accepted"]),
                         ("complete_at_tip", False, False, False))

        # Hiding the INVALID verdict succeeds on supplied evidence alone — hence `evidence: supplied` — and is a
        # refusal once a projection holds the cell
        not_bad = lambda x: V.Seal.decode(bytes.fromhex(x)).h_target != bad.id
        hidden = dict(bundle, verdicts=[v for v in bundle["verdicts"] if v != bad.encode().hex()],
                      seals=[x for x in bundle["seals"] if not_bad(x)])
        alone = V.verify_attestation({k: v for k, v in hidden.items() if k != "projection"})
        self.assertEqual((alone["evidence"], alone["attested"], alone["accepted"]), ("supplied", True, False))
        with self.assertRaisesRegex(V.VarsError, "omits 1 verdict"):
            V.verify_attestation(hidden)

        # Hiding only the seals on it fools the supplied computation, not the tip's
        r = V.verify_attestation(dict(bundle, seals=[x for x in bundle["seals"] if not_bad(x)]))
        self.assertEqual((r["attested"], r["attested_at_tip"], r["accepted"]), (True, False, False))

        # An unwitnessed projection is not acceptance, and the CLI says so by its exit code
        _, ids3 = mc.release(self.repo_path, sk, "c" * 40, ["test_vars1 OK"])
        good = json.loads(json.dumps(V.export_attestation(repo, "minds", ids2["decision"], ids3["projection"])))
        self.assertTrue(V.verify_attestation(good)["accepted"])
        unwitnessed = dict(good, projection=dict(good["projection"], seals=[]))
        r = V.verify_attestation(unwitnessed)
        self.assertEqual((r["attested_at_tip"], r["active_at_tip"], r["projection_witnessed"], r["accepted"]),
                         (True, True, False, False))
        for b, code in ((good, 0), (unwitnessed, 1), ({k: v for k, v in good.items() if k != "projection"}, 1)):
            path = Path(self.tmp.name) / "attestation.json"
            path.write_text(json.dumps(b))
            out = subprocess.run([sys.executable, str(ROOT_DIR / "vars1.py"), "inspect-attestation", str(path)],
                                 capture_output=True, text=True)
            self.assertEqual(out.returncode, code, out.stdout + out.stderr)

    def test_18_release_refuses_unless_head_is_main_and_clean(self) -> None:
        """`release` records main@SHA only when the checks run on exactly that commit (Monday F33)."""
        mc = self._minds_chain()
        work = Path(self.tmp.name) / "work"
        work.mkdir()
        g = lambda *a: subprocess.run(["git", "-C", str(work), "-c", "user.name=t", "-c", "user.email=t@t", *a],
                                      capture_output=True, text=True, check=True).stdout
        g("init", "-q", "-b", "main")
        g("commit", "-q", "--allow-empty", "-m", "one")
        self.assertEqual(mc.release_target(work), (g("rev-parse", "main").strip(), None))
        g("checkout", "-q", "-b", "other")
        g("commit", "-q", "--allow-empty", "-m", "two")
        self.assertIn("HEAD is not main", mc.release_target(work)[1] or "")
        g("checkout", "-q", "--detach", "main")
        self.assertIsNone(mc.release_target(work)[1], "a detached HEAD at main's commit is that commit")
        g("checkout", "-q", "main")
        (work / "x").write_text("x")
        self.assertIn("not clean", mc.release_target(work)[1] or "")

    def test_19_a_second_member_verifies_releases(self) -> None:
        """After `join`, a release is settled, and its projection witnessed, only when every member has attested and
        sealed: one key alone no longer suffices. A member's verdict follows the checks it ran itself."""
        mc = self._minds_chain()
        sk, sk2 = b"\x07" * 32, b"\x08" * 32
        mc.init(self.repo_path, sk)
        repo = V.GitVarsRepo(self.repo_path)
        _, r1 = mc.release(self.repo_path, sk, "a" * 40, ["test_vars1 OK"])
        mc.join(self.repo_path, sk, V.ed25519_pubkey(sk2), "second")
        self.assertEqual(mc.roster(repo), sorted([V.ed25519_pubkey(sk), V.ed25519_pubkey(sk2)]))
        with self.assertRaisesRegex(V.VarsError, "already a member"):
            mc.join(self.repo_path, sk, V.ed25519_pubkey(sk2), "second")
        _, r2 = mc.release(self.repo_path, sk, "b" * 40, ["test_vars1 OK"])
        lens = repo.lens("minds")
        self.assertTrue(lens["settled"][r1["decision"]], "a release before the join stays settled")
        self.assertFalse(lens["settled"][r2["decision"]], "the maintainer alone no longer settles a release")
        self.assertFalse(lens["settled"][r2["projection"]], "nor witnesses a projection")
        b = json.loads(json.dumps(V.export_attestation(repo, "minds", r1["decision"], r2["projection"])))
        self.assertFalse(V.verify_attestation(b)["accepted"])

        seen = []
        def fake(repo_dir, sha, rules, ok=True):
            seen.append((sha, rules))
            return ["test_vars1 OK" if ok else "test_vars1 FAILED"], ok
        with self.assertRaisesRegex(V.VarsError, "not on the roster"):
            mc.verify_release(self.repo_path, b"\x09" * 32, r2["decision"], "stranger", checks=fake)
        _, ok, _ = mc.verify_release(self.repo_path, sk2, r2["decision"], "second", checks=fake)
        self.assertTrue(ok)
        self.assertEqual(seen, [("b" * 40, V.H_LENS_KERNEL)], "the checks ran on the commit the release names")
        with self.assertRaisesRegex(V.VarsError, "already recorded"):
            mc.verify_release(self.repo_path, sk2, r2["decision"], "second", checks=fake)
        lens = repo.lens("minds")
        self.assertTrue(lens["settled"][r2["decision"]])
        self.assertTrue(lens["settled"][r2["projection"]])
        self.assertEqual(mc.covering_projection(repo, r1["decision"]), r2["projection"])
        b = json.loads(json.dumps(V.export_attestation(repo, "minds", r1["decision"], r2["projection"])))
        self.assertTrue(V.verify_attestation(b)["accepted"])

        # The second member's failed checks leave the next release unsettled, however the maintainer votes
        _, r3 = mc.release(self.repo_path, sk, "c" * 40, ["test_vars1 OK"])
        self.assertEqual(mc.covering_projection(repo, r1["decision"]), r2["projection"],
                         "a witnessed projection is preferred over a later unwitnessed one")
        _, ok, _ = mc.verify_release(self.repo_path, sk2, r3["decision"], "second",
                                     checks=lambda *a: fake(*a, ok=False))
        self.assertFalse(ok)
        lens = repo.lens("minds")
        self.assertFalse(lens["settled"][r3["decision"]])
        self.assertTrue(lens["settled"][r3["projection"]], "witnessing the chain does not depend on the checks")
        b = json.loads(json.dumps(V.export_attestation(repo, "minds", r2["decision"], r3["projection"])))
        r = V.verify_attestation(b)
        self.assertTrue(r["accepted"])
        self.assertEqual(len(r["endorsers_at_tip"]), 2)

    def test_20_checks_at_runs_in_a_worktree_at_the_released_commit(self) -> None:
        mc = self._minds_chain()
        work = Path(self.tmp.name) / "proj" / "minds"
        work.mkdir(parents=True)
        g = lambda *a: subprocess.run(["git", "-C", str(work), "-c", "user.name=t", "-c", "user.email=t@t", *a],
                                      capture_output=True, text=True, check=True).stdout.strip()
        g("init", "-q", "-b", "main")
        (work / "f").write_text("one")
        g("add", "f")
        g("commit", "-q", "-m", "one")
        first = g("rev-parse", "HEAD")
        (work / "f").write_text("two")
        g("commit", "-q", "-am", "two")
        got = {}
        def spy(root, rules):
            got.update(head=subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True,
                                           text=True).stdout.strip(), f=(root / "f").read_text(), rules=rules,
                       sibling=(root.parent / "sigma-glyph").exists())
            return ["spy OK"], True
        real, mc.run_checks = mc.run_checks, spy
        try:
            self.assertEqual(mc.checks_at(work, first, b"\x01" * 32), (["spy OK"], True))
        finally:
            mc.run_checks = real
        self.assertEqual(got, {"head": first, "f": "one", "rules": b"\x01" * 32, "sibling": False},
                         "nothing beside the worktree: the commit carries its dependencies")
        self.assertEqual(g("worktree", "list", "--porcelain").count("worktree "), 1, "the worktree is removed")
        self.assertEqual((work / "f").read_text(), "two", "the checkout itself is untouched")
        g("checkout", "-q", "-b", "side")
        g("commit", "-q", "--allow-empty", "-m", "side")
        side = g("rev-parse", "HEAD")
        g("checkout", "-q", "main")
        real, mc.run_checks = mc.run_checks, spy
        try:
            with self.assertRaises(subprocess.CalledProcessError, msg="a commit not on main is not a release"):
                mc.checks_at(work, side, V.H_LENS_KERNEL)
        finally:
            mc.run_checks = real

    def test_21_attestation_counts_what_the_lens_counts(self) -> None:
        """An INVALID verdict that judges the cell without attesting it still contradicts it in Pass 3, so a bundle
        must carry it; an INVALID verdict recorded after the projection's tip withdraws acceptance."""
        mc = self._minds_chain()
        sk = b"\x07" * 32
        mc.init(self.repo_path, sk)
        repo = V.GitVarsRepo(self.repo_path)
        _, r1 = mc.release(self.repo_path, sk, "a" * 40, ["test_vars1 OK"])
        _, r2 = mc.release(self.repo_path, sk, "b" * 40, ["test_vars1 OK"])
        d1 = r1["decision"]
        self.assertTrue(V.verify_attestation(V.export_attestation(repo, "minds", d1, r2["projection"]))["accepted"])

        atoms: dict[bytes, bytes] = {}
        bad = V.Cell(
            h_schema=V.H_SCHEMA["verdict"],
            h_slot_name=self._put_atom(atoms, V.atom_utf8("minds/release/aaaaaaaaaaaa/withdrawn")),
            h_payload=d1,
            slots=(V.H_EMPTY, V.H_VERDICT_INVALID, self._put_atom(atoms, V.atom_utf8("minds-maintainer"))),
        )
        tip = repo.ref_commit("minds")
        c = repo.build_candidate_commit("minds", atoms, [bad], [V.Seal.sign(sk, bad.id, mc.governing_scope(repo))],
                                        parent_commit=tip)
        repo.admit_and_advance("minds", c, expected_old=tip)
        self.assertFalse(repo.lens("minds")["settled"][d1], "the lens: a non-attesting INVALID still contradicts")

        # After p2's tip: the supplied INVALID withdraws acceptance, though Pass 3 at the tip still settles
        r = V.verify_attestation(json.loads(json.dumps(V.export_attestation(repo, "minds", d1, r2["projection"]))))
        self.assertEqual((r["attested_at_tip"], r["contradicted_after_tip"], r["accepted"]), (True, True, False))

        # Within p3's tip: Pass 3 there agrees with the lens, and the bundle cannot leave the verdict out
        _, r3 = mc.release(self.repo_path, sk, "c" * 40, ["test_vars1 OK"])
        b = json.loads(json.dumps(V.export_attestation(repo, "minds", d1, r3["projection"])))
        r = V.verify_attestation(b)
        self.assertEqual((r["evidence"], r["attested_at_tip"], r["accepted"]), ("complete_at_tip", False, False))
        hidden = dict(b, verdicts=[v for v in b["verdicts"] if v != bad.encode().hex()],
                      seals=[x for x in b["seals"] if V.Seal.decode(bytes.fromhex(x)).h_target != bad.id])
        with self.assertRaisesRegex(V.VarsError, "omits 1 verdict"):
            V.verify_attestation(hidden)

    def test_22_one_member_can_rotate_the_other_out_but_a_reader_pin_holds(self) -> None:
        """Monday F36: admission is 1-of-n, so one member alone may rotate the roster down to itself, after which its
        releases settle on the chain without the other. A reader who pins both keys still refuses them."""
        mc = self._minds_chain()
        ska, skb = b"\x07" * 32, b"\x08" * 32
        pka, pkb = V.ed25519_pubkey(ska), V.ed25519_pubkey(skb)
        mc.init(self.repo_path, ska)
        repo = V.GitVarsRepo(self.repo_path)
        mc.join(self.repo_path, ska, pkb, "bob")
        _, r1 = mc.release(self.repo_path, ska, "a" * 40, ["test_vars1 OK"])  # bob never attests r1

        # Alice alone rotates Bob out: the gate admits it, as §3 check 1 asks only the admission quorum
        atoms: dict[bytes, bytes] = {}
        s = mc.governing_scope(repo)
        pol = self._pol(atoms, 1, [pka])
        solo = V.Cell(h_schema=V.H_SCHEMA["scope"], h_slot_name=self._put_atom(atoms, V.atom_utf8("minds/SCOPE")),
                      h_payload=self._put_atom(atoms, V.atom_utf8("alice alone")),
                      h_supersedes=self._hv(atoms, [s]), h_loss=self._put_atom(atoms, V.atom_utf8("bob removed")),
                      slots=(pol, pol, V.H_LENS_KERNEL))
        tip = repo.ref_commit("minds")
        c = repo.build_candidate_commit("minds", atoms, [solo], [V.Seal.sign(ska, solo.id, s)], parent_commit=tip)
        repo.admit_and_advance("minds", c, expected_old=tip)
        self.assertEqual(mc.roster(repo), [pka])
        _, r2 = mc.release(self.repo_path, ska, "b" * 40, ["test_vars1 OK"])
        _, r3 = mc.release(self.repo_path, ska, "c" * 40, ["test_vars1 OK"])
        lens = repo.lens("minds")
        self.assertFalse(lens["settled"][r1["decision"]], "a release recorded under both still needs both")
        self.assertTrue(lens["settled"][r2["decision"]], "after the rotation Alice alone settles a release")

        b = json.loads(json.dumps(V.export_attestation(repo, "minds", r2["decision"], r3["projection"])))
        self.assertTrue(V.verify_attestation(b)["accepted"], "the chain describes itself consistently")
        pinned = V.verify_attestation(b, require=[pka, pkb])
        self.assertFalse(pinned["accepted"], "a reader who pinned Bob's key does not accept it")
        self.assertEqual(pinned["required_missing"], [pkb.hex()])
        self.assertTrue(V.verify_attestation(b, require=[pka])["accepted"])

        # Bob rejoins and witnesses a later projection without having attested r2: still missing for the pin
        mc.join(self.repo_path, ska, pkb, "bob")
        _, r4 = mc.release(self.repo_path, ska, "d" * 40, ["test_vars1 OK"])
        mc.verify_release(self.repo_path, skb, r4["decision"], "bob", checks=lambda *a: (["ok"], True))
        b4 = json.loads(json.dumps(V.export_attestation(repo, "minds", r2["decision"], r4["projection"])))
        self.assertIn(pkb.hex(), V.verify_projection(b4["projection"])["witnesses"])
        self.assertEqual(V.verify_attestation(b4, require=[pka, pkb])["required_missing"], [pkb.hex()])

        path = Path(self.tmp.name) / "attestation.json"
        path.write_text(json.dumps(b))
        cli = lambda cmd, *a: subprocess.run([sys.executable, str(ROOT_DIR / "vars1.py"), cmd, str(path), *a],
                                             capture_output=True, text=True).returncode
        self.assertEqual((cli("inspect-attestation"), cli("verify-attestation"),
                          cli("verify-attestation", "--require", pka.hex()),
                          cli("verify-attestation", "--require", pka.hex(), "--require", pkb.hex())), (0, 2, 0, 1))

    def test_23_a_member_revokes_its_own_attestation(self) -> None:
        """Monday F37: a member who attested a release and later finds a failure records INVALID under the same
        verifier id through `verify-release`, which contradicts its ATTESTED and unsettles the release."""
        mc = self._minds_chain()
        ska, skb = b"\x07" * 32, b"\x08" * 32
        mc.init(self.repo_path, ska)
        repo = V.GitVarsRepo(self.repo_path)
        mc.join(self.repo_path, ska, V.ed25519_pubkey(skb), "bob")
        _, r1 = mc.release(self.repo_path, ska, "a" * 40, ["test_vars1 OK"])
        ok_checks = lambda *a: (["test_vars1 OK"], True)
        bad_checks = lambda *a: (["test_vars1 FAILED"], False)
        mc.verify_release(self.repo_path, skb, r1["decision"], "bob", checks=ok_checks)
        self.assertTrue(repo.lens("minds")["settled"][r1["decision"]])
        with self.assertRaisesRegex(V.VarsError, "already recorded"):
            mc.verify_release(self.repo_path, skb, r1["decision"], "bob", checks=ok_checks)
        try:
            _, ok, _ = mc.verify_release(self.repo_path, skb, r1["decision"], "bob", checks=bad_checks)
        except V.VarsError as e:
            self.fail(f"the member could not revoke its own attestation: {e}")
        self.assertFalse(ok)
        self.assertFalse(repo.lens("minds")["settled"][r1["decision"]], "Bob's INVALID withdraws Bob's ATTESTED")
        with self.assertRaisesRegex(V.VarsError, "already recorded"):
            mc.verify_release(self.repo_path, skb, r1["decision"], "bob", checks=bad_checks)

    def test_24_releases_pin_the_sibling_checkouts(self) -> None:
        """Monday (F36 review, note): releases that pinned sigma-glyph and primitives commits are checked on those
        commits, extracted beside the worktree, not on whatever the sibling checkouts hold, and Book I is compared
        with the spec's pin. Releases since minds carries its dependencies pin nothing and see no siblings."""
        mc = self._minds_chain()
        proj = Path(self.tmp.name) / "proj"

        def repo(name):
            d = proj / name
            d.mkdir(parents=True)
            g = lambda *a: subprocess.run(["git", "-C", str(d), "-c", "user.name=t", "-c", "user.email=t@t", *a],
                                          capture_output=True, text=True, check=True).stdout.strip()
            g("init", "-q", "-b", "main")
            return d, g

        def commit(d, g, files, msg):
            for f, text in files.items():
                (d / f).parent.mkdir(parents=True, exist_ok=True)
                (d / f).write_text(text)
            g("add", "-A")
            g("commit", "-q", "-m", msg)
            return g("rev-parse", "HEAD")

        minds, gm = repo("minds")
        m1 = commit(minds, gm, {"f": "minds"}, "one")
        sg, gs = repo("sigma-glyph")
        pin = commit(sg, gs, {"impl/sigma_resume.py": "book one", "proofs/A.lean": "a", "README": "r1"}, "pin")
        s_same = commit(sg, gs, {"README": "r2"}, "docs only")
        s_new = commit(sg, gs, {"impl/sigma_resume.py": "book two"}, "book changed")
        pr, gp = repo("primitives")
        p1 = commit(pr, gp, {"v": "vectors one"}, "one")
        commit(pr, gp, {"v": "vectors two"}, "two")

        seen = {}
        def spy(root, rules):
            if not (root.parent / "sigma-glyph").exists():
                return ["spy OK"], True
            seen.update(book=(root.parent / "sigma-glyph" / "impl" / "sigma_resume.py").read_text(),
                        readme=(root.parent / "sigma-glyph" / "README").read_text(),
                        vectors=(root.parent / "primitives" / "v").read_text(),
                        linked=(root.parent / "sigma-glyph").is_symlink())
            return ["spy OK"], True
        real_checks, real_pin = mc.run_checks, mc.SIGMA_PIN
        mc.run_checks, mc.SIGMA_PIN = spy, pin
        try:
            lines, ok = mc.checks_at(minds, m1, V.H_LENS_KERNEL, {"sigma-glyph": s_same, "primitives": p1})
            self.assertTrue(ok, lines)
            self.assertEqual(seen, {"book": "book one", "readme": "r2", "vectors": "vectors one", "linked": False},
                             "the checks saw the pinned commits, not the checkouts")
            self.assertFalse((minds / ".git" / "vars" / "verify" / m1[:12] / "sigma-glyph").exists())
            lines, ok = mc.checks_at(minds, m1, V.H_LENS_KERNEL, {"sigma-glyph": s_new, "primitives": p1})
            self.assertFalse(ok)
            self.assertIn(f"sigma-glyph Book I equals the spec's pin {pin} FAILED", lines)
            self.assertEqual(mc.checks_at(minds, m1, V.H_LENS_KERNEL), (["spy OK"], True))
        finally:
            mc.run_checks, mc.SIGMA_PIN = real_checks, real_pin


        # The statement carries the pins, and verify-release hands them to the checks
        stmt = f"minds release main@{m1} rules@{V.H_LENS_KERNEL.hex()} sigma-glyph@{s_same} primitives@{p1}; checks: x"
        self.assertEqual(mc.parse_release(stmt), (m1, V.H_LENS_KERNEL, {"sigma-glyph": s_same, "primitives": p1}))
        self.assertEqual(mc.parse_release(f"minds release main@{m1} rules@{V.H_LENS_KERNEL.hex()}; checks: x"),
                         (m1, V.H_LENS_KERNEL, None))
        sk, skb = b"\x07" * 32, b"\x08" * 32
        mc.init(self.repo_path, sk)
        mc.join(self.repo_path, sk, V.ed25519_pubkey(skb), "bob")
        _, r = mc.release(self.repo_path, sk, m1, ["x OK"], {"sigma-glyph": s_same, "primitives": p1})
        got = []
        mc.verify_release(self.repo_path, skb, r["decision"], "bob",
                          checks=lambda *a, **kw: (got.append((a[1:], kw)), (["ok"], True))[1])
        self.assertEqual(got, [((m1, V.H_LENS_KERNEL), {"siblings": {"sigma-glyph": s_same, "primitives": p1}})])

    def test_25_readme_keys_are_the_chain_roster(self) -> None:
        """The member keys README.md publishes for pinning are the roster of this repository's own chain."""
        mc = self._minds_chain()
        repo = V.GitVarsRepo(ROOT_DIR)
        if repo.ref_commit(mc.SCOPE) is None:
            self.skipTest("refs/vars/heads/minds is not fetched in this clone")
        published = set(re.findall(r"\| `([0-9a-f]{64})` \|", (ROOT_DIR / "README.md").read_text()))
        self.assertEqual(published, {k.hex() for k in mc.roster(repo)})

    def test_26_concurrent_builders_get_their_own_cells(self) -> None:
        """Codex MND-01: two builders on one repository and scope, scheduled so that B stages between A's staging
        and A's write-tree; each candidate holds exactly its own cell (the schedule only orders real git calls)."""
        import threading
        old, scope, _ = self._bootstrap_genesis("core")
        staged_a, staged_b, read_a = threading.Event(), threading.Event(), threading.Event()
        original = V.subprocess.run

        def scheduled(cmd, *a, **kw):
            tag = threading.current_thread().name
            if tag == "A" and "write-tree" in cmd:
                staged_a.set()
                staged_b.wait(20)
                out = original(cmd, *a, **kw)
                read_a.set()
                return out
            if tag == "B" and "write-tree" in cmd:
                staged_b.set()
                read_a.wait(20)
            return original(cmd, *a, **kw)

        got, cells, errors = {}, {}, {}
        def worker(tag):
            try:
                build(tag)
            except Exception as e:  # noqa: BLE001 - reported below as a failed assertion
                errors[tag] = f"{type(e).__name__}: {e}"

        def build(tag):
            if tag == "B":
                staged_a.wait(20)
            atoms: dict[bytes, bytes] = {}
            cell = V.Cell(V.H_SCHEMA["axiom"], self._put_atom(atoms, V.atom_utf8("core/" + tag)),
                          self._put_atom(atoms, V.atom_utf8(tag)))
            cells[tag] = cell
            repo = V.GitVarsRepo(self.repo_path)
            c = repo.build_candidate_commit("core", atoms, [cell], [V.Seal.sign(self.sk1, cell.id, scope.id)],
                                            parent_commit=old)
            got[tag] = set(repo.read_cas_tree(c)[1])

        V.subprocess.run = scheduled
        try:
            ts = [threading.Thread(target=worker, args=(t,), name=t) for t in "AB"]
            for t in ts:
                t.start()
            for t in ts:
                t.join(60)
        finally:
            V.subprocess.run = original
        self.assertTrue(staged_b.is_set(), "the schedule interleaved the two builders")
        self.assertEqual(errors, {})
        for mine, other in (("A", "B"), ("B", "A")):
            self.assertIn(cells[mine].id, got[mine])
            self.assertNotIn(cells[other].id, got[mine])

    def test_27_a_historical_attestation_survives_a_rotation(self) -> None:
        """Codex MND-02: after `join`, exporting an older release with the projection that covers it bundles the
        scope that governed that projection's tip, so the bundle still verifies."""
        mc = self._minds_chain()
        sk = b"\x07" * 32
        mc.init(self.repo_path, sk)
        repo = V.GitVarsRepo(self.repo_path)
        _, r1 = mc.release(self.repo_path, sk, "a" * 40, ["x OK"])
        _, r2 = mc.release(self.repo_path, sk, "b" * 40, ["x OK"])
        before = V.export_attestation(repo, "minds", r1["decision"], r2["projection"])
        mc.join(self.repo_path, sk, V.ed25519_pubkey(b"\x08" * 32), "bob")
        after = json.loads(json.dumps(V.export_attestation(repo, "minds", r1["decision"], r2["projection"])))
        self.assertEqual(after["scope"], before["scope"], "the scope of the projection's tip, not of the head")
        self.assertTrue(V.verify_attestation(after)["accepted"])

    def test_28_a_later_invalid_withdraws_only_its_own_verifier(self) -> None:
        """Codex MND-03: an INVALID recorded after the projection's tip withdraws the ATTESTED verdicts of its own
        verifier, as at the tip and in the lens; another verifier's INVALID does not."""
        mc = self._minds_chain()
        sk = b"\x07" * 32
        mc.init(self.repo_path, sk)
        repo = V.GitVarsRepo(self.repo_path)
        _, r1 = mc.release(self.repo_path, sk, "a" * 40, ["x OK"])
        _, r2 = mc.release(self.repo_path, sk, "b" * 40, ["x OK"])
        d1 = r1["decision"]

        def invalid(verifier, name):
            atoms: dict[bytes, bytes] = {}
            w = V.Cell(V.H_SCHEMA["verdict"], self._put_atom(atoms, V.atom_utf8(name)), d1,
                       h_attests=self._hv(atoms, [d1]),
                       slots=(V.H_EMPTY, V.H_VERDICT_INVALID, self._put_atom(atoms, V.atom_utf8(verifier))))
            tip = repo.ref_commit("minds")
            c = repo.build_candidate_commit("minds", atoms, [w], [V.Seal.sign(sk, w.id, mc.governing_scope(repo))],
                                            parent_commit=tip)
            repo.admit_and_advance("minds", c, expected_old=tip)

        verify = lambda: V.verify_attestation(json.loads(json.dumps(
            V.export_attestation(repo, "minds", d1, r2["projection"]))))
        invalid("different-verifier", "minds/other-verifier")
        self.assertTrue(repo.lens("minds")["settled"][d1])
        r = verify()
        self.assertEqual((r["contradicted_after_tip"], r["accepted"]), (False, True))
        invalid("minds-maintainer", "minds/maintainer-withdraws")
        self.assertFalse(repo.lens("minds")["settled"][d1])
        r = verify()
        self.assertEqual((r["attested_at_tip"], r["contradicted_after_tip"], r["accepted"]), (True, True, False))

    def test_29_gate_enforces_payloads_and_enumerations(self) -> None:
        """Codex MND-04: each malformed cell is refused, and its well-formed neighbour admitted."""
        def attempt(build):
            T = TestVars1Conformance()
            T.setUp()
            try:
                c0, s0, _ = T._bootstrap_genesis("core")
                a: dict[bytes, bytes] = {}
                put = lambda raw: T._put_atom(a, raw)
                ax = V.Cell(V.H_SCHEMA["axiom"], put(V.atom_utf8("core/ax")), put(V.atom_utf8("axiom")))
                d = V.Cell(V.H_SCHEMA["decision"], put(V.atom_utf8("core/decision")), put(V.atom_utf8("statement")),
                           slots=(V.H_OWNER, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY))
                cells = build(put, ax, d, c0, s0, T)
                c = T.repo.build_candidate_commit("core", a, cells, [V.Seal.sign(T.sk1, x.id, s0.id) for x in cells],
                                                  parent_commit=c0)
                T.repo.admit_and_advance("core", c, expected_old=c0)
                return None
            except V.VarsError as e:
                return str(e)
            finally:
                T.tearDown()

        def verdict(put, d, code, ck=V.H_EMPTY, **kw):
            return V.Cell(V.H_SCHEMA["verdict"], put(V.atom_utf8("core/verdict")), d.id,
                          h_attests=put(V.atom_hvec([d.id])), slots=(ck, code, put(V.atom_utf8("verifier"))), **kw)

        def schema_cell(put, desc):
            sc = V.Cell(V.H_META_SCHEMA, put(V.atom_utf8("core/custom-schema")), V.H_EMPTY,
                        slots=(put(V.atom_utf8(desc)),))
            return [sc, V.Cell(sc.id, put(V.atom_utf8("core/custom")), put(V.atom_utf8("x")), slots=(V.H_ZERO,))]

        def projection(put, c0, s0, T, payload):
            hi, ho = T.repo.projection_digests("core", c0)
            return V.Cell(V.H_SCHEMA["projection"], put(V.atom_utf8("core/projection")), payload,
                          slots=(put(V.atom_utf8(c0)), V.H_LENS_KERNEL, hi, ho, s0.slots[0]))

        cases = {
            "statement payload": (
                lambda put, ax, d, *_: [ax, dataclasses.replace(d, h_payload=V.H_ZERO)],
                lambda put, ax, d, *_: [ax, d]),
            "computation payload": (
                lambda put, ax, d, *_: [ax, V.Cell(V.H_SCHEMA["computation"], put(V.atom_utf8("core/comp")), V.H_ZERO)],
                None),
            "tier": (
                lambda put, ax, d, *_: [ax, dataclasses.replace(d, slots=(put(V.atom_utf8("owenr")), *d.slots[1:]))],
                lambda put, ax, d, *_: [ax, dataclasses.replace(d, slots=(V.H_PROVISIONAL, *d.slots[1:]))]),
            "loss": (
                lambda put, ax, d, *_: [ax, d, V.Cell(V.H_SCHEMA["axiom"], put(V.atom_utf8("core/retire")),
                                                      put(V.atom_utf8("retire")), h_retires=put(V.atom_hvec([ax.id])),
                                                      h_loss=put(V.atom_u64(123)))],
                lambda put, ax, d, *_: [ax, d, V.Cell(V.H_SCHEMA["axiom"], put(V.atom_utf8("core/retire")),
                                                      put(V.atom_utf8("retire")), h_retires=put(V.atom_hvec([ax.id])),
                                                      h_loss=put(V.atom_utf8("retired on purpose")))]),
            "field type": (
                lambda put, ax, d, *_: [ax, d, *schema_cell(put, "field:totally-unknown")],
                lambda put, ax, d, *_: [ax, d, *schema_cell(put, "field:u64")]),
            "field type, schema alone": (
                lambda put, ax, d, *_: [ax, d, schema_cell(put, "field:totally-unknown")[0]],
                lambda put, ax, d, *_: [ax, d, schema_cell(put, "field:u64")[0]]),
            "field descriptor shape": (
                lambda put, ax, d, *_: [ax, d, schema_cell(put, "no-type-here")[0]],
                None),
            "verdict code": (
                lambda put, ax, d, *_: [ax, d, verdict(put, d, put(V.atom_utf8("UNKNOWN")))],
                lambda put, ax, d, *_: [ax, d, verdict(put, d, V.H_VERDICT_INVALID)]),
            "attested with a witness": (
                lambda put, ax, d, *_: [ax, d, verdict(put, d, V.H_ATTESTED, ax.id, h_relies=put(V.atom_hvec([ax.id])))],
                lambda put, ax, d, *_: [ax, d, verdict(put, d, V.H_ATTESTED)]),
            "projection payload": (
                lambda put, ax, d, c0, s0, T: [ax, d, projection(put, c0, s0, T, V.H_ZERO)],
                lambda put, ax, d, c0, s0, T: [ax, d, projection(put, c0, s0, T, V.H_EMPTY)]),
        }
        for name, (bad, good) in cases.items():
            with self.subTest(name):
                self.assertIsNotNone(attempt(bad), f"{name}: the malformed cell was admitted")
                if good is not None:
                    self.assertIsNone(attempt(good), f"{name}: the well-formed neighbour was refused")

    def test_30_checkpoint_actions_are_replayed(self) -> None:
        """Codex MND-05: a checkpoint's `actions` must equal the replayed transition's action count."""
        def admit(actions):
            T = TestVars1Conformance()
            T.setUp()
            try:
                c0, s0, _ = T._bootstrap_genesis("core")
                a: dict[bytes, bytes] = {}
                put = lambda raw: T._put_atom(a, raw)
                raw = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=V.H_I, right=V.H_K)
                h = put(raw)
                env = SR.Environment([h], {h: raw})
                cid = bytes.fromhex(SR.root(h, env)[1])
                self.assertEqual(put(V.atom_computation_root(h, put(V.atom_environment([h])))), cid)
                doc, i, state = SR.start(cid.hex(), h)
                nf = SR.advance(doc, i, state, env, 10)
                comp = V.Cell(V.H_SCHEMA["computation"], put(V.atom_utf8("core/comp")), cid)
                ck = V.Cell(V.H_SCHEMA["checkpoint"], put(V.atom_utf8("core/ck")), put(nf.state_bytes),
                            h_relies=put(V.atom_hvec([comp.id])),
                            slots=(cid, put(V.atom_u64(10)), put(V.atom_u64(nf.checkpoint["spent_total"])),
                                   put(V.atom_u64(nf.checkpoint["peak_semantic_size"])), V.H_NORMAL_FORM,
                                   put(V.atom_u64(actions(nf.checkpoint["transition_claim"]["actions"])))))
                c = T.repo.build_candidate_commit("core", a, [comp, ck], [V.Seal.sign(T.sk1, x.id, s0.id)
                                                                          for x in (comp, ck)], parent_commit=c0)
                T.repo.admit_and_advance("core", c, expected_old=c0)
                return None
            except V.VarsError as e:
                return str(e)
            finally:
                T.tearDown()
        self.assertIsNone(admit(lambda n: n))
        self.assertIn("actions", admit(lambda n: n + 997) or "")
        self.assertIn("actions", admit(lambda n: 0) or "")

    def test_31_a_question_is_answered_by_any_cell_of_its_schema(self) -> None:
        """Codex MND-06: the INVALID-verdict exclusion is for contract and decision witnesses; a question whose
        expected schema is verdict is answered (Settled) by an INVALID verdict, as the spec now says."""
        old, scope, _ = self._bootstrap_genesis("core")
        a: dict[bytes, bytes] = {}
        put = lambda raw: self._put_atom(a, raw)
        q = V.Cell(V.H_SCHEMA["question"], put(V.atom_utf8("core/q")), put(V.atom_utf8("Need a verdict")),
                   slots=(V.H_SCHEMA["verdict"], V.H_EMPTY))
        w = V.Cell(V.H_SCHEMA["verdict"], put(V.atom_utf8("core/no")), q.id, h_attests=put(V.atom_hvec([q.id])),
                   slots=(V.H_EMPTY, V.H_VERDICT_INVALID, put(V.atom_utf8("verifier"))))
        c = self.repo.build_candidate_commit("core", a, [q, w], [V.Seal.sign(self.sk1, x.id, scope.id) for x in (q, w)],
                                             parent_commit=old)
        self.repo.admit_and_advance("core", c, expected_old=old)
        self.assertTrue(self.repo.lens("core")["settled"][q.id])

    def _try_admit(self, build):
        """Admit `build(put, ax, d, c0, s0, T)` on a fresh `core` chain; None if admitted, else the refusal."""
        T = TestVars1Conformance()
        T.setUp()
        try:
            c0, s0, _ = T._bootstrap_genesis("core")
            a: dict[bytes, bytes] = {}
            put = lambda raw: T._put_atom(a, raw)
            ax = V.Cell(V.H_SCHEMA["axiom"], put(V.atom_utf8("core/ax")), put(V.atom_utf8("axiom")))
            d = V.Cell(V.H_SCHEMA["decision"], put(V.atom_utf8("core/d")), put(V.atom_utf8("decision")),
                       slots=(V.H_OWNER, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY))
            cells = build(put, ax, d, c0, s0, T)
            c = T.repo.build_candidate_commit("core", a, cells, [V.Seal.sign(T.sk1, x.id, s0.id) for x in cells],
                                              parent_commit=c0)
            T.repo.admit_and_advance("core", c, expected_old=c0)
            return None
        except V.VarsError as e:
            return str(e)
        finally:
            T.tearDown()

    def test_32_gate_validates_whole_objects(self) -> None:
        """Codex R2-01: roots, environments, nodes and states are validated whole, verdicts by the kinds they name,
        and a scope's payload is a UTF8 label; each case has its well-formed neighbour."""
        canon = lambda doc: json.dumps(doc, sort_keys=True, separators=(",", ":")).encode()
        node = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=V.H_I, right=V.H_K)

        def comp(put, root_doc=None, env_doc=None):
            env = put(canon(env_doc) if env_doc is not None else V.atom_environment([]))
            rd = json.loads(V.atom_computation_root(V.H_I, env)) if root_doc is None else dict(root_doc, environment_id=env.hex())
            return V.Cell(V.H_SCHEMA["computation"], put(V.atom_utf8("core/comp")), put(canon(rd)))

        def verdict(put, target, code, ck=V.H_EMPTY, **kw):
            return V.Cell(V.H_SCHEMA["verdict"], put(V.atom_utf8("core/verdict")), target.id,
                          slots=(ck, code, put(V.atom_utf8("verifier"))), **kw)

        def scope(put, s0, payload):
            return V.Cell(V.H_SCHEMA["scope"], put(V.atom_utf8("core/SCOPE")), payload,
                          h_supersedes=put(V.atom_hvec([s0.id])), h_loss=put(V.atom_utf8("rotate")), slots=s0.slots)

        def atom_only(raw):
            return lambda put, ax, d, *_: (put(raw), [ax])[1]

        cases = {
            "incomplete root": (
                lambda put, ax, d, *_: [ax, comp(put, root_doc={"schema": "sigma-resume.root@draft-1"})],
                lambda put, ax, d, *_: [ax, comp(put)]),
            "incomplete environment": (
                lambda put, ax, d, *_: [ax, comp(put, env_doc={"schema": "sigma-resume.environment@draft-1"})],
                lambda put, ax, d, *_: [ax, comp(put, env_doc={"schema": "sigma-resume.environment@draft-1",
                                                               "hashes": []})]),
            "REPLAYED naming an axiom": (
                lambda put, ax, d, *_: [ax, d, verdict(put, d, V.H_REPLAYED, ax.id, h_relies=put(V.atom_hvec([ax.id])),
                                                       h_attests=put(V.atom_hvec([d.id])))],
                None),
            "ATTESTED judging an axiom": (
                lambda put, ax, d, *_: [ax, verdict(put, ax, V.H_ATTESTED)],
                lambda put, ax, d, *_: [ax, verdict(put, ax, V.H_VERDICT_INVALID)]),
            "scope label not UTF8": (
                lambda put, ax, d, c0, s0, T: [scope(put, s0, put(V.atom_u64(55)))],
                lambda put, ax, d, c0, s0, T: [scope(put, s0, put(V.atom_utf8("rotated")))]),
            "node atom": (atom_only(b"\x00\x00" + b"x" * 32), atom_only(node)),
            "state atom": (atom_only(b"SGS1" + b"x" * 32 + b"X" + b"x" * 32),
                           atom_only(SR.start(V.sha256(b"c").hex(), V.sha256(node))[2])),
        }
        for name, (bad, good) in cases.items():
            with self.subTest(name):
                self.assertIsNotNone(self._try_admit(bad), f"{name}: the malformed object was admitted")
                if good is not None:
                    self.assertIsNone(self._try_admit(good), f"{name}: the well-formed neighbour was refused")

    def test_33_intrinsic_atoms_need_not_be_stored(self) -> None:
        """Codex R2-02: the same checkpoint, its u64 slots naming intrinsic H_ZERO, is admitted whether or not the
        zero atom is stored."""
        def build(store):
            def b(put, ax, d, c0, s0, T):
                raw = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=V.H_I, right=V.H_K)
                h = put(raw)
                env = SR.Environment([h], {h: raw})
                root = put(V.atom_computation_root(h, put(V.atom_environment([h]))))
                doc, i, state = SR.start(root.hex(), h)
                honest = SR.advance(doc, i, state, env, 0)
                if store:
                    put(V.atom_u64(0))
                comp = V.Cell(V.H_SCHEMA["computation"], put(V.atom_utf8("core/comp")), root)
                ck = V.Cell(V.H_SCHEMA["checkpoint"], put(V.atom_utf8("core/ck")), put(state),
                            h_relies=put(V.atom_hvec([comp.id])),
                            slots=(root, V.H_ZERO, V.H_ZERO, put(V.atom_u64(honest.checkpoint["peak_semantic_size"])),
                                   V.H_PAUSED, V.H_ZERO))
                ids.append(ck.id)
                return [comp, ck]
            return b
        ids: list = []
        self.assertEqual(V.sha256(V.atom_u64(0)), V.H_ZERO)
        self.assertIsNone(self._try_admit(build(False)), "intrinsic H_ZERO without its bytes stored")
        self.assertIsNone(self._try_admit(build(True)), "intrinsic H_ZERO with its bytes stored")
        self.assertEqual(ids[0], ids[1])

    def test_34_no_reference_to_a_later_born_cell(self) -> None:
        """Codex R2-03: an opaque digest equal to a future cell's id does not become a backward-in-time reference;
        that cell is refused, and any other cell is admitted."""
        old, scope, _ = self._bootstrap_genesis("core")
        a: dict[bytes, bytes] = {}
        put = lambda raw: self._put_atom(a, raw)
        fa: dict[bytes, bytes] = {}
        future = V.Cell(V.H_SCHEMA["axiom"], self._put_atom(fa, V.atom_utf8("core/planned")),
                        self._put_atom(fa, V.atom_utf8("planned work")))
        schema = V.Cell(V.H_META_SCHEMA, put(V.atom_utf8("core/opaque-schema")), V.H_EMPTY,
                        slots=(put(V.atom_utf8("value:digest")),))
        holder = V.Cell(schema.id, put(V.atom_utf8("core/opaque")), put(V.atom_utf8("checksum")), slots=(future.id,))
        c1 = self.repo.build_candidate_commit("core", a, [schema, holder],
                                              [V.Seal.sign(self.sk1, x.id, scope.id) for x in (schema, holder)],
                                              parent_commit=old)
        self.repo.admit_and_advance("core", c1, expected_old=old)
        c2 = self.repo.build_candidate_commit("core", fa, [future], [V.Seal.sign(self.sk1, future.id, scope.id)],
                                              parent_commit=c1)
        with self.assertRaisesRegex(V.VarsError, "later-born cell"):
            self.repo.admit_and_advance("core", c2, expected_old=c1)
        other = dataclasses.replace(future, h_payload=self._put_atom(fa, V.atom_utf8("other work")))
        c3 = self.repo.build_candidate_commit("core", fa, [other], [V.Seal.sign(self.sk1, other.id, scope.id)],
                                              parent_commit=c1)
        self.repo.admit_and_advance("core", c3, expected_old=c1)

    def test_35_parents_come_from_the_commit_header(self) -> None:
        """Codex R2-04: a `parent` line in the message is not a parent; a real second parent is still refused."""
        old, _, _ = self._bootstrap_genesis("core")
        tree = self.repo._git("rev-parse", old + "^{tree}").decode().strip()
        msg = self.repo._git("commit-tree", tree, "-p", old, "-m", "ordinary\n\nparent " + "f" * 40).decode().strip()
        try:
            self.repo.admit_and_advance("core", msg, expected_old=old)
        except V.VarsError as e:
            self.fail(f"a one-parent commit was refused for its message: {e}")
        tip = self.repo.ref_commit("core")
        merge = self.repo._git("commit-tree", tree, "-p", tip, "-p", old, "-m", "merge").decode().strip()
        with self.assertRaisesRegex(V.VarsError, "single parent"):
            self.repo.admit_and_advance("core", merge, expected_old=tip)

    def test_36_offline_verifier_in_a_fresh_folder(self) -> None:
        """Codex direction 2: verify/minds_verify.py alone, copied into a folder with no .git and no siblings and run
        with `python3 -I -S`, verifies real exported bundles and explains acceptance and refusal: counted witnesses
        and keys, blocked verifiers at and after the tip, the scope epoch, the policy, why a pinned key is missing,
        and an unsupported rules identity."""
        mc = self._minds_chain()
        ska, skb = b"\x07" * 32, b"\x08" * 32
        pka, pkb = V.ed25519_pubkey(ska), V.ed25519_pubkey(skb)
        mc.init(self.repo_path, ska)
        repo = V.GitVarsRepo(self.repo_path)
        _, r1 = mc.release(self.repo_path, ska, "a" * 40, ["x OK"])
        _, r2 = mc.release(self.repo_path, ska, "b" * 40, ["x OK"])
        scope1 = mc.governing_scope(repo)

        fresh_tmp = tempfile.TemporaryDirectory()
        self.addCleanup(fresh_tmp.cleanup)
        fresh = Path(fresh_tmp.name) / "client"
        fresh.mkdir()
        (fresh / "minds_verify.py").write_bytes((ROOT_DIR / "verify" / "minds_verify.py").read_bytes())
        self.assertEqual(sorted(p.name for p in fresh.iterdir()), ["minds_verify.py"])
        self.assertFalse(any((d / ".git").exists() for d in (fresh, *fresh.parents)), "no repository around it")
        self.assertFalse((fresh.parent / "sigma-glyph").exists() or (fresh.parent / "primitives").exists())
        env = {"PATH": "/usr/bin:/bin"}
        loaded = subprocess.run([sys.executable, "-I", "-S", "-c",
                                 "import sys; sys.path.insert(0, '.'); import minds_verify; "
                                 "print(sorted(m for m in sys.modules if m != '__main__' and m.split('.')[0] not in sys.stdlib_module_names))"],
                                cwd=fresh, env=env, capture_output=True, text=True)
        self.assertEqual(loaded.stdout.strip(), "['minds_verify']", loaded.stderr)

        def offline(cmd, bundle, *args):
            (fresh / "bundle.json").write_text(json.dumps(bundle))
            out = subprocess.run([sys.executable, "-I", "-S", "minds_verify.py", cmd, "bundle.json", *args],
                                 cwd=fresh, env=env, capture_output=True, text=True)
            (fresh / "bundle.json").unlink()
            return out.returncode, (json.loads(out.stdout) if out.returncode in (0, 1) else out.stderr)

        # A real bundle verifies offline, and the trace names what was counted
        b1 = json.loads(json.dumps(V.export_attestation(repo, "minds", r1["decision"], r2["projection"])))
        code, r = offline("inspect-attestation", b1)
        self.assertEqual((code, r["accepted"], r["rules_status"]), (0, True, "known"))
        ex = r["explain"]
        self.assertEqual(ex["at_tip"]["counted"], [{"verdict": r1["verdict"].hex(), "verifier": "minds-maintainer",
                                                    "endorsers": [pka.hex()]}])
        self.assertEqual(ex["supplied"]["counted"], ex["at_tip"]["counted"])
        self.assertEqual((ex["at_tip"]["blocked_verifiers"], ex["after_tip"]["blocked_verifiers"]), ([], []))
        self.assertEqual(ex["scope_epoch"], scope1.hex())
        self.assertEqual((ex["policy"]["source"], ex["policy"]["threshold"], ex["policy"]["keys"]),
                         ("evaluator_policy", 1, [pka.hex()]))
        self.assertEqual(ex["rules"]["status"], "known")
        self.assertEqual(r, V.verify_attestation(b1), "vars1.py and the standalone file are one implementation")
        code, p = offline("inspect-projection", b1["projection"])
        self.assertEqual((code, p["explain"]["scope_epoch"], p["explain"]["witnesses_missing"]), (0, scope1.hex(), []))
        self.assertEqual([(s["key"], s["counted"]) for s in p["explain"]["witness_seals"]], [(pka.hex(), True)])
        pcell = V.Cell.decode(bytes.fromhex(b1["projection"]["cell"]))
        ctx = V.Seal.decode(bytes.fromhex(b1["projection"]["seals"][0])).h_scope_ctx
        stranger = V.ed25519_pubkey(b"\x09" * 32)
        alien = V.Seal.sign(b"\x09" * 32, pcell.id, ctx).encode().hex()
        code, p = offline("inspect-projection", dict(b1["projection"], seals=[alien]))
        self.assertEqual((code, p["witnessed"], p["explain"]["witnesses_missing"]), (1, False, [pka.hex()]))
        self.assertEqual([(s["key"], s["counted"]) for s in p["explain"]["witness_seals"]], [(stranger.hex(), False)])

        # Mutated output bytes: refused
        out = b1["projection"]["output"]
        flipped = dict(b1, projection=dict(b1["projection"], output=out[:-2] + ("00" if out[-2:] != "00" else "01")))
        code, err = offline("inspect-attestation", flipped)
        self.assertEqual(code, 2)
        self.assertIn("state digest", err)

        # An unknown rules identity: witnessed and digest-consistent, yet never read as known
        other = dataclasses.replace(pcell, slots=(pcell.slots[0], V.sha256(b"other rules"), *pcell.slots[2:]))
        foreign = dict(b1["projection"], cell=other.encode().hex(), seals=[V.Seal.sign(ska, other.id, ctx).encode().hex()])
        code, p = offline("inspect-projection", foreign)
        self.assertEqual((code, p["witnessed"], p["data_ok"], p["rules_status"], p["statuses"], p["scope"]),
                         (1, True, True, "unsupported", None, None))
        self.assertIn("only H_LENS_KERNEL", p["explain"]["rules"]["reason"])
        code, r = offline("inspect-attestation", dict(b1, projection=foreign))
        self.assertEqual(code, 1, r)
        self.assertEqual((code, r["rules_status"], r["evidence"], r["attested_at_tip"], r["accepted"]),
                         (1, "unsupported", "supplied", None, False))

        # A second member joins: the scope rotates; the earlier bundle keeps the epoch of its projection's tip
        mc.join(self.repo_path, ska, pkb, "bob")
        scope2 = mc.governing_scope(repo)
        self.assertNotEqual(scope1, scope2)
        _, r3 = mc.release(self.repo_path, ska, "c" * 40, ["x OK"])
        mc.verify_release(self.repo_path, skb, r3["decision"], "bob", checks=lambda *a, **kw: (["x OK"], True))
        _, r4 = mc.release(self.repo_path, ska, "d" * 40, ["x OK"])
        mc.verify_release(self.repo_path, skb, r4["decision"], "bob", checks=lambda *a, **kw: (["x OK"], True))
        b1 = json.loads(json.dumps(V.export_attestation(repo, "minds", r1["decision"], r2["projection"])))
        code, r = offline("inspect-attestation", b1)
        self.assertEqual((code, r["explain"]["scope_epoch"]), (0, scope1.hex()))
        b3 = json.loads(json.dumps(V.export_attestation(repo, "minds", r3["decision"], r4["projection"])))
        code, r = offline("verify-attestation", b3, "--require", pka.hex(), "--require", pkb.hex())
        self.assertEqual((code, r["accepted"], r["explain"]["scope_epoch"]), (0, True, scope2.hex()))
        self.assertEqual(sorted((c["verifier"], c["endorsers"]) for c in r["explain"]["at_tip"]["counted"]),
                         [("bob", [pkb.hex()]), ("minds-maintainer", [pka.hex()])])
        self.assertEqual({c["verdict"] for c in r["explain"]["at_tip"]["counted"]},
                         {c.id.hex() for c in map(lambda h: V.Cell.decode(bytes.fromhex(h)), b3["verdicts"])})
        self.assertEqual((r["explain"]["policy"]["threshold"], r["explain"]["required"]),
                         (2, [{"key": pka.hex(), "reasons": []}, {"key": pkb.hex(), "reasons": []}]))
        # Substituting the rotated scope (with its atoms) into the earlier bundle: refused
        rotated = dict(b1, scope=b3["scope"], atoms=sorted(set(b1["atoms"]) | set(b3["atoms"])))
        code, err = offline("inspect-attestation", rotated)
        self.assertEqual(code, 2)
        self.assertIn("does not govern", err)

        # Bob withdraws after p4's tip: one of two witnesses gone, and a reader pinning Bob is told why
        mc.verify_release(self.repo_path, skb, r3["decision"], "bob", checks=lambda *a, **kw: (["x FAILED"], False))
        b3 = json.loads(json.dumps(V.export_attestation(repo, "minds", r3["decision"], r4["projection"])))
        code, r = offline("verify-attestation", b3, "--require", pka.hex(), "--require", pkb.hex(),
                          "--require", stranger.hex())
        self.assertEqual((code, r["attested_at_tip"], r["contradicted_after_tip"], r["accepted"]), (1, True, True, False))
        ex = r["explain"]
        self.assertEqual((ex["at_tip"]["blocked_verifiers"], ex["after_tip"]["blocked_verifiers"]), ([], ["bob"]))
        self.assertEqual(ex["after_tip"]["withdrawn_endorsers"], [pkb.hex()])
        self.assertEqual([c["verifier"] for c in ex["after_tip"]["counted"]], ["minds-maintainer"])
        self.assertEqual(r["required_missing"], [pkb.hex(), stranger.hex()])
        self.assertEqual(ex["required"], [
            {"key": pka.hex(), "reasons": []},
            {"key": pkb.hex(), "reasons": ["its endorsement is withdrawn by an INVALID verdict after the tip"]},
            {"key": stranger.hex(), "reasons": ["does not endorse the cell at the projection's tip",
                                                "did not witness the projection"]},
        ])

        # Once a projection's tip holds Bob's INVALID it blocks there, and leaving it out is a refusal
        _, r5 = mc.release(self.repo_path, ska, "e" * 40, ["x OK"])
        mc.verify_release(self.repo_path, skb, r5["decision"], "bob", checks=lambda *a, **kw: (["x OK"], True))
        b5 = json.loads(json.dumps(V.export_attestation(repo, "minds", r3["decision"], r5["projection"])))
        code, r = offline("inspect-attestation", b5)
        self.assertEqual((code, r["attested_at_tip"], r["explain"]["at_tip"]["blocked_verifiers"]), (1, False, ["bob"]))
        self.assertEqual((r["explain"]["supplied"]["blocked_verifiers"],
                          [c["verifier"] for c in r["explain"]["at_tip"]["counted"]]), (["bob"], ["minds-maintainer"]))
        invalid = [v for v in b5["verdicts"] if V.Cell.decode(bytes.fromhex(v)).slots[1] == V.H_VERDICT_INVALID]
        self.assertEqual(len(invalid), 1)
        bad_id = V.Cell.decode(bytes.fromhex(invalid[0])).id
        hidden = dict(b5, verdicts=[v for v in b5["verdicts"] if v not in invalid],
                      seals=[x for x in b5["seals"] if V.Seal.decode(bytes.fromhex(x)).h_target != bad_id])
        code, err = offline("inspect-attestation", hidden)
        self.assertEqual(code, 2)
        self.assertIn("omits 1 verdict", err)

    def test_37_dependencies_are_pinned_by_content(self) -> None:
        """minds carries its dependencies: Book I from PyPI, checked by the modules' bytes at import (a modified
        sigma_resume first on the path is refused); the vendored Lean sources and vectors match their SOURCE."""
        for d in ("proofs/SigmaEval", "vectors"):
            listed = {}
            for line in (ROOT_DIR / d / "SOURCE").read_text().splitlines():
                parts = line.split()
                if len(parts) == 2 and len(parts[0]) == 64:
                    listed[parts[1]] = parts[0]
            self.assertTrue(listed, d)
            on_disk = {f.name for f in (ROOT_DIR / d).iterdir() if f.name != "SOURCE"}
            self.assertEqual(set(listed), on_disk, f"{d}: SOURCE lists exactly the files present")
            for name, digest in listed.items():
                self.assertEqual(V.sha256((ROOT_DIR / d / name).read_bytes()).hex(), digest, f"{d}/{name}")

        fake = Path(self.tmp.name) / "fake"
        fake.mkdir()
        (fake / "sigma_resume.py").write_bytes(Path(SR.__file__).read_bytes() + b"\n# modified\n")
        out = subprocess.run([sys.executable, "-c", "import vars1"], cwd=ROOT_DIR, capture_output=True, text=True,
                             env={**os.environ, "PYTHONPATH": str(fake)})
        self.assertNotEqual(out.returncode, 0)
        self.assertIn("is not Book I", out.stderr)
        ok = subprocess.run([sys.executable, "-c", "import vars1"], cwd=ROOT_DIR, capture_output=True, text=True)
        self.assertEqual(ok.returncode, 0, ok.stderr)

    def _raw_commit(self, parent: str, entries: list[tuple[str, str]]) -> str:
        """A commit adding `(path, blob oid)` entries to `parent`'s tree, objects not checked (write-tree --missing-ok)."""
        env = {**os.environ, "GIT_INDEX_FILE": str(Path(self.tmp.name) / "raw-index")}
        git = lambda *a, inp=None: subprocess.run(["git", "-C", str(self.repo_path), *a], input=inp, env=env,
                                                  capture_output=True, check=True).stdout.decode().strip()
        git("read-tree", parent)
        git("update-index", "--add", "--index-info",
            inp="".join(f"100644 {oid}\t{path}\n" for path, oid in entries).encode())
        return git("commit-tree", git("write-tree", "--missing-ok"), "-p", parent, "-m", "raw")

    def _blob(self, raw: bytes) -> str:
        return subprocess.run(["git", "-C", str(self.repo_path), "hash-object", "-w", "--stdin"], input=raw,
                              capture_output=True, check=True).stdout.decode().strip()

    def test_38_caches_never_stand_in_for_new_bytes(self) -> None:
        """The host reads each commit once (its diff-tree delta) and keeps checked objects by content hash. New bytes
        are always read, hashed against their path and checked: a forged seal, bytes that do not hash to an
        already-checked object's name, and a missing object are refused by an instance whose caches hold the history;
        a missing object of an admitted commit is refused by a fresh instance. Caches change no result."""
        c0, s0, _ = self._bootstrap_genesis("core")
        repo = self.repo
        atoms: dict[bytes, bytes] = {}
        ax1 = self._axiom(atoms, "core/ax.1", "first")
        c1 = self._admit(atoms, [ax1], [V.Seal.sign(self.sk1, ax1.id, s0.id)], c0)

        # A forged seal: the same target, context and key as a valid one, one signature bit flipped
        atoms2: dict[bytes, bytes] = {}
        ax2 = self._axiom(atoms2, "core/ax.2", "second")
        good = V.Seal.sign(self.sk1, ax2.id, s0.id)
        forged = dataclasses.replace(good, signature=bytes([good.signature[0] ^ 1]) + good.signature[1:])
        cand = repo.build_candidate_commit("core", atoms2, [ax2], [forged], parent_commit=c1)
        with self.assertRaisesRegex(V.VarsError, "invalid or weak-key Ed25519 signature on SEAL"):
            repo.admit_and_advance("core", cand, expected_old=c1)

        # Bytes under the name of an object this instance has already checked (from a refused, unsealed candidate)
        cand = repo.build_candidate_commit("core", atoms2, [ax2], [], parent_commit=c1)
        with self.assertRaisesRegex(V.VarsError, "lacks a valid Seal"):
            repo.admit_and_advance("core", cand, expected_old=c1)
        self.assertIn(("cells", ax2.id), repo._checked)
        enc = ax2.encode()
        # (and, for a seal not yet checked, bytes that do not hash to its name)
        for kind, h, raw in (("cells", ax2.id, enc[:-1] + bytes([enc[-1] ^ 1])),
                             ("seals", good.id, good.encode()[:-1] + b"\x00")):
            path = f"cas/{kind}/{h.hex()[:2]}/{h.hex()[2:]}"
            cand = self._raw_commit(c1, [(path, self._blob(raw))])
            with self.assertRaisesRegex(V.VarsError, "CAS SHA-256 mismatch"):
                repo.admit_and_advance("core", cand, expected_old=c1)

        # A tree entry whose object is not in the store
        h = V.sha256(V.atom_utf8("never stored"))
        cand = self._raw_commit(c1, [(f"cas/atoms/{h.hex()[:2]}/{h.hex()[2:]}", "ab" * (len(c1) // 2))])
        with self.assertRaisesRegex(V.VarsError, "missing"):
            repo.admit_and_advance("core", cand, expected_old=c1)

        # After the refusals the valid commit is admitted, and a fresh instance computes the same fold and lens
        c2 = self._admit(atoms2, [ax2], [good], c1)
        warm = repo.lens("core")
        cold = V.GitVarsRepo(self.repo_path).lens("core")
        for name in ("active", "stale", "settled", "provisional"):
            self.assertEqual(warm[name], cold[name], name)
        self.assertEqual(warm["kernel_input"], cold["kernel_input"])
        self.assertTrue(cold["active"][ax2.id])

        # An admitted commit's object goes missing: a fresh instance (nothing cached) refuses the chain
        ls = subprocess.run(["git", "-C", str(self.repo_path), "ls-tree", "-r", c2], capture_output=True, text=True,
                            check=True).stdout
        oid = next(line.split()[2] for line in ls.splitlines() if line.endswith(ax1.id.hex()[2:]))
        (self.repo_path / ".git" / "objects" / oid[:2] / oid[2:]).unlink()
        with self.assertRaisesRegex(V.VarsError, "missing"):
            V.GitVarsRepo(self.repo_path).lens("core")

    def test_39_verify_needs_a_trust_anchor_the_reader_chose(self) -> None:
        """Monday F39: a bundle's own witness policy is self-declared. `verify-*` exits 0 only against keys the
        reader pins with --require (and, for a projection, with its data); `inspect-*` checks internal consistency
        and claims no trust."""
        mc = self._minds_chain()
        sk = b"\x07" * 32
        mc.init(self.repo_path, sk)
        repo = V.GitVarsRepo(self.repo_path)
        _, r1 = mc.release(self.repo_path, sk, "a" * 40, ["x OK"])
        _, r2 = mc.release(self.repo_path, sk, "b" * 40, ["x OK"])
        honest = json.loads(json.dumps(V.export_projection(repo, "minds", r2["projection"])))
        pk = V.ed25519_pubkey(sk).hex()

        # An attacker's projection: its own key as the whole witness policy, signed, no data
        ska = b"\x0b" * 32
        atoms: dict[bytes, bytes] = {}
        tip_atom = self._put_atom(atoms, V.atom_utf8("c" * 40))
        pol = self._pol(atoms, 1, [V.ed25519_pubkey(ska)])
        forged = V.Cell(V.H_SCHEMA["projection"], self._put_atom(atoms, V.atom_utf8("minds/projection/forged")),
                        V.H_EMPTY, slots=(tip_atom, V.H_LENS_KERNEL, V.sha256(b"in"), V.sha256(b"out"), pol))
        hv = V.parse_pol1(atoms[pol])[1]
        attack = {"format": honest["format"], "cell": forged.encode().hex(),
                  "atoms": [atoms[h].hex() for h in (tip_atom, pol, hv)],
                  "seals": [V.Seal.sign(ska, forged.id, forged.id).encode().hex()]}

        def cli(cmd, bundle, *pins):
            path = Path(self.tmp.name) / "bundle.json"
            path.write_text(json.dumps(bundle))
            args = [x for k in pins for x in ("--require", k)]
            return subprocess.run([sys.executable, str(ROOT_DIR / "vars1.py"), cmd, str(path), *args],
                                  capture_output=True, text=True).returncode

        self.assertEqual(cli("inspect-projection", attack), 0, "internally consistent, and inspect claims no more")
        self.assertNotEqual(cli("verify-projection", attack), 0, "no trust anchor chosen by the reader")
        self.assertNotEqual(cli("verify-projection", attack, pk), 0, "the pinned key did not witness it")
        self.assertNotEqual(cli("verify-projection", attack, V.ed25519_pubkey(ska).hex()), 0, "no data to verify")
        self.assertEqual(cli("verify-projection", honest, pk), 0)
        self.assertNotEqual(cli("verify-projection", honest, V.ed25519_pubkey(ska).hex()), 0,
                            "data present, but the pinned key is not a witness")
        # A policy naming a pinned key that never sealed: in the policy is not the same as having witnessed
        hc = V.Cell.decode(bytes.fromhex(honest["cell"]))
        a2: dict[bytes, bytes] = {V.sha256(bytes.fromhex(x)): bytes.fromhex(x) for x in honest["atoms"]}
        pol2 = self._pol(a2, 1, [V.ed25519_pubkey(sk), V.ed25519_pubkey(ska)])
        two = dataclasses.replace(hc, slots=(*hc.slots[:4], pol2))
        both = dict(honest, cell=two.encode().hex(),
                    atoms=[a2[h].hex() for h in (hc.slots[0], pol2, V.parse_pol1(a2[pol2])[1])],
                    seals=[V.Seal.sign(sk, two.id, two.id).encode().hex()])
        self.assertEqual(cli("verify-projection", both, pk), 0)
        self.assertNotEqual(cli("verify-projection", both, V.ed25519_pubkey(ska).hex()), 0,
                            "named in the policy, but never sealed it")
        self.assertNotEqual(cli("verify-projection", {k: v for k, v in honest.items() if k not in ("input", "output")},
                                pk), 0, "a verified projection carries its data")

        att = json.loads(json.dumps(V.export_attestation(repo, "minds", r1["decision"], r2["projection"])))
        self.assertEqual(cli("inspect-attestation", att), 0)
        self.assertNotEqual(cli("verify-attestation", att), 0, "the bundle's own scope policy is not a trust anchor")
        self.assertEqual(cli("verify-attestation", att, pk), 0)
        self.assertNotEqual(cli("verify-attestation", att, V.ed25519_pubkey(ska).hex()), 0)

    def test_43_test_numbers_are_unique(self) -> None:
        """Documents cite these tests by number (ASSURANCE.md), so a number names exactly one test."""
        numbers = re.findall(r"^    def test_(\d+)_", (ROOT_DIR / "test_vars1.py").read_text(), re.M)
        dupes = sorted({n for n in numbers if numbers.count(n) > 1})
        self.assertEqual(dupes, [], "test numbers used more than once")

    def test_44_supersedes_stays_within_a_schema_and_attested_names_no_witness(self) -> None:
        """Each rule alone, with its well-formed neighbour: a decision may not supersede an axiom (an axiom may); an
        ATTESTED verdict may not name even a real checkpoint (an INVALID verdict may)."""
        def supersede(schema_of_new):
            def b(put, ax, d, *_):
                newer = V.Cell(schema_of_new, put(V.atom_utf8("core/newer")), put(V.atom_utf8("newer")),
                               h_supersedes=put(V.atom_hvec([ax.id])), h_loss=put(V.atom_utf8("replaced")),
                               slots=(V.H_OWNER, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY) if schema_of_new == V.H_SCHEMA["decision"] else ())
                return [ax, newer]
            return b
        self.assertIn("cross-schema", self._try_admit(supersede(V.H_SCHEMA["decision"])) or "")
        self.assertIsNone(self._try_admit(supersede(V.H_SCHEMA["axiom"])))

        def verdict_naming_a_checkpoint(code):
            def b(put, ax, d, *_):
                raw = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=V.H_I, right=V.H_K)
                h = put(raw)
                env = SR.Environment([h], {h: raw})
                root = put(V.atom_computation_root(h, put(V.atom_environment([h]))))
                doc, i, state = SR.start(root.hex(), h)
                nf = SR.advance(doc, i, state, env, 10)
                comp = V.Cell(V.H_SCHEMA["computation"], put(V.atom_utf8("core/comp")), root)
                ck = V.Cell(V.H_SCHEMA["checkpoint"], put(V.atom_utf8("core/ck")), put(nf.state_bytes),
                            h_relies=put(V.atom_hvec([comp.id])),
                            slots=(root, put(V.atom_u64(10)), put(V.atom_u64(nf.checkpoint["spent_total"])),
                                   put(V.atom_u64(nf.checkpoint["peak_semantic_size"])), V.H_NORMAL_FORM,
                                   put(V.atom_u64(nf.checkpoint["transition_claim"]["actions"]))))
                w = V.Cell(V.H_SCHEMA["verdict"], put(V.atom_utf8("core/verdict")), d.id,
                           h_relies=put(V.atom_hvec([ck.id])), h_attests=put(V.atom_hvec([d.id])),
                           slots=(ck.id, code, put(V.atom_utf8("verifier"))))
                return [ax, d, comp, ck, w]
            return b
        self.assertIn("ATTESTED", self._try_admit(verdict_naming_a_checkpoint(V.H_ATTESTED)) or "")
        self.assertIsNone(self._try_admit(verdict_naming_a_checkpoint(V.H_VERDICT_INVALID)))

    def test_45_the_spec_is_a_projection_of_its_witnesses(self) -> None:
        """tools/check_claims.py passes on the repository, and refuses each way the spec could go green over nothing:
        an uncovered normative paragraph, an edited quote, a witness that does not exist, a tested claim without a
        mutant."""
        tool = ROOT_DIR / "tools" / "check_claims.py"
        spec = (ROOT_DIR / "VARS-1-SPEC.md").read_text()
        claims = json.loads((ROOT_DIR / "claims.json").read_text())

        assurance = (ROOT_DIR / "ASSURANCE.md").read_text()
        norm = lambda t: re.sub(r"\s+", " ", t).strip()

        def check(spec_text, claims_obj, assurance_text=assurance):
            d = Path(self.tmp.name)
            (d / "spec.md").write_text(spec_text)
            (d / "claims.json").write_text(json.dumps(claims_obj))
            (d / "assurance.md").write_text(assurance_text)
            out = subprocess.run([sys.executable, str(tool), "--spec", str(d / "spec.md"), "--claims", str(d / "claims.json"),
                                  "--assurance", str(d / "assurance.md")], capture_output=True, text=True)
            return out.returncode, out.stdout

        code, out = check(spec, claims)
        self.assertEqual(code, 0, out)
        anchor = "### 4.3 Rules object"
        code, out = check(spec.replace(anchor, anchor + "\n\nA new rule nobody holds to anything.\n"), claims)
        self.assertEqual(code, 1)
        self.assertIn("no claim or informative quote covers this block", out)
        code, out = check(spec.replace("Non-canonical bytes are refused, never normalized.",
                                       "Non-canonical bytes are refused, sometimes normalized."), claims)
        self.assertIn("atoms.canonical: quote not in the spec", out)
        weak = json.loads(json.dumps(claims))
        tested = next(c for c in weak["claims"] if c["status"] == "tested")
        tested["witnesses"] = ["test:test_99_does_not_exist"]
        code, out = check(spec, weak)
        self.assertIn("witness does not exist: test:test_99_does_not_exist", out)
        bare = json.loads(json.dumps(claims))
        tested = next(c for c in bare["claims"] if c["status"] == "tested")
        tested["mutants"] = []
        code, out = check(spec, bare)
        self.assertIn(f"{tested['id']}: tested without a mutant", out)
        # a claim on what the tools establish beyond the spec quotes ASSURANCE.md, and goes stale like any other
        moved = json.loads(json.dumps(claims))
        held = next(c for c in moved["claims"] if c.get("source") == "ASSURANCE.md")
        held["quote"] += " and more"
        code, out = check(spec, moved)
        self.assertIn(f"{held['id']}: quote in 0 rows of ASSURANCE.md", out)
        # a quote kept only in a comment, its live row changed, holds nothing (Codex PR #4 r1 F6)
        row = next(l for l in assurance.splitlines() if norm(held["quote"][: -len(" and more")]) in norm(l))
        hidden = assurance.replace(row, "| `verify-release` does not check profiles | Not established | — |\n<!--\n" + row + "\n-->")
        code, out = check(spec, claims, hidden)
        self.assertIn(f"{held['id']}: quote in 0 rows of ASSURANCE.md", out)
        code, out = check(spec, claims, hidden.replace("<!--\n", "```\n").replace("\n-->", "\n```"))
        self.assertIn(f"{held['id']}: quote in 0 rows of ASSURANCE.md", out, "nor in a fenced example (Codex r2 F4)")
        # a live row whose evidence column no longer states the claim's status
        code, out = check(spec, claims, assurance.replace(row, row.replace("| Tested, with mutants |", "| Assumed |")))
        self.assertIn(f"{held['id']}: ASSURANCE.md row says 'Assumed'", out)
        held["quote"], held["source"] = held["quote"][: -len(" and more")], "README.md"
        code, out = check(spec, moved)
        self.assertIn(f"{held['id']}: unknown source 'README.md'", out)

    def test_46_latches_and_witnesses_need_their_quorum_and_kind(self) -> None:
        """Below its quorum an acceptance admits nothing and a custom schema is not Authorized; at the quorum both
        are. A decision whose only verdict is NOT_ASSESSED is not Settled; an ATTESTED one settles it."""
        c0, s0 = self._genesis([self.pk1, self.pk2], 2, [self.pk1, self.pk2], 2, [self.sk1, self.sk2])
        a: dict[bytes, bytes] = {}
        fb = self._scope_cell(a, "peerB", "peerB", (1, [self.pk_peer]))
        fx = self._axiom(a, "peerB/x", "a peerB fact")
        schema = V.Cell(V.H_META_SCHEMA, self._put_atom(a, V.atom_utf8("core/custom")), V.H_EMPTY,
                        slots=(self._put_atom(a, V.atom_utf8("n:u64")),))
        acc = V.Cell(h_schema=V.H_SCHEMA["acceptance"], h_slot_name=self._put_atom(a, V.atom_utf8("core/acc")),
                     h_payload=fx.id, slots=(self._put_atom(a, V.atom_utf8("peerB")), fb.id))
        d = V.Cell(V.H_SCHEMA["decision"], self._put_atom(a, V.atom_utf8("core/d")), self._put_atom(a, V.atom_utf8("d")),
                   slots=(V.H_OWNER, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY))
        na = V.Cell(V.H_SCHEMA["verdict"], self._put_atom(a, V.atom_utf8("core/na")), d.id,
                    h_attests=self._hv(a, [d.id]),
                    slots=(V.H_EMPTY, V.H_NOT_ASSESSED, self._put_atom(a, V.atom_utf8("v1"))))
        c1 = self._admit(a, [fb, fx, schema, acc, d, na],
                         [V.Seal.sign(self.sk_peer, fb.id, fb.id), V.Seal.sign(self.sk_peer, fx.id, fb.id),
                          V.Seal.sign(self.sk1, schema.id, s0.id), V.Seal.sign(self.sk1, acc.id, s0.id),
                          V.Seal.sign(self.sk1, d.id, s0.id), V.Seal.sign(self.sk1, na.id, s0.id),
                          V.Seal.sign(self.sk2, na.id, s0.id)], c0)
        lens = self.repo.lens("core")
        self.assertFalse(lens["accepted"][fx.id], "an acceptance below its quorum admits nothing")
        self.assertFalse(lens["settled"][schema.id], "a custom schema below the admission quorum is not Authorized")
        self.assertFalse(lens["settled"][d.id], "a NOT_ASSESSED verdict is no witness")

        a = {}
        ok = V.Cell(V.H_SCHEMA["verdict"], self._put_atom(a, V.atom_utf8("core/ok")), d.id,
                    h_attests=self._hv(a, [d.id]), slots=(V.H_EMPTY, V.H_ATTESTED, self._put_atom(a, V.atom_utf8("v2"))))
        self._admit(a, [ok], [V.Seal.sign(self.sk2, schema.id, s0.id), V.Seal.sign(self.sk2, acc.id, s0.id),
                              V.Seal.sign(self.sk1, ok.id, s0.id), V.Seal.sign(self.sk2, ok.id, s0.id)], c1)
        lens = self.repo.lens("core")
        self.assertTrue(lens["accepted"][fx.id])
        self.assertTrue(lens["settled"][schema.id])
        self.assertTrue(lens["settled"][d.id])

    # -- rules v2 (RULES-V2.md, dormant) and changing the rules (VARS-1-SPEC.md §4.3) ----------------------------------
    def _commit(self, scope: str, parent: str, governing: V.Cell, a: dict[bytes, bytes], cells: list,
                sk: bytes | None = None) -> str:
        sk = sk or self.sk1
        c = self.repo.build_candidate_commit(scope, a, cells, [V.Seal.sign(sk, x.id, governing.id) for x in cells],
                                             parent_commit=parent)
        self.repo.admit_and_advance(scope, c, expected_old=parent)
        return c

    def _r2_03(self) -> tuple[tuple[str, int], V.Cell, V.Cell]:
        """Codex R2-03 as a chain under v2 rules, scope `cx`: a foreign cell Y, accepted, holds as an opaque `digest`
        the id of a cell X of its own origin born after it. v1 reads every payload or slot equal to a cell id as a
        reference, so X becomes Accepted through Y; v2 reads a `digest` field as a value, so X is not.
        Returns (tip, X's index in the v2 kernel input), Y and X."""
        a = {**V.STD_SCHEMA_ATOMS, V.H_LENS_KERNEL_V2: V.KERNEL2_ATOM}
        pol = self._pol(a, 1, [self.pk1])
        s0 = V.Cell(V.H_SCHEMA["scope"], self._put_atom(a, V.atom_utf8("cx/SCOPE")),
                    self._put_atom(a, V.atom_utf8("counterexample R2-03")), slots=(pol, pol, V.H_LENS_KERNEL_V2))
        c0 = self.repo.build_candidate_commit("cx", a, [*V.STD_SCHEMAS.values(), s0],
                                              [V.Seal.sign(self.sk1, s0.id, s0.id)], parent_commit=None)
        self.repo.admit_and_advance("cx", c0, expected_old=None)
        b: dict[bytes, bytes] = {}
        put = lambda raw: self._put_atom(b, raw)  # noqa: E731
        ppol = self._pol(b, 1, [self.pk_peer])
        sp = V.Cell(V.H_SCHEMA["scope"], put(V.atom_utf8("peerB/SCOPE")), put(V.atom_utf8("peerB")),
                    slots=(ppol, ppol, V.H_LENS_KERNEL))
        opaque = V.Cell(V.H_META_SCHEMA, put(V.atom_utf8("cx/opaque")), V.H_EMPTY,
                        slots=(put(V.atom_utf8("value:digest")),))
        xa: dict[bytes, bytes] = {}
        x = self._axiom(xa, "peerB/x", "born after the digest that names it")
        y = V.Cell(opaque.id, put(V.atom_utf8("peerB/y")), put(V.atom_utf8("y")), slots=(x.id,))
        acc = V.Cell(V.H_SCHEMA["acceptance"], put(V.atom_utf8("cx/accept.y")), y.id,
                     slots=(put(V.atom_utf8("peerB")), sp.id))
        c1 = self.repo.build_candidate_commit("cx", b, [sp, opaque, y, acc], [
            V.Seal.sign(self.sk_peer, sp.id, sp.id), V.Seal.sign(self.sk1, opaque.id, s0.id),
            V.Seal.sign(self.sk_peer, y.id, sp.id), V.Seal.sign(self.sk1, acc.id, s0.id)], parent_commit=c0)
        self.repo.admit_and_advance("cx", c1, expected_old=c0)
        c2 = self.repo.build_candidate_commit("cx", xa, [x], [V.Seal.sign(self.sk_peer, x.id, sp.id)], parent_commit=c1)
        try:
            self.repo.admit_and_advance("cx", c2, expected_old=c1)
        except V.VarsError as e:
            self.fail(f"a digest written in a v2 epoch vetoed the later cell it names: {e}")
        order = self.repo.rules_output("cx", c2, V.H_LENS_KERNEL_V2)[1]["order"]
        self.cx_y, self.cx_s0 = y, s0
        return (c2, order.index(x.id)), y, x

    def _change_rules(self, scope: str, parent: str, base: V.Cell, new_rules: bytes, sks: list[bytes],
                      cx: tuple[str, int], *, label: str = "v2", fields: "list[str] | None" = None,
                      override: "dict | None" = None, decision_sks: "list[bytes] | None" = None,
                      rotate: bool = True, decide: bool = True, twice: bool = False,
                      schema: bool = True, cx_scope: str = "cx") -> tuple[str, V.Cell, "V.Cell | None"]:
        """A candidate commit (not admitted) rotating `scope` from `base` to a scope naming `new_rules`, with a
        rules-change decision whose digests are the gate's own replay; `override` then replaces fields by name
        (a value, or a function of `put`), and `fields` builds it on a schema with only those fields."""
        cx_tip, cx_cell = cx
        a = dict(V.RULES_ATOMS)
        put = lambda raw: self._put_atom(a, raw)  # noqa: E731
        sch, sch_atoms = V.rules_change_schema(scope)
        a.update(sch_atoms)
        if fields is not None:
            sch = V.Cell(V.H_META_SCHEMA, sch.h_slot_name, V.H_EMPTY, slots=tuple(put(V.atom_utf8(f)) for f in fields))
        ev = self.repo.rules_change_evidence(scope, parent, base.slots[2], new_rules, cx_scope, cx_tip)
        vals = {"old_rules": base.slots[2], "new_rules": new_rules, "basis": put(V.atom_utf8(parent)),
                "reproduce": ev["reproduce"], "counterexample_scope": put(V.atom_utf8(cx_scope)),
                "counterexample": put(V.atom_utf8(cx_tip)), "cell": put(V.atom_u64(cx_cell)),
                "status": put(V.atom_u64(0)), "right": put(V.atom_u64(0)),  # X is not Accepted
                "refutes": ev["refutes"], "latches": ev["latches"]}
        for k, v in (override or {}).items():
            vals[k] = v(put) if callable(v) else v
        names = [f.split(":")[0] for f in (fields or V.RULES_CHANGE_FIELDS)]

        def decision(tag: str) -> V.Cell:
            return V.Cell(sch.id, put(V.atom_utf8(f"{scope}/rules-change/{label}{tag}")),
                          put(V.atom_utf8(f"{scope} moves to rules {new_rules.hex()[:12]}: Codex R2-03{tag}")),
                          slots=tuple(vals[n] for n in names))

        s = V.Cell(V.H_SCHEMA["scope"], put(V.atom_utf8(f"{scope}/SCOPE")), put(V.atom_utf8(f"{scope} under {label}")),
                   h_supersedes=self._hv(a, [base.id]), h_loss=put(V.atom_utf8(f"rules change to {label}")),
                   slots=(base.slots[0], base.slots[1], new_rules))
        ds = ([decision("")] if decide else []) + ([decision(".again")] if twice else [])
        cells = ds + ([s] if rotate else []) + ([sch] if schema and ds else [])
        seals = [V.Seal.sign(k, s.id, base.id) for k in sks] if rotate else []
        seals += [V.Seal.sign(k, d.id, base.id) for d in ds for k in (decision_sks or sks)]
        seals += [V.Seal.sign(sks[0], sch.id, base.id)] if schema and ds else []
        c = self.repo.build_candidate_commit(scope, a, cells, seals, parent_commit=parent)
        return c, s, (ds[0] if ds else None)

    def _gate_refuses(self, regex: str, scope: str, cand: str, parent: str) -> None:
        with self.assertRaisesRegex(V.VarsError, regex):
            self.repo.admit_and_advance(scope, cand, expected_old=parent)

    def _rules_change_fixture(self) -> tuple[tuple[str, int], str, V.Cell]:
        cx, _, _ = self._r2_03()
        c0, s0, _ = self._bootstrap_genesis("core")
        a: dict[bytes, bytes] = {}
        c1 = self._commit("core", c0, s0, a, [self._axiom(a, "core/fact", "a fact")])
        return cx, c1, s0

    def test_47_rules_change_admits_a_rotation_whose_decision_replays(self) -> None:
        """§4.3: a rotation v1 -> v2 is admitted with a rules-change decision whose three computations the gate
        replays: the new rules reproduce the history, refute the old on Codex R2-03, and keep every latch."""
        cx, c1, s0 = self._rules_change_fixture()
        ev = self.repo.rules_change_evidence("core", c1, V.H_LENS_KERNEL, V.H_LENS_KERNEL_V2, "cx", cx[0])
        old_cx, new_cx = ev["counterexample"]
        x = new_cx["order"][cx[1]]
        self.assertEqual((old_cx["status"][x] & 1, new_cx["status"][x] & 1), (1, 0),
                         "R2-03: under v1 the digest makes X Accepted, under v2 it does not")
        self.assertEqual(ev["basis"][0]["status"], ev["basis"][1]["status"])

        cand, s1, d = self._change_rules("core", c1, s0, V.H_LENS_KERNEL_V2, [self.sk1], cx)
        self.repo.admit_and_advance("core", cand, expected_old=c1)
        lens = self.repo.lens("core")
        self.assertEqual(lens["rules"], V.H_LENS_KERNEL, "the rotation commit is still in the old epoch")
        self.assertTrue(lens["active"][d.id] and lens["active"][s1.id])
        a: dict[bytes, bytes] = {}
        self._commit("core", cand, s1, a, [self._axiom(a, "core/after", "after the change")])
        lens = self.repo.lens("core")
        self.assertEqual(lens["rules"], V.H_LENS_KERNEL_V2)
        self.assertEqual(struct.unpack_from("<I", lens["kernel_input"])[0], V.KERNEL2_MAGIC)

    def test_48_rules_change_needs_its_decision(self) -> None:
        """A rotation to other rules without a rules-change decision is refused, and so is one whose decision lacks
        the fields of (a), (b) or (c) (another schema, so no decision), names other rules or another basis, lacks
        the admission quorum, comes twice, or comes without the rotation it decides."""
        cx, c1, s0 = self._rules_change_fixture()
        V2 = V.H_LENS_KERNEL_V2
        need = "exactly one rules-change decision"
        self._gate_refuses(need, "core", self._change_rules("core", c1, s0, V2, [self.sk1], cx, decide=False)[0], c1)
        for drop in ({"reproduce"}, {"counterexample_scope", "counterexample", "cell", "status", "right", "refutes"},
                     {"latches"}):
            fields = [f for f in V.RULES_CHANGE_FIELDS if f.split(":")[0] not in drop]
            self._gate_refuses(need, "core", self._change_rules("core", c1, s0, V2, [self.sk1], cx, fields=fields)[0], c1)
        self._gate_refuses(need, "core", self._change_rules("core", c1, s0, V2, [self.sk1], cx, twice=True)[0], c1)
        self._gate_refuses("comes only with the rotation", "core",
                      self._change_rules("core", c1, s0, V2, [self.sk1], cx, rotate=False)[0], c1)
        self._gate_refuses("other rules than those the rotation changes", "core",
                      self._change_rules("core", c1, s0, V2, [self.sk1], cx,
                                         override={"old_rules": V2})[0], c1)
        self._gate_refuses("basis is not the chain so far", "core",
                      self._change_rules("core", c1, s0, V2, [self.sk1], cx,
                                         override={"basis": lambda put: put(V.atom_utf8("0" * 40))})[0], c1)
        # a 2-of-2 roster: the rotation carries both seals, the decision only one
        q0, t0, _ = self._bootstrap_genesis("q", adm_threshold=2)
        self._gate_refuses("lacks the governing scope's admission quorum", "q",
                      self._change_rules("q", q0, t0, V2, [self.sk1, self.sk2], cx, decision_sks=[self.sk1])[0], q0)
        cand, _, _ = self._change_rules("q", q0, t0, V2, [self.sk1, self.sk2], cx)
        self.repo.admit_and_advance("q", cand, expected_old=q0)

    def test_49_rules_change_a_reproduces_the_history(self) -> None:
        """(a): a reproduce digest other than the replay's is refused, and so are new rules that change a status of
        the chain so far (a stand-in that flips one status byte of the replay), digests notwithstanding."""
        cx, c1, s0 = self._rules_change_fixture()
        V2 = V.H_LENS_KERNEL_V2
        self._gate_refuses(r"\(a\): the decision's reproduce digest", "core",
                      self._change_rules("core", c1, s0, V2, [self.sk1], cx, override={"reproduce": bytes(32)})[0], c1)
        real = self.repo.rules_output

        def flips_a_status(scope, tip, rules):
            out, read = real(scope, tip, rules)
            if scope == "core" and rules == V2:
                read = {**read, "status": {**read["status"], s0.id: read["status"][s0.id] ^ 0x40}}
            return out, read

        self.repo.rules_output = flips_a_status
        try:
            self._gate_refuses(r"\(a\): the new rules do not reproduce", "core",
                          self._change_rules("core", c1, s0, V2, [self.sk1], cx)[0], c1)
        finally:
            del self.repo.rules_output

    def test_50_rules_change_b_refutes_the_old_rules(self) -> None:
        """(b): the counterexample must be a chain the gate admits, its digest the replay's, and the named status
        must be one the new rules give right and the old rules wrong."""
        cx, c1, s0 = self._rules_change_fixture()
        V2 = V.H_LENS_KERNEL_V2
        attempt = lambda **o: self._change_rules("core", c1, s0, V2, [self.sk1], cx, override=o)[0]  # noqa: E731
        self._gate_refuses(r"\(b\): the decision's refutes digest", "core", attempt(refutes=bytes(32)), c1)
        self._gate_refuses(r"\(b\): the new rules do not give", "core",
                      attempt(right=lambda put: put(V.atom_u64(1))), c1)
        y_ix = self.repo.rules_output("cx", cx[0], V2)[1]["order"].index(self.cx_y.id)
        self._gate_refuses(r"\(b\): the old rules give that verdict too", "core",
                      attempt(cell=lambda put: put(V.atom_u64(y_ix)), right=lambda put: put(V.atom_u64(1))), c1)
        for o in ({"cell": 10_000}, {"status": 7}, {"right": 2}):
            (k, v), = o.items()
            self._gate_refuses(r"\(b\): the decision names no status", "core",
                          attempt(**{k: lambda put, v=v: put(V.atom_u64(v))}), c1)
        # a counterexample tip whose chain the gate refuses: an unsealed cell on top of the R2-03 chain
        ua: dict[bytes, bytes] = {}
        bad_tip = self.repo.build_candidate_commit("cx", ua, [self._axiom(ua, "cx/unsealed", "no seal")], [],
                                                   parent_commit=cx[0])
        self._gate_refuses("lacks a valid Seal", "core", attempt(counterexample=lambda put: put(V.atom_utf8(bad_tip))), c1)
        # either rules refusing either log refuses the rotation (a stand-in: the old rules refuse the counterexample)
        honest, real = attempt(), self.repo.rules_output

        def refuses(scope, tip, rules):
            if scope == "cx" and rules == V.H_LENS_KERNEL:
                raise V.KernelRefusal(-2)
            return real(scope, tip, rules)

        self.repo.rules_output = refuses
        try:
            self._gate_refuses("rules change: the old rules over the counterexample: rules kernel E-2", "core", honest, c1)
        finally:
            del self.repo.rules_output

    def test_51_rules_change_c_latches_only_grow(self) -> None:
        """(c): a latches digest other than the replay's is refused, and so are new rules that drop a latch the old
        rules set, over the chain so far or over the counterexample, while every status is reproduced."""
        cx, c1, s0 = self._rules_change_fixture()
        V2 = V.H_LENS_KERNEL_V2
        self._gate_refuses(r"\(c\): the decision's latches digest", "core",
                      self._change_rules("core", c1, s0, V2, [self.sk1], cx, override={"latches": bytes(32)})[0], c1)
        real = self.repo.rules_output
        for on in ("core", "cx"):
            def drops_a_latch(scope, tip, rules, on=on):
                out, read = real(scope, tip, rules)
                if scope == on and rules == V2:
                    auth = dict(read["auth"])
                    auth[next(k for k, v in auth.items() if v and k not in V.STD_SCHEMA_IDS)] = 0
                    read = {**read, "auth": auth}
                return out, read

            self.repo.rules_output = drops_a_latch
            try:
                self._gate_refuses(r"\(c\): a latch the old rules set is lost", "core",
                              self._change_rules("core", c1, s0, V2, [self.sk1], cx)[0], c1)
            finally:
                del self.repo.rules_output

    def test_52_rules_never_rotate_back_to_v1(self) -> None:
        """A rotation from v2 back to v1 is refused (kernel E-25 and its twin), with or without a decision; a
        rotation that keeps v2 needs none."""
        cx, c1, s0 = self._rules_change_fixture()
        cand, s1, _ = self._change_rules("core", c1, s0, V.H_LENS_KERNEL_V2, [self.sk1], cx)
        self.repo.admit_and_advance("core", cand, expected_old=c1)
        for decide in (True, False):
            back, _, _ = self._change_rules("core", cand, s1, V.H_LENS_KERNEL, [self.sk1], cx, label="back",
                                            decide=decide, schema=False)
            self._gate_refuses("rules kernel E-25:", "core", back, cand)
        again, _, _ = self._change_rules("core", cand, s1, V.H_LENS_KERNEL_V2, [self.sk1], cx, label="v2-again",
                                         decide=False)
        self.repo.admit_and_advance("core", again, expected_old=cand)
        self.assertEqual(self.repo.lens("core")["rules"], V.H_LENS_KERNEL_V2)

    def test_53_v1_releases_survive_a_rules_change(self) -> None:
        """tools/minds_chain.py after a rotation to v2 (Monday F40): `release` and `join` keep the governing rules,
        a release projection names its tip's epoch, and v1 projection and attestation bundles made before the
        change still verify against a pinned key; a v2 projection is admitted, and offline it is unsupported."""
        mc = self._minds_chain()
        sk, sk2 = b"\x07" * 32, b"\x08" * 32
        pk = V.ed25519_pubkey(sk)
        mc.init(self.repo_path, sk)
        repo = V.GitVarsRepo(self.repo_path)
        _, r1 = mc.release(self.repo_path, sk, "a" * 40, ["x OK"])
        _, r2 = mc.release(self.repo_path, sk, "b" * 40, ["x OK"])
        cx, _, _ = self._r2_03()
        tip = repo.ref_commit("minds")
        base = repo.read_cas_tree(tip)[1][mc.governing_scope(repo)]
        cand, _, _ = self._change_rules("minds", tip, base, V.H_LENS_KERNEL_V2, [sk], cx)
        self.repo.admit_and_advance("minds", cand, expected_old=tip)
        self.assertEqual(mc.governing_rules(repo), V.H_LENS_KERNEL_V2)

        def admitted(step, *args):
            try:
                return step(self.repo_path, sk, *args)
            except V.VarsError as e:
                self.fail(f"{step.__name__} after the change to v2 was refused: {e}")

        _, r3 = admitted(mc.release, "c" * 40, ["x OK"])  # its projection's tip is the rotation: a v1 epoch
        _, r4 = admitted(mc.release, "d" * 40, ["x OK"])  # its projection's tip is in the v2 epoch
        rows = {r["name"]: r for r in mc.show(self.repo_path)}
        self.assertIn(f"rules@{V.H_LENS_KERNEL_V2.hex()}", rows["minds/release/cccccccccccc"]["statement"])
        cells = repo.read_cas_tree(repo.ref_commit("minds"))[1]
        self.assertEqual(cells[r3["projection"]].slots[1], V.H_LENS_KERNEL)
        self.assertEqual(cells[r4["projection"]].slots[1], V.H_LENS_KERNEL_V2)
        admitted(mc.join, V.ed25519_pubkey(sk2), "second")
        self.assertEqual(mc.governing_rules(repo), V.H_LENS_KERNEL_V2, "a membership rotation keeps the rules")

        got = V.verify_projection(json.loads(json.dumps(V.export_projection(repo, "minds", r2["projection"]))),
                                  require=[pk])
        self.assertTrue(got["witnessed"] and got["data_ok"] and not got["required_missing"])
        b = json.loads(json.dumps(V.export_attestation(repo, "minds", r1["decision"], r2["projection"])))
        self.assertTrue(V.verify_attestation(b, require=[pk])["accepted"])
        self.assertTrue(repo.lens("minds")["settled"][r4["projection"]])
        got = V.verify_projection(json.loads(json.dumps(V.export_projection(repo, "minds", r4["projection"]))))
        self.assertEqual(got["rules_status"], "unsupported", "the offline verifier interprets v1 only")

    def test_54_rules_v2_keep_an_opaque_digest_opaque(self) -> None:
        """RULES-V2: after the change to v2, a digest equal to a later cell's id stays opaque and vetoes nothing; the
        same digest written in the v1 epoch still refuses that cell, after the change too."""
        cx, c1, s0 = self._rules_change_fixture()
        fa: dict[bytes, bytes] = {}
        planned_v1 = self._axiom(fa, "core/planned-1", "planned in v1")
        planned_v2 = self._axiom(fa, "core/planned-2", "planned in v2")
        a: dict[bytes, bytes] = {}
        schema = V.Cell(V.H_META_SCHEMA, self._put_atom(a, V.atom_utf8("core/opaque-schema")), V.H_EMPTY,
                        slots=(self._put_atom(a, V.atom_utf8("value:digest")),))
        holder1 = V.Cell(schema.id, self._put_atom(a, V.atom_utf8("core/holder-1")), self._put_atom(a, V.atom_utf8("h1")),
                         slots=(planned_v1.id,))
        c2 = self._commit("core", c1, s0, a, [schema, holder1])
        cand, s1, _ = self._change_rules("core", c2, s0, V.H_LENS_KERNEL_V2, [self.sk1], cx)
        self.repo.admit_and_advance("core", cand, expected_old=c2)
        a3: dict[bytes, bytes] = {}
        holder2 = V.Cell(schema.id, self._put_atom(a3, V.atom_utf8("core/holder-2")),
                         self._put_atom(a3, V.atom_utf8("h2")), slots=(planned_v2.id,))
        c3 = self._commit("core", cand, s1, a3, [holder2])
        try:
            c4 = self._commit("core", c3, s1, dict(fa), [planned_v2])
        except V.VarsError as e:
            self.fail(f"a digest written in the v2 epoch vetoed the cell it names: {e}")
        fold = self.repo._evaluate_commit_chain("core", self.repo.commit_chain(c4))
        self.assertEqual(fold["value_refs"][holder2.id], [], "a v2 digest is never a reference")
        self.assertEqual(fold["value_refs"][holder1.id], [], "nor is a v1 digest naming no cell yet")
        self.assertTrue(self.repo.lens("core")["active"][planned_v2.id])
        late = self.repo.build_candidate_commit("core", dict(fa), [planned_v1],
                                                [V.Seal.sign(self.sk1, planned_v1.id, s1.id)], parent_commit=c4)
        self._gate_refuses("later-born cell", "core", late, c4)

    def test_55_rules_v2_read_references_by_type(self) -> None:
        """RULES-V2: a v2-born cell's references are its typed positions (a `cell` field); `hash` and `digest`
        values naming existing cells are not. A v1-born cell keeps v1's reading under v2."""
        cx, c1, s0 = self._rules_change_fixture()
        a: dict[bytes, bytes] = {}
        target = self._axiom(a, "core/target", "target")
        schema = V.Cell(V.H_META_SCHEMA, self._put_atom(a, V.atom_utf8("core/mixed-schema")), V.H_EMPTY,
                        slots=tuple(self._put_atom(a, V.atom_utf8(d)) for d in ("link:cell", "d:digest", "h:hash")))
        old = V.Cell(schema.id, self._put_atom(a, V.atom_utf8("core/old")), target.id, slots=(target.id,) * 3)
        c2 = self._commit("core", c1, s0, a, [target, schema, old])
        cand, s1, _ = self._change_rules("core", c2, s0, V.H_LENS_KERNEL_V2, [self.sk1], cx)
        self.repo.admit_and_advance("core", cand, expected_old=c2)
        a3: dict[bytes, bytes] = {}
        new = V.Cell(schema.id, self._put_atom(a3, V.atom_utf8("core/new")), target.id, slots=(target.id,) * 3)
        c3 = self._commit("core", cand, s1, a3, [new])
        fold = self.repo._evaluate_commit_chain("core", self.repo.commit_chain(c3))
        self.assertEqual(fold["rules"], V.H_LENS_KERNEL_V2)
        self.assertEqual(fold["value_refs"][new.id], [(1, target.id)], "only the `cell` field is a reference")
        self.assertEqual(fold["value_refs"][old.id], [(p, target.id) for p in range(4)],
                         "v1-born: the payload and every slot")

    def test_56_rules_v2_kernel_checks_the_reference_list(self) -> None:
        """The v2 module recomputes every cell's reference positions and refuses an input whose list differs, and a
        v1-encoded input; over a log wholly in v1 epochs it gives v1's output byte for byte."""
        cx, c1, s0 = self._rules_change_fixture()
        a: dict[bytes, bytes] = {}
        target = self._axiom(a, "core/target", "target")
        schema = V.Cell(V.H_META_SCHEMA, self._put_atom(a, V.atom_utf8("core/link-schema")), V.H_EMPTY,
                        slots=(self._put_atom(a, V.atom_utf8("link:cell")), self._put_atom(a, V.atom_utf8("d:digest"))))
        c2 = self._commit("core", c1, s0, a, [target, schema])
        v1_deltas = self.repo.chain_deltas(self.repo.commit_chain(c2))
        run1, run2 = V.kernel_runner(V.H_LENS_KERNEL).run, V.kernel_runner(V.H_LENS_KERNEL_V2).run
        self.assertEqual(run2(V.kernel_facts("core", v1_deltas, V.H_LENS_KERNEL_V2)[0]),
                         run1(V.kernel_facts("core", v1_deltas)[0]))
        with self.assertRaisesRegex(V.KernelRefusal, "E-1:"):
            run2(V.kernel_facts("core", v1_deltas)[0])
        cand, s1, _ = self._change_rules("core", c2, s0, V.H_LENS_KERNEL_V2, [self.sk1], cx)
        self.repo.admit_and_advance("core", cand, expected_old=c2)
        a3: dict[bytes, bytes] = {}
        linker = V.Cell(schema.id, self._put_atom(a3, V.atom_utf8("core/linker")), self._put_atom(a3, V.atom_utf8("x")),
                        slots=(target.id, target.id))
        c3 = self._commit("core", cand, s1, a3, [linker])
        deltas = self.repo.chain_deltas(self.repo.commit_chain(c3))
        run2(V.kernel_facts("core", deltas)[0])  # the honest encoding is accepted
        real = V.cell_refs
        try:
            for fake, why in ((lambda c, cells, atoms, v1: [], "dropped"),
                              (lambda c, cells, atoms, v1: real(c, cells, atoms, True), "untyped added")):
                V.cell_refs = lambda c, cells, atoms, v1, f=fake: f(c, cells, atoms, v1) if c.id == linker.id \
                    else real(c, cells, atoms, v1)
                with self.assertRaisesRegex(V.KernelRefusal, "E-6:", msg=why):
                    run2(V.kernel_facts("core", deltas)[0])
        finally:
            V.cell_refs = real

    def test_57_rules_v2_from_genesis(self) -> None:
        """A scope may start under v2 without a decision: its genesis stores the module and names it. Projections
        name the rules of their tip's epoch."""
        atoms = {**V.STD_SCHEMA_ATOMS, V.H_LENS_KERNEL_V2: V.KERNEL2_ATOM}
        pol = self._pol(atoms, 1, [self.pk1])
        s0 = V.Cell(V.H_SCHEMA["scope"], self._put_atom(atoms, V.atom_utf8("core/SCOPE")),
                    self._put_atom(atoms, V.atom_utf8("core")), slots=(pol, pol, V.H_LENS_KERNEL_V2))
        c0 = self.repo.build_candidate_commit("core", atoms, [*V.STD_SCHEMAS.values(), s0],
                                              [V.Seal.sign(self.sk1, s0.id, s0.id)], parent_commit=None)
        self.repo.admit_and_advance("core", c0, expected_old=None)
        lens = self.repo.lens("core")
        self.assertEqual(lens["rules"], V.H_LENS_KERNEL_V2)
        self.assertTrue(lens["active"][s0.id])
        # rules this host does not implement are refused, even as a stored wasm module
        other = {**atoms, V.sha256(b"\0asm\1\0\0\0"): b"\0asm\1\0\0\0"}
        s9 = V.Cell(V.H_SCHEMA["scope"], s0.h_slot_name, s0.h_payload, slots=(pol, pol, V.sha256(b"\0asm\1\0\0\0")))
        self._gate_refuses("rules this host does not implement", "other", self.repo.build_candidate_commit(
            "other", other, [*V.STD_SCHEMAS.values(), s9], [V.Seal.sign(self.sk1, s9.id, s9.id)], parent_commit=None), None)
        h_in, h_state = self.repo.projection_digests("core", c0)
        for rules, ok in ((V.H_LENS_KERNEL, False), (V.H_LENS_KERNEL_V2, True)):
            pa: dict[bytes, bytes] = {}
            p = V.Cell(V.H_SCHEMA["projection"], self._put_atom(pa, V.atom_utf8("core/p")), V.H_EMPTY,
                       slots=(self._put_atom(pa, V.atom_utf8(c0)), rules, h_in, h_state, pol))
            c = self.repo.build_candidate_commit("core", pa, [p], [V.Seal.sign(self.sk1, p.id, s0.id)], parent_commit=c0)
            if ok:
                self.repo.admit_and_advance("core", c, expected_old=c0)
            else:
                self._gate_refuses("rules than those of its tip's epoch", "core", c, c0)

    def test_58_release_checks_rebuild_every_rules_module(self) -> None:
        """Monday F41: a release rebuilds every rules module its commit carries; each must hash to its identity,
        and the rules the release names must be among them (an older commit without kernel2/ checks kernel/)."""
        mc = self._minds_chain()
        root = Path(self.tmp.name) / "wt"
        built = {"kernel": V.KERNEL_ATOM, "kernel2": V.KERNEL2_ATOM, "commit-bound": V.KERNEL1B_ATOM}

        def fake_cargo(cmd, cwd):
            out = cwd / "target" / "wasm32-unknown-unknown" / "release"
            out.mkdir(parents=True, exist_ok=True)
            (out / ("vars_lens.wasm" if cwd.name == "kernel" else "vars_lens2.wasm")).write_bytes(
                built["commit-bound" if "commit-bound" in cmd else cwd.name])
            return True

        (root / "kernel").mkdir(parents=True)
        self.assertEqual(mc.kernel_checks(root, V.H_LENS_KERNEL, fake_cargo),
                         [("kernel rebuild hashes to H_LENS_KERNEL", True), ("the released rules are rebuilt here", True)])
        self.assertFalse(mc.kernel_checks(root, V.H_LENS_KERNEL_V2, fake_cargo)[-1][1])
        (root / "kernel2").mkdir()
        self.assertEqual(mc.kernel_checks(root, V.H_LENS_KERNEL_V2, fake_cargo),
                         [("kernel rebuild hashes to H_LENS_KERNEL", True),
                          ("kernel2 rebuild hashes to H_LENS_KERNEL_V2", True), ("the released rules are rebuilt here", True)])
        built["kernel2"] = V.KERNEL2_ATOM + b"\x00"
        self.assertEqual(mc.kernel_checks(root, V.H_LENS_KERNEL, fake_cargo),
                         [("kernel rebuild hashes to H_LENS_KERNEL", True),
                          ("kernel2 rebuild hashes to H_LENS_KERNEL_V2", False), ("the released rules are rebuilt here", True)])
        # a commit carrying kernel/lens1b.wasm rebuilds it with the commit-bound feature, after hashing kernel/'s v1
        (root / "kernel" / "lens1b.wasm").write_bytes(V.KERNEL1B_ATOM)
        self.assertEqual(mc.kernel_checks(root, V.H_LENS_KERNEL_V1B, fake_cargo),
                         [("kernel rebuild hashes to H_LENS_KERNEL", True),
                          ("kernel2 rebuild hashes to H_LENS_KERNEL_V2", False),
                          ("kernel/lens1b.wasm rebuild hashes to H_LENS_KERNEL_V1B", True),
                          ("the released rules are rebuilt here", True)])
        built["commit-bound"] = V.KERNEL_ATOM
        self.assertFalse(mc.kernel_checks(root, V.H_LENS_KERNEL_V1B, fake_cargo)[-2][1])

    def test_59_a_counterexample_is_named_by_its_full_commit_id(self) -> None:
        """Review AMEND P1 on 2b82da8: the counterexample field must hold a full commit id, never a ref, an
        abbreviation, a revision expression or another object; a decision so pinned replays, fresh and warm, after
        the counterexample's ref moves on or is deleted."""
        cx, c1, s0 = self._rules_change_fixture()
        V2 = V.H_LENS_KERNEL_V2
        tree = subprocess.run(["git", "-C", str(self.repo_path), "rev-parse", f"{cx[0]}^{{tree}}"],
                              capture_output=True, text=True, check=True).stdout.strip()
        git = lambda *a: subprocess.run(["git", "-C", str(self.repo_path), *a], check=True)  # noqa: E731
        hex_refs = ("a" * 64, "b" * 40)  # hex-named refs: of the other length a ref, of the native length an id
        for h in hex_refs:
            git("update-ref", f"refs/heads/{h}", cx[0])
        git("-c", "user.name=t", "-c", "user.email=t@t", "tag", "-a", "-m", "an annotated tag", "cx-tag", cx[0])
        tag = subprocess.run(["git", "-C", str(self.repo_path), "rev-parse", "cx-tag"], capture_output=True, text=True,
                             check=True).stdout.strip()
        for name in ("refs/vars/heads/cx", cx[0][:12], f"{cx[0]}^{{commit}}", cx[0].upper(), "--all", tree, tag,
                     *hex_refs):
            attempt = self._change_rules("core", c1, s0, V2, [self.sk1], cx,
                                         override={"counterexample": lambda put, n=name: put(V.atom_utf8(n))})[0]
            # a native-length hex id of no object here names a commit this repository lacks: missing evidence, refused
            missing = name == "b" * 40
            with self.assertRaises(V.VarsError) as got:
                self.repo.admit_and_advance("core", attempt, expected_old=c1)
            self.assertEqual(type(got.exception), V.EvidenceMissing if missing else V.VarsError, str(got.exception))
            self.assertRegex(str(got.exception),
                             "is not in this repository" if missing else "counterexample is not a full commit id")
        cand, _, _ = self._change_rules("core", c1, s0, V2, [self.sk1], cx)
        self.repo.admit_and_advance("core", cand, expected_old=c1)
        # the counterexample's scope moves on with a cell that changes the rules' output there, and the hex-named refs
        # follow it; then the refs are deleted: the objects stay, the decision still replays
        before = self.repo.rules_output("cx", cx[0], V2)[0]
        a: dict[bytes, bytes] = {}
        late = self._axiom(a, "cx/later", "a later cell of the counterexample's scope")
        later = self.repo.build_candidate_commit("cx", a, [late], [V.Seal.sign(self.sk1, late.id, self.cx_s0.id)],
                                                 parent_commit=cx[0])
        self.repo.admit_and_advance("cx", later, expected_old=cx[0])
        self.assertNotEqual(self.repo.rules_output("cx", later, V2)[0], before, "the moved ref names other evidence")
        for h in hex_refs:
            git("update-ref", f"refs/heads/{h}", later)
        for moved in ("advanced", "deleted"):
            for gate in (self.repo, V.GitVarsRepo(self.repo_path)):
                try:
                    gate.check_chain("core", cand)
                except V.VarsError as e:
                    self.fail(f"after the counterexample's ref was {moved}, a {'warm' if gate is self.repo else 'fresh'} "
                              f"gate refuses the admitted rotation: {e}")
            for ref in ("refs/vars/heads/cx", *(f"refs/heads/{h}" for h in hex_refs)):
                git("update-ref", "-d", ref)

    def test_60_the_gate_names_commits_by_canonical_id(self) -> None:
        """Review round 2: the gate and the chain reader accept a commit only by its canonical id in this repository's
        object format. A candidate, a parent or a chain tip given as a ref, a hex-named ref or an abbreviation is
        refused, so what the gate checked is what the ref records."""
        c0, s0, _ = self._bootstrap_genesis("core")
        a: dict[bytes, bytes] = {}
        ax = self._axiom(a, "core/fact", "a fact")
        cand = self.repo.build_candidate_commit("core", a, [ax], [V.Seal.sign(self.sk1, ax.id, s0.id)], parent_commit=c0)
        git = lambda *a: subprocess.run(["git", "-C", str(self.repo_path), *a], check=True)  # noqa: E731
        for h in ("refs/heads/cand", "a" * 64):
            git("update-ref", h if h.startswith("refs/") else f"refs/heads/{h}", cand)
        for name in ("refs/heads/cand", "a" * 64, cand[:12], "refs/vars/heads/core"):
            with self.assertRaisesRegex(V.VarsError, "not the full commit id", msg=name):
                self.repo.commit_chain(name)
        for name in ("refs/heads/cand", "a" * 64, cand[:12]):
            self._gate_refuses("not the full commit id", "core", name, c0)
        git("update-ref", "refs/heads/old", c0)
        with self.assertRaisesRegex(V.VarsError, "not the full commit id"):
            self.repo.check_chain("core", "refs/heads/old")
        with self.assertRaisesRegex(V.VarsError, "not the full commit id"):
            self.repo.projection_digests("core", "refs/vars/heads/core")
        self.repo.admit_and_advance("core", cand, expected_old=c0)

    def test_61_release_checks_name_commits_by_canonical_id(self) -> None:
        """Review round 2: `checks_at` checks out a release commit, and extracts sibling pins, only by canonical ids of
        their own repositories (in a SHA-256 repository a 40-hex name may be a ref), and the spec's Book I pin is a full
        id, not the abbreviation a same-named ref would shadow."""
        mc = self._minds_chain()
        proj = Path(self.tmp.name) / "proj256"

        def repo(name):
            d = proj / name
            d.mkdir(parents=True)
            g = lambda *a: subprocess.run(["git", "-C", str(d), "-c", "user.name=t", "-c", "user.email=t@t", *a],
                                          capture_output=True, text=True, check=True).stdout.strip()
            g("init", "-q", "-b", "main", "--object-format=sha256")
            (d / "f").write_text(name)
            g("add", "f")
            g("commit", "-q", "-m", "one")
            return d, g

        minds, gm = repo("minds")
        m1 = gm("rev-parse", "HEAD")
        self.assertEqual(len(m1), 64)
        ref40 = "c" * 40
        gm("update-ref", f"refs/heads/{ref40}", m1)
        ran = []
        real, mc.run_checks = mc.run_checks, lambda root, rules: (ran.append(root), (["spy OK"], True))[1]
        try:
            with self.assertRaisesRegex(V.VarsError, "not a full commit id"):
                mc.checks_at(minds, ref40, V.H_LENS_KERNEL)
            self.assertEqual(ran, [], "no check ran at a commit named by a ref")
            sg, gs = repo("sigma-glyph")
            pr, gp = repo("primitives")
            gs("update-ref", f"refs/heads/{ref40}", gs("rev-parse", "HEAD"))
            with self.assertRaisesRegex(V.VarsError, "sigma-glyph pin .* not a full commit id"):
                mc.checks_at(minds, m1, V.H_LENS_KERNEL, {"sigma-glyph": ref40, "primitives": gp("rev-parse", "HEAD")})
            self.assertEqual(ran, [])
            pins = {"sigma-glyph": gs("rev-parse", "HEAD"), "primitives": gp("rev-parse", "HEAD")}
            with self.assertRaisesRegex(V.VarsError, "Book I pin"):  # the spec's pin is no commit of this sibling
                mc.checks_at(minds, m1, V.H_LENS_KERNEL, pins)
            self.assertEqual(ran, [])
            self.assertEqual(mc.checks_at(minds, m1, V.H_LENS_KERNEL), (["spy OK"], True))
        finally:
            mc.run_checks = real
        spec_pin = re.search(r"`sigma-glyph` at `([0-9a-f]+)`", (ROOT_DIR / "VARS-1-SPEC.md").read_text()).group(1)
        self.assertRegex(mc.SIGMA_PIN, r"^[0-9a-f]{40}$")
        self.assertTrue(mc.SIGMA_PIN.startswith(spec_pin))


    # -- classes of rules change (VARS-1-SPEC.md §4.3, AMENDMENTS.md) -------------------------------------------------
    BUDGET = 10_000_000

    def _fuzz_counterexample(self, commits: int = 84_000_000) -> bytes:
        """The fuzzer's counterexample, rebuilt (its artifact was not kept): a real v1 input, a scope with a fact,
        whose commit count says `commits`. Every other count is bounded by the input's length; this one is not."""
        if not hasattr(self, "_seed_input"):
            c0, s0, _ = self._bootstrap_genesis("seed")
            a: dict[bytes, bytes] = {}
            c1 = self._commit("seed", c0, s0, a, [self._axiom(a, "seed/fact", "a fact")])
            self._seed_input = V.kernel_facts("seed", self.repo.chain_deltas(self.repo.commit_chain(c1)))[0]
        inp = bytearray(self._seed_input)
        inp[0:4] = struct.pack("<I", commits)
        return bytes(inp)

    def _register_rules(self, h: bytes, rules: "V.Rules", atom: bytes) -> None:
        """A rules module as only this test's host implements it (a stand-in), restored after the test."""
        saved = [(d, d.get(h)) for d in (V.RULES, V.RULES_MODULES, V.RULES_ATOMS)]
        V.RULES[h], V.RULES_MODULES[h], V.RULES_ATOMS[h] = rules, rules.path, atom

        def restore() -> None:
            for d, old in saved:
                if old is None:
                    d.pop(h, None)
                else:
                    d[h] = old
        self.addCleanup(restore)

    def _equivalent_v1(self) -> bytes:
        """v1 with other bytes and the same behaviour: lens.wasm with a custom section appended."""
        raw = V.KERNEL_ATOM + b"\x00\x0b\x05minds" + b"same!"
        path = Path(self.tmp.name) / "lens-equivalent.wasm"
        path.write_bytes(raw)
        self._register_rules(V.sha256(raw), V.Rules(path, "v1"), raw)
        return V.sha256(raw)

    def _change(self, kind: str, scope: str, parent: str, base: V.Cell, new_rules: bytes, *, label: str,
                inp: bytes = b"", budget: int = BUDGET, refusal: int = 7, override: "dict | None" = None,
                rotate: bool = True, fields: "list[str] | None" = None) -> tuple[str, V.Cell, V.Cell]:
        """A candidate commit rotating `scope` to `new_rules` with a decision of class `kind` (not `correction`:
        see `_change_rules`), its digests the gate's own replay; `override` replaces fields by name."""
        a = dict(V.RULES_ATOMS)
        put = lambda raw: self._put_atom(a, raw)  # noqa: E731
        sch, sch_atoms = V.rules_change_schema(scope, kind)
        a.update(sch_atoms)
        all_fields = V.RULES_CHANGE_CLASSES[kind][1]
        if fields is not None:
            sch = V.Cell(V.H_META_SCHEMA, sch.h_slot_name, V.H_EMPTY, slots=tuple(put(V.atom_utf8(f)) for f in fields))
        old = base.slots[2]
        vals = {"old_rules": old, "new_rules": new_rules, "basis": put(V.atom_utf8(parent))}
        try:
            vals["reproduce"] = self.repo.rules_change_basis(scope, parent, old, new_rules)["reproduce"]
        except V.VarsError:
            vals["reproduce"] = bytes(32)
        if kind != "equivalent":
            vals.update(input=put(V.atom_kin1(inp)), budget=put(V.atom_u64(budget)), refusal=put(V.atom_u64(refusal)),
                        refutes=self.repo.rules_change_refusal(old, new_rules, inp, min(budget, V.MAX_RULES_BUDGET))["refutes"])
        for k, v in (override or {}).items():
            vals[k] = v(put) if callable(v) else v
        names = [f.split(":")[0] for f in (fields or all_fields)]
        d = V.Cell(sch.id, put(V.atom_utf8(f"{scope}/rules-change/{label}")),
                   put(V.atom_utf8(f"{scope} moves to rules {new_rules.hex()[:12]}: {kind}")),
                   slots=tuple(vals[n] for n in names))
        s = V.Cell(V.H_SCHEMA["scope"], put(V.atom_utf8(f"{scope}/SCOPE")), put(V.atom_utf8(f"{scope} under {label}")),
                   h_supersedes=self._hv(a, [base.id]), h_loss=put(V.atom_utf8(f"rules change to {label}")),
                   slots=(base.slots[0], base.slots[1], new_rules))
        cells = [d, sch] + ([s] if rotate else [])
        seals = [V.Seal.sign(self.sk1, x.id, base.id) for x in cells]
        return self.repo.build_candidate_commit(scope, a, cells, seals, parent_commit=parent), s, d

    def _core(self) -> tuple[str, V.Cell]:
        c0, s0, _ = self._bootstrap_genesis("core")
        a: dict[bytes, bytes] = {}
        return self._commit("core", c0, s0, a, [self._axiom(a, "core/fact", "a fact")]), s0

    def test_62_a_resource_hardening_bounds_the_commit_count(self) -> None:
        """The first amendment (ASSURANCE.md, found by fuzzing): v1 visits every commit an input claims, so a small
        input claiming 84 M commits runs unbounded; v1b refuses an input with more commits than bytes (E-7). The
        rotation v1 -> v1b is a resource hardening: on the fuzzer's input, under a budget of steps, v1 exhausts it
        and v1b refuses with its resource code; over the chain so far the two give the same output byte for byte."""
        inp = self._fuzz_counterexample()
        ev = self.repo.rules_change_refusal(V.H_LENS_KERNEL, V.H_LENS_KERNEL_V1B, inp, self.BUDGET)
        self.assertEqual((ev["old"].kind, ev["new"]), ("exhausted", V.RulesResult("refusal", code=-7)))
        honest = self._fuzz_counterexample(commits=2)  # its real count: both rules give the same output
        self.assertEqual(V.kernel_runner(V.H_LENS_KERNEL).run(honest), V.kernel_runner(V.H_LENS_KERNEL_V1B).run(honest))
        cx, _, _ = self._r2_03()
        v2_input = V.kernel_facts("cx", self.repo.chain_deltas(self.repo.commit_chain(cx[0])))[0]
        for rules, inputs in ((V.H_LENS_KERNEL, [honest, inp[:-1]]), (V.H_LENS_KERNEL_V1B, [honest, inp]),
                              (V.H_LENS_KERNEL_V2, [v2_input, v2_input[:-1]])):
            for x in inputs:
                try:
                    plain = V.RulesResult("output", output=V.kernel_runner(rules).run(x))
                except V.KernelRefusal as e:
                    plain = V.RulesResult("refusal", code=e.code)
                self.assertEqual(V.metered_runner(rules).run(x, self.BUDGET), plain, "metering changes no result")
        c1, s0 = self._core()
        cand, s1, d = self._change("hardening", "core", c1, s0, V.H_LENS_KERNEL_V1B, label="v1b", inp=inp)
        try:
            self.repo.admit_and_advance("core", cand, expected_old=c1)
        except V.VarsError as e:
            self.fail(f"the hardening v1 -> v1b was refused: {e}")
        a: dict[bytes, bytes] = {}
        self._commit("core", cand, s1, a, [self._axiom(a, "core/after", "after the hardening")])
        lens = self.repo.lens("core")
        self.assertEqual(lens["rules"], V.H_LENS_KERNEL_V1B)
        self.assertTrue(lens["active"][d.id] and lens["active"][s1.id])

    def test_63_the_bound_refuses_a_chain_of_empty_commits(self) -> None:
        """The gate admits a commit that adds nothing, so a chain can claim more commits than its input has bytes:
        v1 folds it, v1b refuses it (E-7), and the host's twin agrees with each (no TwinDivergence)."""
        for rules in (V.H_LENS_KERNEL, V.H_LENS_KERNEL_V1B):
            repo = V.GitVarsRepo(self.repo_path)
            a = {**V.STD_SCHEMA_ATOMS, rules: V.RULES_ATOMS[rules]}
            pol = self._pol(a, 1, [self.pk1])
            s0 = V.Cell(V.H_SCHEMA["scope"], self._put_atom(a, V.atom_utf8("e/SCOPE")), self._put_atom(a, V.atom_utf8("e")),
                        slots=(pol, pol, rules))
            c0 = repo.build_candidate_commit("e", a, [*V.STD_SCHEMAS.values(), s0], [V.Seal.sign(self.sk1, s0.id, s0.id)],
                                             parent_commit=None)
            n = len(V.kernel_facts("e", repo.chain_deltas([c0]))[0])
            tree = subprocess.run(["git", "-C", str(self.repo_path), "rev-parse", f"{c0}^{{tree}}"], capture_output=True,
                                  text=True, check=True).stdout.strip()
            script = "".join(f"commit refs/heads/empty\ncommitter t <t@t> 0 +0000\ndata 0\n"
                             f"{'from ' + c0 + chr(10) if i == 0 else ''}M 040000 {tree} \"\"\n\n" for i in range(n))
            subprocess.run(["git", "-C", str(self.repo_path), "fast-import", "--quiet", "--force"], input=script.encode(),
                           check=True)
            tip = subprocess.run(["git", "-C", str(self.repo_path), "rev-parse", "refs/heads/empty"], capture_output=True,
                                 text=True, check=True).stdout.strip()
            commits = repo.commit_chain(tip)
            self.assertEqual(len(commits), n + 1)
            if rules == V.H_LENS_KERNEL:
                repo._evaluate_commit_chain("e", commits)
                continue
            with self.assertRaisesRegex(V.VarsError, r"more commits than its rules input has bytes \[rules kernel E-7"):
                repo._evaluate_commit_chain("e", commits)
            repo._evaluate_commit_chain("e", commits[:-1])  # one commit fewer: within the bound

    def test_64_a_resource_hardening_needs_each_piece(self) -> None:
        """A hardening is refused when its reproduce or refutes digest is not the replay's, when the chain so far
        changes by a byte, when the new rules do not refuse the input with the named code within the budget, when
        that code is not a resource refusal of theirs, when the old rules finish within the budget, when the budget is
        over the gate's limit, when the input is no KIN1 atom, and across encodings."""
        inp = self._fuzz_counterexample()
        c1, s0 = self._core()
        V1B = V.H_LENS_KERNEL_V1B
        attempt = lambda **kw: self._change("hardening", "core", c1, s0, V1B, label="v1b", inp=inp, **kw)[0]  # noqa: E731
        self._gate_refuses(r"\(hardening\): the decision's reproduce digest", "core", attempt(override={"reproduce": bytes(32)}), c1)
        self._gate_refuses(r"\(hardening\): the decision's refutes digest", "core", attempt(override={"refutes": bytes(32)}), c1)
        self._gate_refuses(r"\(hardening\): the new rules do not refuse the input with E-8", "core", attempt(refusal=8), c1)
        self._gate_refuses(r"\(hardening\): the new rules do not refuse the input with E-7 within the budget \(they give "
                           r"exhausted\)", "core", attempt(budget=3), c1)
        self._gate_refuses("outside 0..", "core", attempt(budget=V.MAX_RULES_BUDGET + 1), c1)
        malformed = inp[:4] + struct.pack("<I", 1 << 30) + inp[8:]  # N over the input's length: both refuse E-1
        self._gate_refuses(r"\(hardening\): E-1 is not a resource refusal", "core",
                           self._change("hardening", "core", c1, s0, V1B, label="v1b", inp=malformed, refusal=1)[0], c1)
        over = self._fuzz_counterexample(commits=len(inp) + 1)  # just over the bound: v1 finishes at once
        self._gate_refuses(r"\(hardening\): the old rules give output within the budget, so there is nothing to harden",
                           "core", self._change("hardening", "core", c1, s0, V1B, label="v1b", inp=over)[0], c1)
        V.validate_atom(V.atom_kin1(bytes(V.MAX_KIN1_BYTES)))  # at most 1 MiB: the bound itself is admitted
        with self.assertRaisesRegex(V.VarsError, "KIN1 rules input over 1 MiB"):
            V.validate_atom(V.atom_kin1(bytes(V.MAX_KIN1_BYTES + 1)))
        self._gate_refuses("is not a kin1 atom", "core",
                           attempt(override={"input": lambda put: put(V.atom_utf8("not an input"))}), c1)
        self._gate_refuses("a hardening change keeps the input encoding", "core",
                           self._change("hardening", "core", c1, s0, V.H_LENS_KERNEL_V2, label="v2", inp=inp)[0], c1)
        real = self.repo.rules_output

        def one_byte_more(scope, tip, rules):
            out, read = real(scope, tip, rules)
            return (out + b"\x00" if rules == V1B else out), read

        self.repo.rules_output = one_byte_more
        try:
            self._gate_refuses(r"\(hardening\): the new rules do not give the old rules' output over the chain so far, "
                               "byte for byte", "core", attempt(), c1)
        finally:
            del self.repo.rules_output
        need = "exactly one rules-change decision"
        for drop in ("input", "budget", "refusal", "refutes", "reproduce"):
            fields = [f for f in V.REFUSAL_CHANGE_FIELDS if f.split(":")[0] != drop]
            self._gate_refuses(need, "core", attempt(fields=fields), c1)
        self._gate_refuses("comes only with the rotation", "core", attempt(rotate=False), c1)
        self.repo.admit_and_advance("core", attempt(), expected_old=c1)

    def test_65_a_validation_tightening(self) -> None:
        """A tightening: the new rules refuse, with a refusal that is not a resource one, an input the old rules
        give an output for. A stand-in host reads v1b's E-7 as no resource refusal; then the input just over the
        bound is a tightening, the fuzzer's input is none (v1 exhausts the budget there), and real v1b is refused as
        a tightening (E-7 is its resource refusal: that is a hardening)."""
        over = self._fuzz_counterexample(commits=len(self._fuzz_counterexample()) + 1)
        c1, s0 = self._core()
        V1B = V.H_LENS_KERNEL_V1B
        self._gate_refuses(r"\(tightening\): E-7 is a resource refusal: that is a hardening", "core",
                           self._change("tightening", "core", c1, s0, V1B, label="t", inp=over)[0], c1)
        self._register_rules(V1B, V.Rules(V.RULES[V1B].path, "v1"), V.KERNEL1B_ATOM)
        self._gate_refuses(r"\(tightening\): the old rules give exhausted, not an output", "core",
                           self._change("tightening", "core", c1, s0, V1B, label="t", inp=self._fuzz_counterexample())[0], c1)
        self.repo.admit_and_advance("core", self._change("tightening", "core", c1, s0, V1B, label="t", inp=over)[0],
                                    expected_old=c1)

    def test_66_an_implementation_equivalent_change(self) -> None:
        """Other bytes, the same output over the chain so far byte for byte, no counterexample: admitted. Refused
        with another reproduce digest, an output differing by a byte, or across encodings."""
        c1, s0 = self._core()
        eq = self._equivalent_v1()
        self.assertNotEqual(eq, V.H_LENS_KERNEL)
        attempt = lambda **kw: self._change("equivalent", "core", c1, s0, eq, label="eq", **kw)[0]  # noqa: E731
        self._gate_refuses(r"\(equivalent\): the decision's reproduce digest", "core", attempt(override={"reproduce": bytes(32)}), c1)
        self._gate_refuses("an equivalent change keeps the input encoding", "core",
                           self._change("equivalent", "core", c1, s0, V.H_LENS_KERNEL_V2, label="v2")[0], c1)
        real = self.repo.rules_output

        def one_byte_more(scope, tip, rules):
            out, read = real(scope, tip, rules)
            return (out + b"\x00" if rules == eq else out), read

        self.repo.rules_output = one_byte_more
        try:
            self._gate_refuses(r"\(equivalent\): the new rules do not give the old rules' output", "core", attempt(), c1)
        finally:
            del self.repo.rules_output
        cand = attempt()
        self.repo.admit_and_advance("core", cand, expected_old=c1)
        self.assertEqual(V.GitVarsRepo(self.repo_path).rules_output("core", cand, eq)[0],
                         V.GitVarsRepo(self.repo_path).rules_output("core", cand, V.H_LENS_KERNEL)[0])

    def test_67_earlier_counterexamples_stay_decided(self) -> None:
        """(d): a later rules change must keep every earlier one. After the hardening v1 -> v1b, an "equivalent"
        change back to v1 (the same output over the chain) is refused: v1 exhausts the budget on the hardening's input
        again; v1b -> v2 is refused before (d) (test 68), and (d) alone refuses it too: v2 cannot read that input. After the correction v1 -> v2, an equivalent
        v2' is admitted only while it still gives the correction's counterexample its verdict."""
        inp = self._fuzz_counterexample()
        cx, c1b, t0 = self._rules_change_fixture_on("q")
        c1, s0 = self._core()
        cand, s1, _ = self._change("hardening", "core", c1, s0, V.H_LENS_KERNEL_V1B, label="v1b", inp=inp)
        self.repo.admit_and_advance("core", cand, expected_old=c1)
        self._gate_refuses(r"\(d\): the earlier rules change [0-9a-f]{12} is undone: the new rules no longer refuse its "
                           "input with E-7", "core",
                           self._change("equivalent", "core", cand, s1, V.H_LENS_KERNEL, label="back")[0], cand)
        # v1b -> v2 is refused before (d) (test 68: v2 reads v1b-born cells by type); (d) would refuse it too, since v2
        # cannot read the hardening's v1-encoded input
        self._gate_refuses("v2 reads as v1 only the cells born under H_LENS_KERNEL", "core",
                           self._change_rules("core", cand, s1, V.H_LENS_KERNEL_V2, [self.sk1], cx)[0], cand)
        with self.assertRaisesRegex(V.VarsError, r"\(d\): the earlier rules change [0-9a-f]{12}: its input is encoded for "
                                                 "other rules"):
            self.repo._check_earlier_changes("core", self.repo.commit_chain(cand), V.H_LENS_KERNEL_V2, b"")

        cand2, t1, _ = self._change_rules("q", c1b, t0, V.H_LENS_KERNEL_V2, [self.sk1], cx)
        self.repo.admit_and_advance("q", cand2, expected_old=c1b)
        v2b = V.KERNEL2_ATOM + b"\x00\x0b\x05minds" + b"same!"
        path = Path(self.tmp.name) / "lens2-equivalent.wasm"
        path.write_bytes(v2b)
        h2 = V.sha256(v2b)
        self._register_rules(h2, V.Rules(path, "v2"), v2b)
        real = self.repo.rules_output
        x = real("cx", cx[0], V.H_LENS_KERNEL_V2)[1]["order"][cx[1]]

        def gives_the_old_verdict(scope, tip, rules):
            out, read = real(scope, tip, rules)
            if scope == "cx" and rules == h2:
                read = {**read, "status": {**read["status"], x: read["status"][x] | 1}}
            return out, read

        self.repo.rules_output = gives_the_old_verdict
        try:
            self._gate_refuses(r"\(d\): the earlier rules change [0-9a-f]{12} is undone: the new rules no longer give its "
                               "counterexample's verdict", "q", self._change("equivalent", "q", cand2, t1, h2, label="v2b")[0],
                               cand2)
        finally:
            del self.repo.rules_output
        self.repo.admit_and_advance("q", self._change("equivalent", "q", cand2, t1, h2, label="v2b")[0], expected_old=cand2)

    def _rules_change_fixture_on(self, scope: str) -> tuple[tuple[str, int], str, V.Cell]:
        cx, _, _ = self._r2_03()
        c0, s0, _ = self._bootstrap_genesis(scope)
        a: dict[bytes, bytes] = {}
        return cx, self._commit(scope, c0, s0, a, [self._axiom(a, f"{scope}/fact", "a fact")]), s0

    def test_68_no_rotation_from_v2_to_rules_that_read_as_v1(self) -> None:
        """v1b reads references as v1 does, so it cannot read a v2 epoch: v2 -> v1b is refused, whatever the class
        (the v2 kernel's E-25 covers only v1 itself); and v1b -> v2 is refused, since v2 reads as v1 only the cells
        born under H_LENS_KERNEL."""
        cx, c1, s0 = self._rules_change_fixture()
        cand, s1, _ = self._change_rules("core", c1, s0, V.H_LENS_KERNEL_V2, [self.sk1], cx)
        self.repo.admit_and_advance("core", cand, expected_old=c1)
        self._gate_refuses("cannot read a v2 epoch", "core",
                           self._change("hardening", "core", cand, s1, V.H_LENS_KERNEL_V1B, label="v1b",
                                        inp=self._fuzz_counterexample())[0], cand)
        # Codex review r1 F1: nor the other way. v2 reads as v1 only cells born under H_LENS_KERNEL, so a v1b-born
        # digest would stop carrying acceptance; a chain with a v1b epoch (here its genesis) does not rotate to v2
        a = {**V.STD_SCHEMA_ATOMS, V.H_LENS_KERNEL_V1B: V.KERNEL1B_ATOM}
        pol = self._pol(a, 1, [self.pk1])
        b0 = V.Cell(V.H_SCHEMA["scope"], self._put_atom(a, V.atom_utf8("b/SCOPE")), self._put_atom(a, V.atom_utf8("b")),
                    slots=(pol, pol, V.H_LENS_KERNEL_V1B))
        g = self.repo.build_candidate_commit("b", a, [*V.STD_SCHEMAS.values(), b0], [V.Seal.sign(self.sk1, b0.id, b0.id)],
                                             parent_commit=None)
        self.repo.admit_and_advance("b", g, expected_old=None)
        self._gate_refuses("v2 reads as v1 only the cells born under H_LENS_KERNEL", "b",
                           self._change_rules("b", g, b0, V.H_LENS_KERNEL_V2, [self.sk1], cx)[0], g)


    def test_69_a_fresh_clone_replays_a_past_rules_change(self) -> None:
        """Codex §4.5: a counterexample named by commit id is no edge Git follows. The gate writes
        refs/vars/evidence/<scope>/<decision> with the rotation, in one transaction; a fresh clone that fetches only
        refs/vars/heads/core and refs/vars/evidence/* replays the change after the author's helper refs are deleted;
        without the evidence ref, after gc, the replay reports missing evidence, which is not a refutation. The
        evidence manifest names each change's needs; a hardening's input travels in the chain itself."""
        mc = self._minds_chain()
        cx, c1, s0 = self._rules_change_fixture()
        cand, s1, d = self._change_rules("core", c1, s0, V.H_LENS_KERNEL_V2, [self.sk1], cx)
        self.repo.admit_and_advance("core", cand, expected_old=c1)
        ref = f"refs/vars/evidence/core/{d.id.hex()}/{cx[0]}"
        git = lambda repo, *a: subprocess.run(["git", "-C", str(repo), *a], capture_output=True, text=True,  # noqa: E731
                                              check=True).stdout.strip()
        got = subprocess.run(["git", "-C", str(self.repo_path), "rev-parse", "--verify", "--quiet", ref], capture_output=True,
                             text=True).stdout.strip()
        self.assertEqual(got, cx[0], "the rotation wrote the evidence ref")
        man = mc.evidence(self.repo_path, "core")
        self.assertEqual([(c["decision"], c["class"], c["counterexample"], c["needs"]) for c in man["changes"]],
                         [(d.id.hex(), "correction", {"scope": "cx", "commit": cx[0]},
                           [{"scope": "cx", "commit": cx[0], "ref": ref}])])
        self.assertEqual(man["changes"][0]["in_chain"], sorted([V.H_LENS_KERNEL.hex(), V.H_LENS_KERNEL_V2.hex()]))
        git(self.repo_path, "update-ref", "-d", "refs/vars/heads/cx")  # the author's helper ref
        git(self.repo_path, "reflog", "expire", "--expire=now", "--all")
        git(self.repo_path, "gc", "--quiet", "--prune=now")

        fresh = Path(self.tmp.name) / "fresh"
        git(Path(self.tmp.name), "init", "-q", str(fresh))
        git(fresh, "fetch", "-q", "--no-tags", str(self.repo_path),
            "refs/vars/heads/core:refs/vars/heads/core", "+refs/vars/evidence/*:refs/vars/evidence/*")
        self.assertEqual(git(fresh, "for-each-ref", "--format=%(refname)").split(), sorted([ref, "refs/vars/heads/core"]))
        self.assertEqual(mc.evidence(fresh, "core"), man)
        self.assertEqual(mc.replay_changes(fresh, "core"), [(d.id.hex(), "REPLAYED")])
        V.GitVarsRepo(fresh).check_chain("core", cand)

        git(fresh, "update-ref", "-d", ref)
        git(fresh, "reflog", "expire", "--expire=now", "--all")
        git(fresh, "gc", "--quiet", "--prune=now")
        self._missing(f"counterexample {cx[0]} is not in this repository", fresh, cand)
        (dec, result), = mc.replay_changes(fresh, "core")
        self.assertTrue(result.startswith("EVIDENCE MISSING:"), result)
        # the counterexample commit is here but not all its history: a shallow fetch, or a lost object
        git(fresh, "fetch", "-q", "--no-tags", "--depth=1", str(self.repo_path), f"+{ref}:{ref}")
        self.assertEqual(git(fresh, "rev-parse", "--is-shallow-repository"), "true")
        self._missing("with its history", fresh, cand)
        loose = Path(self.tmp.name) / "loose"
        git(Path(self.tmp.name), "init", "-q", str(loose))
        git(loose, "-c", "fetch.unpackLimit=1000000", "fetch", "-q", "--no-tags", str(self.repo_path),
            "refs/vars/heads/core:refs/vars/heads/core", f"+{ref}:{ref}")
        cx_genesis = git(loose, "rev-list", "--max-parents=0", cx[0])
        (loose / ".git" / "objects" / cx_genesis[:2] / cx_genesis[2:]).unlink()
        self._missing("with its history", loose, cand)

        # a hardening needs no ref: its input is a KIN1 atom of the rotation commit
        inp = self._fuzz_counterexample()
        h0, t0, _ = self._bootstrap_genesis("h")
        hc, _, hd = self._change("hardening", "h", h0, t0, V.H_LENS_KERNEL_V1B, label="v1b", inp=inp)
        self.repo.admit_and_advance("h", hc, expected_old=h0)
        item, = mc.evidence(self.repo_path, "h")["changes"]
        self.assertEqual(item["input"], {"atom": V.sha256(V.atom_kin1(inp)).hex(), "bytes": len(inp)})
        fresh_h = Path(self.tmp.name) / "fresh-h"
        git(Path(self.tmp.name), "init", "-q", str(fresh_h))
        git(fresh_h, "fetch", "-q", "--no-tags", str(self.repo_path), "refs/vars/heads/h:refs/vars/heads/h")
        self.assertEqual(mc.replay_changes(fresh_h, "h"), [(hd.id.hex(), "REPLAYED")])

    def _missing(self, regex: str, repo: Path, tip: str) -> None:
        """Replaying the chain up to `tip` in `repo` reports missing evidence, not a refusal of what it replays."""
        try:
            V.GitVarsRepo(repo).check_chain("core", tip)
        except V.VarsError as e:
            self.assertIsInstance(e, V.EvidenceMissing, f"missing evidence reported as a refusal: {e}")
            self.assertRegex(str(e), regex)
        else:
            self.fail("the replay ran without its evidence")

    def test_70_a_rotation_is_recorded_only_after_its_shadow_replay(self) -> None:
        """tools/minds_chain.py: `shadow` replays every historical tip under its epoch's rules and the new rules and
        lists every difference (commit, cell, bit, old, new); `change-rules` records a rotation only with a manifest
        equal to that replay now, refuses a hardening or an equivalent change whose manifest lists a difference, and
        records one that changes history only with --accept <digest>. v1 -> v1b leaves the release chain as it was."""
        mc = self._minds_chain()
        sk = b"\x07" * 32
        mc.init(self.repo_path, sk)
        mc.release(self.repo_path, sk, "a" * 40, ["x OK"])
        mc.release(self.repo_path, sk, "b" * 40, ["x OK"])
        repo = V.GitVarsRepo(self.repo_path)
        tips = repo.commit_chain(repo.ref_commit("minds"))
        man = mc.shadow(self.repo_path, V.H_LENS_KERNEL_V1B)
        self.assertEqual((man["tips"], man["differences"]), (len(tips), []))
        self.assertEqual(mc.shadow(self.repo_path, V.H_LENS_KERNEL_V2)["differences"], [])
        real = repo.rules_output.__func__
        flip_at = tips[1]
        fake = {}

        def flips(self_, scope, tip, rules):
            out, read = real(self_, scope, tip, rules)
            if tip == flip_at and rules == fake.get("rules"):
                cid = sorted(read["status"])[0]
                read = {**read, "status": {**read["status"], cid: read["status"][cid] ^ 0x08}}
                fake["cell"] = cid
            return out, read

        inp = self._fuzz_counterexample()
        kw = {"input": inp, "budget": self.BUDGET, "refusal": 7}
        V.GitVarsRepo.rules_output = flips
        try:
            fake["rules"] = V.H_LENS_KERNEL_V1B
            bad = mc.shadow(self.repo_path, V.H_LENS_KERNEL_V1B)
            self.assertEqual(bad["differences"], [{"commit": flip_at, "cell": fake["cell"].hex(), "bit": "retired",
                                                   "old": 0, "new": 1}])
            with self.assertRaisesRegex(V.VarsError, "a hardening change must leave every historical tip"):
                mc.change_rules(self.repo_path, sk, "hardening", V.H_LENS_KERNEL_V1B, bad, **kw)
            fake["rules"] = None
        finally:
            V.GitVarsRepo.rules_output = real
        # a change of history: a correction (or a tightening) is recorded only with the manifest's digest named;
        # an equivalent change never
        cx, _, _ = self._r2_03()
        eq = self._equivalent_v1()
        cxkw = {"counterexample_scope": "cx", "counterexample": cx[0], "cell": cx[1], "status": 0, "right": 0}
        V.GitVarsRepo.rules_output = flips
        try:
            fake["rules"] = eq
            with self.assertRaisesRegex(V.VarsError, "an equivalent change must leave every historical tip"):
                mc.change_rules(self.repo_path, sk, "equivalent", eq, mc.shadow(self.repo_path, eq))
            fake["rules"] = V.H_LENS_KERNEL_V2
            diff = mc.shadow(self.repo_path, V.H_LENS_KERNEL_V2)
            self.assertEqual(len(diff["differences"]), 1)
            for accept in (None, "0" * 64):
                with self.assertRaisesRegex(V.VarsError, "record the change only with --accept <its digest>"):
                    mc.change_rules(self.repo_path, sk, "correction", V.H_LENS_KERNEL_V2, diff, accept, **cxkw)
            self.assertEqual(repo.ref_commit("minds"), tips[-1], "nothing was recorded")
            accepted = Path(self.tmp.name) / "accepted"
            subprocess.run(["git", "clone", "-q", "--mirror", str(self.repo_path), str(accepted)], check=True)
            subprocess.run(["git", "-C", str(accepted), "fetch", "-q", str(self.repo_path), "+refs/vars/*:refs/vars/*"],
                           check=True)
            try:
                mc.change_rules(accepted, sk, "correction", V.H_LENS_KERNEL_V2, mc.shadow(accepted, V.H_LENS_KERNEL_V2),
                                diff["digest"], **cxkw)
            except V.VarsError as e:
                self.fail(f"a correction with its shadow digest accepted was refused: {e}")
            fake["rules"] = None
        finally:
            V.GitVarsRepo.rules_output = real
        # Codex review r2 F2: a writer between the shadow replay and the rotation; the rotation is pinned to the
        # manifest's tip and refused
        shadow_now = mc.shadow

        def then_a_writer(repo_dir, new_rules, scope="minds"):
            got = shadow_now(repo_dir, new_rules, scope)
            w = V.GitVarsRepo(repo_dir)
            tip = w.ref_commit("minds")
            a: dict[bytes, bytes] = {}
            ax = self._axiom(a, "minds/interloper", "written after the shadow replay")
            c = w.build_candidate_commit("minds", a, [ax], [V.Seal.sign(sk, ax.id, mc.governing_scope(w))], parent_commit=tip)
            w.admit_and_advance("minds", c, expected_old=tip)
            return got

        mc.shadow = then_a_writer
        try:
            raced = mc.shadow(self.repo_path, V.H_LENS_KERNEL_V1B)
        finally:
            mc.shadow = shadow_now
        with self.assertRaisesRegex(V.VarsError, "the chain moved after its shadow replay|is not this chain's replay"):
            mc.change_rules(self.repo_path, sk, "hardening", V.H_LENS_KERNEL_V1B, raced, **kw)
        real_shadow, mc.shadow = mc.shadow, lambda repo_dir, new_rules, scope="minds": raced  # validation passes ...
        try:
            with self.assertRaisesRegex(V.VarsError, "the chain moved after its shadow replay"):  # ... the pin does not
                mc.change_rules(self.repo_path, sk, "hardening", V.H_LENS_KERNEL_V1B, raced, **kw)
        finally:
            mc.shadow = real_shadow
        tips = repo.commit_chain(repo.ref_commit("minds"))
        man = mc.shadow(self.repo_path, V.H_LENS_KERNEL_V1B)
        tampered = {**man, "tips": man["tips"] - 1}
        with self.assertRaisesRegex(V.VarsError, "is not this chain's replay"):
            mc.change_rules(self.repo_path, sk, "hardening", V.H_LENS_KERNEL_V1B, tampered, **kw)
        with self.assertRaisesRegex(V.VarsError, "is not this chain's replay"):  # a manifest of other rules
            mc.change_rules(self.repo_path, sk, "hardening", V.H_LENS_KERNEL_V1B,
                            {**mc.shadow(self.repo_path, V.H_LENS_KERNEL_V2), "new_rules": V.H_LENS_KERNEL_V1B.hex()}, **kw)
        self.assertEqual(repo.ref_commit("minds"), tips[-1], "nothing was recorded")
        mc.change_rules(self.repo_path, sk, "hardening", V.H_LENS_KERNEL_V1B, man, **kw)
        self.assertEqual(mc.governing_rules(V.GitVarsRepo(self.repo_path)), V.H_LENS_KERNEL_V1B)
        _, r3 = mc.release(self.repo_path, sk, "c" * 40, ["x OK"])
        self.assertEqual(mc.replay_changes(self.repo_path), [(mc.evidence(self.repo_path)["changes"][0]["decision"],
                                                              "REPLAYED")])


    def test_71_a_trap_is_a_fault_not_exhaustion(self) -> None:
        """Codex review r1 F3: a module that traps gives a fault while steps are left and exhaustion when none are;
        neither is read as the other. A hardening whose old rules trap on the input is admitted (a crash made a
        controlled refusal; the trap at the gate is a stand-in, r2 F5)."""
        def sec(sid: int, body: bytes) -> bytes:
            return bytes([sid, len(body)]) + body
        # types: ()->(), (i32)->i32, (i32,i32)->i32; reset, alloc (1024), run (unreachable); one mutable global
        trap = (b"\x00asm\x01\x00\x00\x00"
                + sec(1, b"\x03\x60\x00\x00\x60\x01\x7f\x01\x7f\x60\x02\x7f\x7f\x01\x7f")
                + sec(3, b"\x03\x00\x01\x02") + sec(5, b"\x01\x00\x01") + sec(6, b"\x01\x7f\x01\x41\x00\x0b")
                + sec(7, b"\x04\x06memory\x02\x00\x05reset\x00\x00\x05alloc\x00\x01\x03run\x00\x02")
                + sec(10, b"\x03\x02\x00\x0b\x05\x00\x41\x80\x08\x0b\x03\x00\x00\x0b"))
        path = Path(self.tmp.name) / "trap.wasm"
        path.write_bytes(trap)
        h = V.sha256(trap)
        self._register_rules(h, V.Rules(path, "v1"), trap)
        self.assertEqual(V.metered_runner(h).run(b"any input", self.BUDGET), V.RulesResult("fault"))
        self.assertEqual(V.metered_runner(h).run(b"any input", 0), V.RulesResult("exhausted"))
        self.assertEqual(V.metered_runner(h).run(b"any input", self.BUDGET), V.RulesResult("fault"), "and again")
        inp = self._fuzz_counterexample()
        ev = self.repo.rules_change_refusal(h, V.H_LENS_KERNEL_V1B, inp, self.BUDGET)
        self.assertEqual((ev["old"], ev["new"]), (V.RulesResult("fault"), V.RulesResult("refusal", code=-7)))
        # the gate: a module that traps on everything cannot reproduce a chain, so a stand-in gives v1's old result on
        # the fuzzer's input as a fault (the old rules crash there), real v1b's new one: the hardening is admitted
        real = self.repo.rules_change_refusal

        def old_traps(old, new, kernel_input, budget):
            got = real(old, new, kernel_input, budget)
            o = V.RulesResult("fault")
            return {**got, "old": o, "refutes": V.sha256(V.sha256(o.encode()) + V.sha256(got["new"].encode()))}

        self.repo.rules_change_refusal = old_traps
        try:
            c1, s0 = self._core()
            cand = self._change("hardening", "core", c1, s0, V.H_LENS_KERNEL_V1B, label="v1b", inp=inp)[0]
            try:
                self.repo.admit_and_advance("core", cand, expected_old=c1)
            except V.VarsError as e:
                self.fail(f"a hardening whose old rules trap was refused: {e}")
        finally:
            del self.repo.rules_change_refusal

    def _r2_03_on(self, scope: str, parent: str, base: V.Cell) -> tuple[str, V.Cell]:
        """Codex R2-03 appended to `scope`'s chain in a v2 epoch: an accepted foreign cell Y holds as a `digest` the id
        of a cell X born after it. Returns the tip and X."""
        b: dict[bytes, bytes] = {}
        put = lambda raw: self._put_atom(b, raw)  # noqa: E731
        ppol = self._pol(b, 1, [self.pk_peer])
        sp = V.Cell(V.H_SCHEMA["scope"], put(V.atom_utf8("peerB/SCOPE")), put(V.atom_utf8("peerB")),
                    slots=(ppol, ppol, V.H_LENS_KERNEL))
        opaque = V.Cell(V.H_META_SCHEMA, put(V.atom_utf8(f"{scope}/opaque")), V.H_EMPTY,
                        slots=(put(V.atom_utf8("value:digest")),))
        xa: dict[bytes, bytes] = {}
        x = self._axiom(xa, "peerB/x", "born after the digest that names it")
        y = V.Cell(opaque.id, put(V.atom_utf8("peerB/y")), put(V.atom_utf8("y")), slots=(x.id,))
        acc = V.Cell(V.H_SCHEMA["acceptance"], put(V.atom_utf8(f"{scope}/accept.y")), y.id,
                     slots=(put(V.atom_utf8("peerB")), sp.id))
        c1 = self.repo.build_candidate_commit(scope, b, [sp, opaque, y, acc], [
            V.Seal.sign(self.sk_peer, sp.id, sp.id), V.Seal.sign(self.sk1, opaque.id, base.id),
            V.Seal.sign(self.sk_peer, y.id, sp.id), V.Seal.sign(self.sk1, acc.id, base.id)], parent_commit=parent)
        self.repo.admit_and_advance(scope, c1, expected_old=parent)
        c2 = self.repo.build_candidate_commit(scope, xa, [x], [V.Seal.sign(self.sk_peer, x.id, sp.id)], parent_commit=c1)
        self.repo.admit_and_advance(scope, c2, expected_old=c1)
        return c2, x

    def test_72_nested_evidence_travels(self) -> None:
        """Codex review r1 F2: a counterexample chain may carry its own correction, whose counterexample its replay
        needs. The gate writes evidence refs for the whole closure, so a fresh clone that fetched only the scope's
        ref and refs/vars/evidence/* replays the change after every helper ref is deleted and gc'd."""
        mc = self._minds_chain()
        leaf, _, _ = self._r2_03()
        q0, t0, _ = self._bootstrap_genesis("q", acc_threshold=1)
        qr, t1, _ = self._change_rules("q", q0, t0, V.H_LENS_KERNEL_V2, [self.sk1], leaf)
        self.repo.admit_and_advance("q", qr, expected_old=q0)
        qt, x = self._r2_03_on("q", qr, t1)
        order = self.repo.rules_output("q", qt, V.H_LENS_KERNEL_V2)[1]["order"]
        c1, s0 = self._core()
        cand, _, d = self._change_rules("core", c1, s0, V.H_LENS_KERNEL_V2, [self.sk1], (qt, order.index(x.id)),
                                        cx_scope="q")
        self.repo.admit_and_advance("core", cand, expected_old=c1)
        git = lambda repo, *a: subprocess.run(["git", "-C", str(repo), *a], capture_output=True, text=True,  # noqa: E731
                                              check=True).stdout.strip()
        refs = sorted(git(self.repo_path, "for-each-ref", "--format=%(refname)", f"refs/vars/evidence/core/{d.id.hex()}").split())
        self.assertEqual(refs, sorted(f"refs/vars/evidence/core/{d.id.hex()}/{c}" for c in (qt, leaf[0])),
                         "the counterexample and the one its own correction names")
        item, = mc.evidence(self.repo_path, "core")["changes"]
        self.assertEqual([(n["scope"], n["commit"]) for n in item["needs"]], [("q", qt), ("cx", leaf[0])])
        for ref in git(self.repo_path, "for-each-ref", "--format=%(refname)").split():
            if ref != "refs/vars/heads/core" and not ref.startswith("refs/vars/evidence/core/"):
                git(self.repo_path, "update-ref", "-d", ref)  # every helper: other heads, q's own evidence refs
        git(self.repo_path, "reflog", "expire", "--expire=now", "--all")
        git(self.repo_path, "gc", "--quiet", "--prune=now")
        fresh = Path(self.tmp.name) / "fresh-nested"
        git(Path(self.tmp.name), "init", "-q", str(fresh))
        git(fresh, "fetch", "-q", "--no-tags", str(self.repo_path),
            "refs/vars/heads/core:refs/vars/heads/core", "+refs/vars/evidence/*:refs/vars/evidence/*")
        self.assertEqual(mc.replay_changes(fresh, "core"), [(d.id.hex(), "REPLAYED")])


    def test_73_change_rules_returns_to_earlier_rules(self) -> None:
        """Codex review r2 F1: each rotation's decision is named by its basis, so `change-rules` can return to rules
        the chain used before (v1 -> v1' -> v1 -> v1', all equivalent), and a fresh gate replays the chain."""
        mc = self._minds_chain()
        sk = b"\x07" * 32
        mc.init(self.repo_path, sk)
        mc.release(self.repo_path, sk, "a" * 40, ["x OK"])
        eq = self._equivalent_v1()
        for rules in (eq, V.H_LENS_KERNEL, eq):
            try:
                mc.change_rules(self.repo_path, sk, "equivalent", rules, mc.shadow(self.repo_path, rules))
            except V.VarsError as e:
                self.fail(f"the equivalent rotation to {rules.hex()[:12]} was refused: {e}")
            self.assertEqual(mc.governing_rules(V.GitVarsRepo(self.repo_path)), rules)
        V.GitVarsRepo(self.repo_path).check_chain("minds", V.GitVarsRepo(self.repo_path).ref_commit("minds"))
        self.assertEqual([r for _, r in mc.replay_changes(self.repo_path)], ["REPLAYED"] * 3)


    def test_74_a_metered_run_does_not_depend_on_earlier_runs(self) -> None:
        """Second review of PR #2, P1: an exhausted or trapping run aborts mid-function, so a reused instance keeps
        whatever it changed (its stack pointer among them); after enough aborts an honest input gave a fault, and a
        gate in the same process refused an admitted hardening. Every metered run now starts from a fresh instance:
        after aborts at many points, on every rules module, a run equals the first, and the admitted rotation replays
        in the same process."""
        inp = self._fuzz_counterexample()
        honest = self._fuzz_counterexample(commits=2)
        c1, s0 = self._core()
        cand = self._change("hardening", "core", c1, s0, V.H_LENS_KERNEL_V1B, label="v1b", inp=inp)[0]
        self.repo.admit_and_advance("core", cand, expected_old=c1)
        cx, _, _ = self._r2_03()
        v2_input = V.kernel_facts("cx", self.repo.chain_deltas(self.repo.commit_chain(cx[0])))[0]
        for rules, x in ((V.H_LENS_KERNEL, honest), (V.H_LENS_KERNEL_V1B, honest), (V.H_LENS_KERNEL_V2, v2_input)):
            runner = V.metered_runner(rules)
            first = runner.run(x, self.BUDGET)
            self.assertEqual(first.kind, "output")
            for i in range(1500):
                self.assertEqual(runner.run(x, 32 + i % 97).kind, "exhausted")
            self.assertEqual(runner.run(x, self.BUDGET), first, f"{rules.hex()[:12]}: a run after 1500 aborts differs")
        try:
            V.GitVarsRepo(self.repo_path).check_chain("core", cand)
        except V.VarsError as e:
            self.fail(f"after aborted runs, a gate in the same process refuses the admitted hardening: {e}")

    def _cycle_fixture(self, atoms: dict[bytes, bytes]) -> tuple[bytes, V.Cell, bytes]:
        """`M M` under the rich profile (`ski+Y+M+W`): the input thunk is forced (3 ATP), then `M M -> M M` costs 2
        and returns to the same state. Returns the computation id, its computation cell and the entry state id."""
        app = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=SR.M_H, right=SR.M_H)
        h_app = self._put_atom(atoms, app)
        h_env = self._put_atom(atoms, V.atom_environment([h_app]))
        comp_id = self._put_atom(atoms, V.atom_computation_root(h_app, h_env, SR.RICH_RUNTIME_ID,
                                                                SR.RICH_COST_MODEL_ID))
        env = SR.Environment([h_app], {h_app: app})
        doc, i, sb = SR.start(comp_id.hex(), h_app)
        entry = SR.advance(doc, i, sb, env, 3, runtime=SR.RICH_RUNTIME_ID)
        self.assertEqual((entry.outcome, entry.checkpoint["spent_total"]), (SR.PAUSED, 3))
        comp = V.Cell(h_schema=V.H_SCHEMA["computation"], h_slot_name=self._put_atom(atoms, V.atom_utf8("core/comp.mm")),
                      h_payload=comp_id)
        return comp_id, comp, self._put_atom(atoms, entry.state_bytes)

    def _cycle_witness(self, atoms: dict[bytes, bytes], name: str, comp: V.Cell, entry: bytes, spent: int,
                       actions: int, cost: int) -> V.Cell:
        u = lambda n: self._put_atom(atoms, V.atom_u64(n))
        return V.Cell(h_schema=V.H_SCHEMA["cycle_witness"], h_slot_name=self._put_atom(atoms, V.atom_utf8(name)),
                      h_payload=entry, h_relies=self._hv(atoms, [comp.id]),
                      slots=(comp.h_payload, u(spent), u(actions), u(cost)))

    def _cycle_contract(self, atoms: dict[bytes, bytes], name: str, comp: V.Cell, expected: bytes,
                        witness: V.Cell) -> tuple[V.Cell, V.Cell]:
        k = V.Cell(h_schema=V.H_SCHEMA["contract"], h_slot_name=self._put_atom(atoms, V.atom_utf8(name)),
                   h_payload=self._put_atom(atoms, V.atom_utf8(f"{name} never reaches a normal form")),
                   h_relies=self._hv(atoms, [comp.id]), slots=(V.H_PROVISIONAL, comp.h_payload, expected, V.H_EMPTY))
        w = V.Cell(h_schema=V.H_SCHEMA["verdict"], h_slot_name=self._put_atom(atoms, V.atom_utf8(f"{name}.verdict")),
                   h_payload=k.id, h_relies=self._hv(atoms, [witness.id]), h_attests=self._hv(atoms, [k.id]),
                   slots=(witness.id, V.H_REPLAYED, self._put_atom(atoms, V.atom_utf8(SR.VERIFIER_ID))))
        return k, w

    def test_75_a_cycle_witness_is_checked_by_verify_cycle(self) -> None:
        """§3 check 4 and §4.2 Pass 3, `H_CYCLE_PROVEN`: the gate admits a cycle witness only if
        `sigma_resume.verify_cycle` proves it, admits one whose period exceeds the host ceiling as `NOT_ASSESSED`, and
        Pass 3 counts a witness only for a contract of its own computation expecting `H_CYCLE_PROVEN`, and never a
        `NOT_ASSESSED` one. What `CYCLE_PROVEN` establishes is proved in proofs/Vars1/Cycle.lean; the property suite
        compares `verify_cycle` with the compiled model (I12)."""
        c0, s0, _ = self._bootstrap_genesis("core", adm_threshold=1, acc_threshold=2)
        atoms: dict[bytes, bytes] = {}
        comp_id, comp, entry = self._cycle_fixture(atoms)
        sign = lambda cells: [V.Seal.sign(self.sk1, c.id, s0.id) for c in cells]
        c1 = self._admit(atoms, [comp], sign([comp]), c0)

        # False witnesses are refused at the gate, each by the check that catches it.
        for name, spent, actions, cost, wrong_entry, why in (
                ("core/cw.cost", 3, 1, 3, False, "replay failed: INVALID_CYCLE_WITNESS: the period costs 2, not 3"),
                ("core/cw.actions", 3, 2, 2, False, "replay failed: INVALID_CYCLE_WITNESS: the period stops after 1 actions (PAUSED)"),
                ("core/cw.spent", 2, 1, 2, False, "replay failed: PREFIX_MISMATCH"),
                ("core/cw.entry", 3, 1, 2, True, "replay failed: PREFIX_MISMATCH: the entry is not the state"),
                ("core/cw.zero", 3, 0, 2, False, "CYCLE_WITNESS requires actions >= 1 and cost >= actions"),
                ("core/cw.cheap", 3, 3, 2, False, "CYCLE_WITNESS requires actions >= 1 and cost >= actions")):
            bad = self._cycle_witness(atoms, name, comp, comp_id if wrong_entry else entry, spent, actions, cost)
            cand = self.repo.build_candidate_commit("core", atoms, [bad], sign([bad]), parent_commit=c1)
            with self.assertRaisesRegex(V.VarsError, re.escape(why)):
                self.repo.admit_and_advance("core", cand, expected_old=c1)

        # The true witness, a NOT_ASSESSED one (period above the 10^7 ceiling), and contracts over them.
        cw = self._cycle_witness(atoms, "core/cw.mm", comp, entry, 3, 1, 2)
        big = self._cycle_witness(atoms, "core/cw.big", comp, entry, 3, 1, 10_000_001)
        all_atoms = {**V.STD_SCHEMA_ATOMS, **atoms}
        try:
            self.assertEqual(V.verify_cycle_witness_replay(cw, all_atoms, gate_mode=True), "CYCLE_PROVEN")
            self.assertEqual(V.verify_cycle_witness_replay(cw, all_atoms, gate_mode=False), "CYCLE_PROVEN")
            self.assertEqual(V.verify_cycle_witness_replay(big, all_atoms, gate_mode=True), "NOT_ASSESSED")
        except V.VarsError as e:
            self.fail(f"a true witness, or one above the host ceiling, is refused: {e}")
        with self.assertRaisesRegex(V.VarsError, "NOT_ASSESSED"):
            V.verify_cycle_witness_replay(big, all_atoms, gate_mode=False)
        k_ok, w_ok = self._cycle_contract(atoms, "core/k.cycle", comp, V.H_CYCLE_PROVEN, cw)
        k_big, w_big = self._cycle_contract(atoms, "core/k.big", comp, V.H_CYCLE_PROVEN, big)
        k_nf, w_nf = self._cycle_contract(atoms, "core/k.nf", comp, V.H_K, cw)
        # a witness of another computation (same term, Book I profile) does not settle a contract of this one
        h_env = V.sha256(V.atom_environment([V.sha256(SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=SR.M_H,
                                                                  right=SR.M_H))]))
        other_id = self._put_atom(atoms, V.atom_computation_root(V.sha256(SG.ser(
            SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=SR.M_H, right=SR.M_H)), h_env))
        other = V.Cell(h_schema=V.H_SCHEMA["computation"],
                       h_slot_name=self._put_atom(atoms, V.atom_utf8("core/comp.other")), h_payload=other_id)
        k_other, w_other = self._cycle_contract(atoms, "core/k.other", other, V.H_CYCLE_PROVEN, cw)
        # the boundary: without required_comp, a contract expecting H_CYCLE_PROVEN settles on an attestation alone
        k_att = V.Cell(h_schema=V.H_SCHEMA["contract"], h_slot_name=self._put_atom(atoms, V.atom_utf8("core/k.att")),
                       h_payload=self._put_atom(atoms, V.atom_utf8("attested, not replayed")),
                       slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_CYCLE_PROVEN, V.H_EMPTY))
        w_att = V.Cell(h_schema=V.H_SCHEMA["verdict"], h_slot_name=self._put_atom(atoms, V.atom_utf8("core/k.att.verdict")),
                       h_payload=k_att.id, h_attests=self._hv(atoms, [k_att.id]),
                       slots=(V.H_EMPTY, V.H_ATTESTED, self._put_atom(atoms, V.atom_utf8(SR.VERIFIER_ID))))
        cells = [cw, big, k_ok, w_ok, k_big, w_big, k_nf, w_nf, other, k_other, w_other, k_att, w_att]
        self._admit(atoms, cells, sign(cells), c1)
        lens = self.repo.lens("core")
        self.assertTrue(lens["settled"][k_ok.id], "a proven cycle witness settles its contract")
        self.assertFalse(lens["settled"][k_big.id], "a NOT_ASSESSED cycle witness is never a witness")
        self.assertFalse(lens["settled"][k_nf.id], "a cycle witness answers only H_CYCLE_PROVEN")
        self.assertFalse(lens["settled"][k_other.id], "a cycle witness answers only for its own computation")
        self.assertTrue(lens["settled"][k_att.id], "without required_comp, Settled is an attestation (ASSURANCE.md)")

    def _commit_files(self, files: dict[str, bytes], msg: str) -> str:
        """Commit `files` on branch main of the scratch repository (beside its refs/vars) and return the commit."""
        g = lambda *a: subprocess.run(["git", "-C", str(self.repo_path), *a], capture_output=True, check=True).stdout
        g("checkout", "-q", "-B", "main")
        for path, raw in files.items():
            (self.repo_path / path).parent.mkdir(parents=True, exist_ok=True)
            (self.repo_path / path).write_bytes(raw)
            g("add", path)
        g("commit", "-q", "--allow-empty", "-m", msg)
        return g("rev-parse", "HEAD").decode().strip()

    def test_76_the_release_profile_names_the_gate_the_rules_hash_does_not(self) -> None:
        """H_LENS_KERNEL names the fold and Passes 1–2, not the host's admission (ASSURANCE.md): two commits whose gate
        differs carry the same rules hash and different release profiles. The profile is read from the commit's
        objects; the offline verifier's rules are read from its own bytes; `verify-release` recomputes the profile a
        release names and records INVALID when the commit's files are not those it names."""
        mc = self._minds_chain()
        wasm = V.KERNEL_ATOM
        verifier = f'H_LENS_KERNEL = bytes.fromhex("{V.H_LENS_KERNEL.hex()}")\n'.encode()
        a = self._commit_files({"vars1.py": b"gate one\n", "verify/minds_verify.py": verifier,
                                "kernel/lens.wasm": wasm}, "one")
        b = self._commit_files({"vars1.py": b"gate two\n"}, "two")
        pa, pb = mc.profile_at(self.repo_path, a), mc.profile_at(self.repo_path, b)
        self.assertEqual(pa["rules_carried"], {"v1": V.H_LENS_KERNEL.hex()})
        self.assertEqual(pa["rules_carried"], pb["rules_carried"], "the rules hash does not see the gate change")
        self.assertNotEqual(pa["id"], pb["id"], "the profile does")
        self.assertNotEqual(pa["files"].get("vars1.py"), pb["files"].get("vars1.py"))
        self.assertIn("meter.py", pa["files"])
        self.assertIsNone(pa["files"]["meter.py"], "a file the commit lacks is named as absent")
        self.assertEqual(pa["offline_reads"], {"v1": V.H_LENS_KERNEL.hex()})
        c = self._commit_files({"verify/minds_verify.py": verifier.replace(V.H_LENS_KERNEL.hex().encode(), b"ab" * 32)},
                               "three")
        self.assertEqual(mc.profile_at(self.repo_path, c)["offline_reads"], {"other": "ab" * 32},
                         "a verifier naming rules the commit does not carry reads none of them")
        self.assertEqual(mc.profile_at(self.repo_path, a)["id"], pa["id"], "the profile is a function of the commit")
        with self.assertRaisesRegex(V.VarsError, "not a full commit id"):
            mc.profile_at(self.repo_path, "main")

        sk, sk2 = b"\x07" * 32, b"\x08" * 32
        mc.init(self.repo_path, sk)
        mc.join(self.repo_path, sk, V.ed25519_pubkey(sk2), "second")
        _, good = mc.release(self.repo_path, sk, b, ["test_vars1 OK"], profile=pb["id"])
        _, wrong = mc.release(self.repo_path, sk, a, ["test_vars1 OK"], profile=pb["id"])  # names b's files
        repo = V.GitVarsRepo(self.repo_path)
        atoms, cells, _ = repo.read_cas_tree(repo.ref_commit("minds"))
        stmt = V.parse_utf8(atoms[cells[good["decision"]].h_payload])
        self.assertEqual(mc.parse_release_profile(stmt)[:3], (b, V.H_LENS_KERNEL, pb["id"]))
        self.assertEqual(mc.parse_release(stmt), (b, V.H_LENS_KERNEL, None), "older readers still parse it")
        fake = lambda repo_dir, sha, rules: (["test_vars1 OK"], True)
        _, ok, lines = mc.verify_release(self.repo_path, sk2, good["decision"], "second", checks=fake)
        self.assertTrue(ok)
        self.assertIn(f"release profile {pb['id'][:12]} is the commit's OK", lines)
        _, ok, lines = mc.verify_release(self.repo_path, sk2, wrong["decision"], "second", checks=fake)
        self.assertFalse(ok, "every check passed, but the commit's files are not the ones the release names")
        self.assertIn(f"release profile {pb['id'][:12]} is the commit's FAILED", lines)
        lens = repo.lens("minds")
        self.assertTrue(lens["settled"][good["decision"]])
        self.assertFalse(lens["settled"][wrong["decision"]])

        # The earlier reader (before profiles, main@21ffb48) matched this prefix only; it still reads a new statement
        old = r"^minds release main@([0-9a-f]{40}) rules@([0-9a-f]{64})(?: sigma-glyph@([0-9a-f]{40}))?(?: primitives@([0-9a-f]{40}))?;"
        self.assertEqual(re.match(old, stmt).groups()[:2], (b, V.H_LENS_KERNEL.hex()))
        self.assertTrue(stmt.endswith(f"; profile@{pb['id']}"))
        fresh = self._commit_files({"fresh": b"f"}, "a commit no release names yet")
        for bad in (["a; b OK"], ["profile@" + "0" * 64]):  # without the guard, these would be recorded
            with self.assertRaisesRegex(V.VarsError, "may not contain"):
                mc.release(self.repo_path, sk, fresh, bad, profile=pb["id"])
        with self.assertRaisesRegex(V.VarsError, "lowercase hex"):  # Codex PR #4 r2 F3
            mc.release(self.repo_path, sk, fresh, ["x OK"], profile="0" * 64 + "; extra")
        with self.assertRaisesRegex(V.VarsError, "malformed profile"):
            mc.parse_release_profile(f"minds release main@{fresh} rules@{V.H_LENS_KERNEL.hex()}; checks: x OK; "
                                     f"profile@{'0' * 64}; extra")

        # A symlink's blob is a name, not the bytes that run (Codex PR #4 r1 F1): a profile path must be a regular file
        (self.repo_path / "kernel" / "body.mjs").write_bytes(b"// runner\n")
        (self.repo_path / "kernel" / "run.mjs").symlink_to("body.mjs")
        g = lambda *x: subprocess.run(["git", "-C", str(self.repo_path), *x], capture_output=True, check=True).stdout
        g("add", "kernel/body.mjs", "kernel/run.mjs")
        g("commit", "-q", "-m", "link")
        link = g("rev-parse", "HEAD").decode().strip()
        with self.assertRaisesRegex(V.VarsError, "kernel/run.mjs .* is not a regular file"):
            mc.profile_at(self.repo_path, link)
        # nor through a directory on the way (Codex PR #4 r2 F1): `kernel -> actual-kernel`
        g("rm", "-q", "-r", "--cached", "kernel")
        (self.repo_path / "kernel").rename(self.repo_path / "actual-kernel")
        (self.repo_path / "actual-kernel" / "run.mjs").unlink()
        (self.repo_path / "actual-kernel" / "run.mjs").write_bytes(b"// runner\n")
        (self.repo_path / "kernel").symlink_to("actual-kernel")
        g("add", "kernel", "actual-kernel")
        g("commit", "-q", "-m", "linked directory")
        with self.assertRaisesRegex(V.VarsError, "kernel at .* is not a directory"):
            mc.profile_at(self.repo_path, g("rev-parse", "HEAD").decode().strip())
        _, linked = mc.release(self.repo_path, sk, link, ["test_vars1 OK"], profile=pb["id"])
        _, ok, lines = mc.verify_release(self.repo_path, sk2, linked["decision"], "second", checks=fake)
        self.assertFalse(ok)
        self.assertIn(f"release profile {pb['id'][:12]} is the commit's FAILED", lines)

    def test_80_the_profile_closes_over_what_the_gate_loads(self) -> None:
        """Every repository file the profiled code loads is itself profiled: the local modules the Python files
        import, the files `vars1.py` opens under kernel/ and kernel2/, and the relative imports of the wasm runners
        (node built-ins and the Python standard library come from the host, ASSURANCE.md)."""
        mc = self._minds_chain()
        profiled = set(mc.PROFILE_FILES)
        for path in profiled:
            text = (ROOT_DIR / path).read_text(errors="replace") if not path.endswith(".wasm") else ""
            if path.endswith(".py"):
                for mod in re.findall(r"^\s*(?:from|import)\s+([A-Za-z_]\w*)", text, re.M):
                    for where in (f"{mod}.py", f"verify/{mod}.py"):
                        if (ROOT_DIR / where).exists():
                            self.assertIn(where, profiled, f"{path} imports {mod}")
                for d, name in re.findall(r"(KERNEL2?_DIR) / \"([^\"]+)\"", text):
                    self.assertIn(("kernel2/" if d == "KERNEL2_DIR" else "kernel/") + name, profiled, f"{path} opens it")
            if path.endswith(".mjs"):
                for spec in re.findall(r"from\s+\"(\.{1,2}/[^\"]+)\"", text):
                    rel = (Path(path).parent / spec).as_posix()
                    self.assertIn(rel, profiled, f"{path} imports {spec}")

    def test_77_status_tells_merged_from_settled(self) -> None:
        """`status` reads the chain and main and writes nothing: whether main is released, how far main is past its
        last release, and for each release who has attested it, contradicted it, or not yet answered — counted
        against the evaluators the release itself names, so a release recorded before a join awaits no one."""
        mc = self._minds_chain()
        sk, sk2 = b"\x07" * 32, b"\x08" * 32
        pk, pk2 = V.ed25519_pubkey(sk).hex(), V.ed25519_pubkey(sk2).hex()
        one = self._commit_files({"claims.json": json.dumps({"claims": [{"status": "tested"}, {"status": "assumed"},
                                                                      {"status": "tested"}]}).encode()}, "one")
        mc.init(self.repo_path, sk)
        _, r1 = mc.release(self.repo_path, sk, one, ["test_vars1 OK"])
        mc.join(self.repo_path, sk, bytes.fromhex(pk2), "second")
        two = self._commit_files({"x": b"x"}, "two")
        three = self._commit_files({"y": b"y"}, "three")
        _, r2 = mc.release(self.repo_path, sk, two, ["test_vars1 OK"])
        _, r3 = mc.release(self.repo_path, sk, three, ["test_vars1 OK"])
        waiting = mc.status(self.repo_path)["unwitnessed_projections"]
        self.assertEqual({w["id"] for w in waiting}, {r2["projection"].hex(), r3["projection"].hex()})
        self.assertTrue(all(w["unwitnessed_by"] == [pk2] for w in waiting))
        mc.verify_release(self.repo_path, sk2, r3["decision"], "second", checks=lambda *a: (["x FAILED"], False))
        before = subprocess.run(["git", "-C", str(self.repo_path), "for-each-ref"], capture_output=True).stdout
        st = mc.status(self.repo_path)
        self.assertEqual(subprocess.run(["git", "-C", str(self.repo_path), "for-each-ref"],
                                        capture_output=True).stdout, before, "status writes nothing")
        rows = {r["commit"]: r for r in st["releases"]}
        self.assertEqual((rows[one]["settled"], rows[one]["attested_by"], rows[one]["awaiting"]), (True, [pk], []),
                         "a release before the join awaits no one")
        self.assertEqual((rows[two]["settled"], rows[two]["attested_by"], rows[two]["awaiting"]), (False, [pk], [pk2]))
        self.assertEqual((rows[three]["settled"], rows[three]["invalid_by"], rows[three]["awaiting"]),
                         (False, [pk2], []), "an INVALID is an answer, and not a settlement")
        self.assertEqual((st["main"], st["main_released"], st["last_released"], st["commits_since_release"]),
                         (three, True, three, 0))
        self.assertEqual(st["unsettled"], sorted([f"minds/release/{two[:12]}", f"minds/release/{three[:12]}"]))
        self.assertEqual(st["claims_at_main"], {"assumed": 1, "tested": 2})
        self.assertEqual(st["rules"], {"id": V.H_LENS_KERNEL.hex(), "name": "v1"})
        self.assertEqual(st["unwitnessed_projections"], [], "a member's verdict also witnesses the chain")
        self._commit_files({"z": b"z"}, "four")
        self._commit_files({"w": b"w"}, "five")
        st = mc.status(self.repo_path)
        self.assertEqual((st["main_released"], st["last_released"], st["commits_since_release"]), (False, three, 2))

    def test_79_status_reads_pass_3(self) -> None:
        """`status` counts what Pass 3 counts, not every stored verdict (Codex PR #4 r1 F3, F4): a verdict that
        attests nothing, an answer superseded by NOT_ASSESSED, and a superseded INVALID leave the member awaited;
        an early release naming no evaluators is read under the scope's current admission policy, so after a
        rotation that replaces the key that attested it, the new key is awaited."""
        import dataclasses
        mc = self._minds_chain()
        sk, sk2 = b"\x07" * 32, b"\x08" * 32
        pk2 = V.ed25519_pubkey(sk2).hex()
        repo = V.GitVarsRepo(self.repo_path)

        def add(atoms: dict, cells: list, signer: bytes) -> None:
            s = mc.governing_scope(repo)
            tip = repo.ref_commit("minds")
            c = repo.build_candidate_commit("minds", atoms, cells, [V.Seal.sign(signer, x.id, s) for x in cells],
                                            parent_commit=tip)
            repo.admit_and_advance("minds", c, expected_old=tip)

        def row(did: bytes) -> dict:
            return next(r for r in mc.status(self.repo_path)["releases"] if r["id"] == did.hex())

        def answer(did: bytes, ok: bool) -> V.Cell:
            mc.verify_release(self.repo_path, sk2, did, "second", checks=lambda *a: (["x OK"], ok))
            atoms, cells, _ = repo.read_cas_tree(repo.ref_commit("minds"))
            return next(c for c in cells.values() if c.h_schema == V.H_SCHEMA["verdict"] and c.h_payload == did
                        and V.parse_utf8(atoms[c.slots[2]]) == "second")

        def withdraw(w: V.Cell) -> None:
            a: dict[bytes, bytes] = {}
            add(a, [dataclasses.replace(w, h_supersedes=mc._put(a, V.atom_hvec([w.id])),
                                        h_loss=mc._put(a, V.atom_utf8("withdrawn")),
                                        slots=(V.H_EMPTY, V.H_NOT_ASSESSED, w.slots[2]))], sk2)

        mc.init(self.repo_path, sk)
        mc.join(self.repo_path, sk, bytes.fromhex(pk2), "second")
        _, r1 = mc.release(self.repo_path, sk, "a" * 40, ["x OK"])
        a: dict[bytes, bytes] = {}
        add(a, [V.Cell(V.H_SCHEMA["verdict"], mc._put(a, V.atom_utf8("minds/no-attests")), r1["decision"],
                       slots=(V.H_EMPTY, V.H_ATTESTED, mc._put(a, V.atom_utf8("second"))))], sk2)
        r = row(r1["decision"])
        self.assertEqual((r["settled"], r["awaiting"]), (False, [pk2]), "a verdict attesting nothing is no answer")

        _, r2 = mc.release(self.repo_path, sk, "b" * 40, ["x OK"])
        withdraw(answer(r2["decision"], True))
        r = row(r2["decision"])
        self.assertEqual((r["settled"], r["awaiting"], pk2 in r["attested_by"]), (False, [pk2], False),
                         "a superseded ATTESTED is no answer")

        _, r3 = mc.release(self.repo_path, sk, "d" * 40, ["x OK"])
        w = answer(r3["decision"], False)
        self.assertEqual((row(r3["decision"])["invalid_by"], row(r3["decision"])["awaiting"]), ([pk2], []))
        withdraw(w)
        r = row(r3["decision"])
        self.assertEqual((r["invalid_by"], r["awaiting"]), ([], [pk2]), "a superseded INVALID is no answer")

        # a foreign INVALID, cross-sealed by an evaluator: the cross-seal is edge authority, not Pass 3's endorsement
        # (Codex PR #4 r2 F2); the evaluator is still awaited, and its own attestation settles the release
        _, r4 = mc.release(self.repo_path, sk, "e" * 40, ["x OK"])
        key = b"\x09" * 32
        a = {}
        pol = mc._policy(a, 1, [V.ed25519_pubkey(key)])
        peer = V.Cell(V.H_SCHEMA["scope"], mc._put(a, V.atom_utf8("peer/SCOPE")), mc._put(a, V.atom_utf8("peer")),
                      slots=(pol, pol, V.H_LENS_KERNEL))
        bad = V.Cell(V.H_SCHEMA["verdict"], mc._put(a, V.atom_utf8("peer/invalid")), r4["decision"],
                     slots=(V.H_EMPTY, V.H_VERDICT_INVALID, mc._put(a, V.atom_utf8("second"))))
        acc = V.Cell(V.H_SCHEMA["acceptance"], mc._put(a, V.atom_utf8("minds/import-invalid")), bad.id,
                     slots=(mc._put(a, V.atom_utf8("peer")), peer.id))
        s = mc.governing_scope(repo)
        tip = repo.ref_commit("minds")
        c = repo.build_candidate_commit("minds", a, [peer, bad, acc],
                                        [V.Seal.sign(key, peer.id, peer.id), V.Seal.sign(key, bad.id, peer.id),
                                         V.Seal.sign(sk2, bad.id, s), V.Seal.sign(sk, acc.id, s)], parent_commit=tip)
        repo.admit_and_advance("minds", c, expected_old=tip)
        lens = repo.lens("minds")
        self.assertTrue(lens["active"][bad.id] and not lens["stale"][bad.id])
        r = row(r4["decision"])
        self.assertEqual((r["settled"], r["invalid_by"], r["awaiting"]), (False, [], [pk2]))
        answer(r4["decision"], True)
        r = row(r4["decision"])
        self.assertEqual((r["settled"], r["invalid_by"], pk2 in r["attested_by"]), (True, [], True))

        # an early release, naming no evaluators: the scope's admission policy, current at the tip
        a = {}
        d = V.Cell(V.H_SCHEMA["decision"], mc._put(a, V.atom_utf8("minds/release/cccccccccccc")),
                   mc._put(a, V.atom_utf8(f"minds release main@{'c' * 40} rules@{V.H_LENS_KERNEL.hex()}; checks: x OK")),
                   slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY))
        v = V.Cell(V.H_SCHEMA["verdict"], mc._put(a, V.atom_utf8("minds/legacy")), d.id,
                   h_attests=mc._put(a, V.atom_hvec([d.id])),
                   slots=(V.H_EMPTY, V.H_ATTESTED, mc._put(a, V.atom_utf8("minds-maintainer"))))
        add(a, [d, v], sk)
        r = row(d.id)
        self.assertEqual((r["settled"], r["threshold"], r["awaiting"]), (True, 1, []),
                         "1-of-2 admission: the maintainer alone settles it, and a Settled release awaits no one")
        a = {}
        pol = mc._policy(a, 1, [bytes.fromhex(pk2)])
        add(a, [V.Cell(V.H_SCHEMA["scope"], mc._put(a, V.atom_utf8("minds/SCOPE")), mc._put(a, V.atom_utf8("new roster")),
                       h_supersedes=mc._put(a, V.atom_hvec([mc.governing_scope(repo)])),
                       h_loss=mc._put(a, V.atom_utf8("replace the maintainer")), slots=(pol, pol, V.H_LENS_KERNEL))], sk)
        r = row(d.id)
        self.assertEqual((r["settled"], r["evaluators"], r["attested_by"], r["awaiting"]), (False, [pk2], [], [pk2]))

    def test_78_each_structural_refusal_has_its_own_input(self) -> None:
        """Each refusal below is reached by its own input (the claims' earlier witnesses never reached them, so a
        mutant removing one survived): raw cell and seal bytes written to the CAS as a writer could, a seal on a cell
        the commit lacks, a foreign cell without its scope, a schema cell with a payload. Without its check, the loss,
        magic and schema inputs are admitted; the foreign cell is still refused by the kernel (twin divergence) and
        the stray seal by the generic malformed-commit refusal, so only the reason changes there. A canonical
        neighbour of each is admitted."""
        c0, s0, _ = self._bootstrap_genesis("core")

        def raw_cell(path_raw: bytes, atoms: dict, seals: list, cells: tuple = ()) -> str:
            h = V.sha256(path_raw).hex()
            return self.repo.build_candidate_commit("core", atoms, list(cells), seals, parent_commit=c0,
                                                    extra_tree_entries=[("100644", "blob", f"cas/cells/{h[:2]}/{h[2:]}",
                                                                         path_raw)])

        def refused(regex: str, cand: str) -> None:
            with self.assertRaisesRegex(V.VarsError, regex):
                self.repo.admit_and_advance("core", cand, expected_old=c0)

        # §1.2 rule 1: an eviction without loss, as bytes (the encoder refuses to make it)
        a: dict[bytes, bytes] = {}
        old = self._axiom(a, "core/old", "old")
        new = self._axiom(a, "core/old", "new", supersedes=[old.id])
        raw = bytearray(new.encode())
        raw[8 + 32 * 8: 8 + 32 * 9] = V.H_EMPTY
        refused("eviction cell missing H_loss",
                raw_cell(bytes(raw), a, [V.Seal.sign(self.sk1, V.sha256(bytes(raw)), s0.id),
                                         V.Seal.sign(self.sk1, old.id, s0.id)], cells=(old,)))

        # §1.1: the magic is part of the cell; a cell that differs only there is refused
        ax = self._axiom(a, "core/ax", "ax")
        bad = b"VARX" + ax.encode()[4:]
        refused("missing VAR1 magic", raw_cell(bad, a, [V.Seal.sign(self.sk1, V.sha256(bad), s0.id)]))

        # §1.3: a seal is "SEAL" ‖ …; one whose signature covers another magic is refused for the magic
        pk = V.ed25519_pubkey(self.sk1)
        body = b"SEAX" + ax.id + s0.id + pk
        sx = body + V.ed25519_sign(self.sk1, body)
        hx = V.sha256(sx).hex()
        cand = self.repo.build_candidate_commit("core", a, [ax], [], parent_commit=c0,
                                                extra_tree_entries=[("100644", "blob", f"cas/seals/{hx[:2]}/{hx[2:]}", sx)])
        refused("invalid SEAL length or magic", cand)

        # §3 check 4: a seal names a cell of the commit
        stray = V.Seal.sign(self.sk1, b"\x42" * 32, s0.id)
        refused("Seal target or scope_ctx missing",
                self.repo.build_candidate_commit("core", a, [ax], [V.Seal.sign(self.sk1, ax.id, s0.id), stray],
                                                 parent_commit=c0))

        # §3 check 5: a foreign cell arrives with a self-sealed scope of its origin
        fa: dict[bytes, bytes] = {}
        fx = self._axiom(fa, "peerB/x", "a peerB fact")
        refused("lacks self-sealed foreign SCOPE",
                self.repo.build_candidate_commit("core", fa, [fx], [V.Seal.sign(self.sk_peer, fx.id, fx.id)],
                                                 parent_commit=c0))

        # §1.2 rule 4: a schema cell has an empty payload and no edges
        sa: dict[bytes, bytes] = {}
        schema = V.Cell(V.H_META_SCHEMA, self._put_atom(sa, V.atom_utf8("core/custom")),
                        self._put_atom(sa, V.atom_utf8("a payload")), slots=(self._put_atom(sa, V.atom_utf8("n:u64")),))
        refused("schema definition cell must have H_EMPTY payload",
                self.repo.build_candidate_commit("core", sa, [schema], [V.Seal.sign(self.sk1, schema.id, s0.id)],
                                                 parent_commit=c0))

        # the neighbour: the same cells, canonical, admit
        good = V.Cell(V.H_META_SCHEMA, schema.h_slot_name, V.H_EMPTY, slots=schema.slots)
        self._admit({**a, **sa}, [ax, good], [V.Seal.sign(self.sk1, ax.id, s0.id),
                                               V.Seal.sign(self.sk1, good.id, s0.id)], c0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
