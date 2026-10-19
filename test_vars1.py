#!/usr/bin/env python3
"""Conformance suite for `vars1.py` (VARS-1-SPEC.md).

Every fold and `lens()` runs the rules kernel (`kernel/lens.wasm`) and its Python twin, which must agree bit for bit;
every `lens()` is also re-run on a separate kernel instance.
Covers golden vectors, the gate's rejections, the local compute/checkpoint/verdict loop, rebinding and rollback,
foreign import and acceptance, scope rotation without retroactivity, replay trust, and all Ed25519 vectors of
`primitives/vectors/verify-sig.json`.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent
PROJECTS_DIR = ROOT_DIR.parent
sys.path.insert(0, str(ROOT_DIR))
sys.path.insert(0, str(PROJECTS_DIR / "sigma-glyph" / "impl"))

import sigma_glyph as SG  # noqa: E402
import sigma_resume as SR  # noqa: E402
import vars1 as V  # noqa: E402


class KernelCheckedRepo(V.GitVarsRepo):
    """Every lens() is re-run on a separate rules-kernel instance (kernel/lens.wasm): Passes 1-2 must reproduce."""

    runner: "V.KernelRunner | None" = None

    def lens(self, scope: str):
        out = super().lens(scope)
        if KernelCheckedRepo.runner is None:
            KernelCheckedRepo.runner = V.KernelRunner()
        for cid, bits in KernelCheckedRepo.runner.statuses(out).items():
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
        self.assertEqual(V.H_LENS_KERNEL.hex(), "993c237fca82d922f61e23759bf43486f17d861a7353c77768fd33c221723263")
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
        # --- 1. Run all 34 Ed25519 vectors in `primitives/vectors/verify-sig.json` ---
        vectors_path = PROJECTS_DIR / "primitives" / "vectors" / "verify-sig.json"
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


    def test_11_projection_is_recomputed_at_the_gate_and_settled_by_witnesses(self) -> None:
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


if __name__ == "__main__":
    unittest.main(verbosity=2)

