#!/usr/bin/env python3
"""Conformance, end-to-end 3-agent experiment, and mutant suite for Metered Portable Agent Spores
(`spore.py`, `proofs/Vars1/Spore.lean`, `AGENT-SPORE-DIRECTION.md` AS-1..AS-8).

    .venv/bin/python -m unittest -v test_spore
    .venv/bin/python test_spore.py --mutants
"""
from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import spore as SP
import vars1 as V

SR = V.SR
ROOT = Path(__file__).resolve().parent


def _seed(n: int) -> bytes:
    return bytes([n]) * 32


def _make_app(f_hash: bytes, a_hash: bytes):
    """Build a canonical Book I APPLY(f, a) atom using sigma-glyph's own serializer."""
    SG = SR.G
    raw = SG.ser(SG.APPLY, SG.F_LEFT | SG.F_RIGHT, left=f_hash, right=a_hash)
    return V.sha256(raw), raw


def _build_nested_i_k(depth: int = 3):
    """Build Book I term I(I(...I(K)...)) of given nesting depth -> reduces in `depth` steps to H_K."""
    atoms = {}
    cur = V.H_K
    chain = []
    for _ in range(depth):
        h, raw = _make_app(V.H_I, cur)
        atoms[h] = raw
        chain.append(h)
        cur = h
    return cur, atoms, chain


class TestSpores(unittest.TestCase):
    def test_01_unfold_on_demand_ignores_missing_unneeded_branch(self):
        """AS-1: minimal spore fetches ONLY needed atoms; an unreferenced missing atom does not block."""
        root_h, atoms, chain = _build_nested_i_k(2)
        remote = SP.ContentStore(atoms)
        unneeded_missing = V.sha256(b"unneeded-branch-not-in-store")
        self.assertFalse(remote.has(unneeded_missing))

        ex = SP.SporeExecutor(_seed(1), local_atoms={}, remote_fetch=remote.get_raw)
        task = SP.TaskSpec(
            subject="reduce/i2k",
            rules_hash=V.H_LENS_KERNEL_V2.hex(),
            runtime="book1/sigma-resume",
            input_term_hash=root_h.hex(),
            env_hashes=(),
            expected_nf_hash=V.H_K.hex(),
        )
        res, ckpt = ex.execute(task, SP.Budget(atp=100, fetches=10, spawns=0, depth=0))
        self.assertEqual(res.outcome, "NORMAL_FORM")
        self.assertEqual(res.nf_term_hash, V.H_K.hex())
        self.assertEqual(res.spent_fetches, 2)
        self.assertEqual(res.bytes_fetched, sum(len(v) for v in atoms.values()))
        self.assertEqual(res.partiality.slice_completeness, "COMPLETE")
        self.assertEqual(res.partiality.history_link, "VERIFIED_HERE")
        self.assertEqual(res.partiality.reliance, "RELIABLE")
        self.assertIsNotNone(ckpt)
        self.assertTrue(res.verify_signature())
        self.assertTrue(ckpt.verify_signature())

    def test_02_missing_needed_dependency_stops_partial(self):
        """AS-1 & AS-4: missing required atom yields NOT_ASSESSED + PARTIAL naming exact hash."""
        root_h, atoms, chain = _build_nested_i_k(2)
        # Drop inner atom chain[0] from remote store
        partial_atoms = {chain[1]: atoms[chain[1]]}
        remote = SP.ContentStore(partial_atoms)
        ex = SP.SporeExecutor(_seed(2), local_atoms={}, remote_fetch=remote.get_raw)
        task = SP.TaskSpec(
            subject="reduce/missing",
            rules_hash=V.H_LENS_KERNEL_V2.hex(),
            runtime="book1/sigma-resume",
            input_term_hash=root_h.hex(),
            env_hashes=(),
        )
        res, ckpt = ex.execute(task, SP.Budget(atp=100, fetches=10, spawns=0, depth=0))
        self.assertEqual(res.outcome, "NOT_ASSESSED")
        self.assertEqual(res.partiality.slice_completeness, "PARTIAL")
        self.assertEqual(res.partiality.stop_reason, "MISSING_DEPENDENCY")
        self.assertIn(chain[0].hex(), res.partiality.missing_hashes)
        self.assertIsNotNone(ckpt)
        self.assertEqual(ckpt.stop_reason, "MISSING_DEPENDENCY")

    def test_03_corrupted_fetch_fails_integrity(self):
        """AS-1 & AS-8: fetched bytes whose SHA-256 != requested hash are refused as INTEGRITY_FAILED."""
        root_h, atoms, _ = _build_nested_i_k(1)
        remote = SP.ContentStore()
        remote.put_raw_unverified(root_h, b"corrupted-bytes-wrong-hash")
        ex = SP.SporeExecutor(_seed(3), local_atoms={}, remote_fetch=remote.get_raw)
        task = SP.TaskSpec(
            subject="reduce/corrupt",
            rules_hash=V.H_LENS_KERNEL_V2.hex(),
            runtime="book1/sigma-resume",
            input_term_hash=root_h.hex(),
            env_hashes=(),
        )
        res, ckpt = ex.execute(task, SP.Budget(atp=50, fetches=5, spawns=0, depth=0))
        self.assertEqual(res.outcome, "REFUSED")
        self.assertEqual(res.partiality.integrity, "FAILED")
        self.assertEqual(res.partiality.stop_reason, "INTEGRITY_FAILED")
        self.assertIsNone(ckpt)

    def test_04_budget_conservation_and_bounded_recursion(self):
        """AS-2: spawning partitions parent budget; overallocation, depth=0 and spawns=0 are refused."""
        root_b = SP.Budget(atp=100, fetches=10, spawns=3, depth=2)
        child1 = SP.Budget(atp=40, fetches=4, spawns=1, depth=1)
        rem1 = root_b.spawn_partition(child1)
        self.assertEqual(rem1.atp + child1.atp, root_b.atp)
        self.assertEqual(rem1.fetches + child1.fetches, root_b.fetches)
        self.assertEqual(rem1.spawns + child1.spawns + 1, root_b.spawns)
        self.assertLess(child1.depth, root_b.depth)

        # Grandchild from child1
        grand = SP.Budget(atp=15, fetches=2, spawns=0, depth=0)
        rem_c1 = child1.spawn_partition(grand)
        self.assertEqual(rem1.atp + rem_c1.atp + grand.atp, root_b.atp)
        self.assertEqual(rem1.fetches + rem_c1.fetches + grand.fetches, root_b.fetches)

        # Refusals: overallocation, depth not strictly decreasing, spawns exhausted
        with self.assertRaises(SP.SporeError) as cm1:
            rem1.spawn_partition(SP.Budget(atp=61, fetches=0, spawns=0, depth=1))
        self.assertEqual(cm1.exception.code, "BUDGET_OVERALLOCATION")
        with self.assertRaises(SP.SporeError) as cm2:
            rem1.spawn_partition(SP.Budget(atp=10, fetches=0, spawns=0, depth=2))
        self.assertEqual(cm2.exception.code, "DEPTH_EXCEEDED")
        with self.assertRaises(SP.SporeError) as cm3:
            grand.spawn_partition(SP.Budget(atp=1, fetches=0, spawns=0, depth=0))
        self.assertIn(cm3.exception.code, ("SPAWN_BUDGET_EXHAUSTED", "DEPTH_EXCEEDED"))

    def test_05_budget_exhaustion_yields_not_assessed_never_refutation(self):
        """AS-2, AS-4, AS-8: ATP exhaustion yields NOT_ASSESSED + checkpoint, never MISMATCH or false verdict."""
        root_h, atoms, _ = _build_nested_i_k(2)
        ex = SP.SporeExecutor(_seed(5), local_atoms=atoms)
        task = SP.TaskSpec(
            subject="reduce/zero-atp",
            rules_hash=V.H_LENS_KERNEL_V2.hex(),
            runtime="book1/sigma-resume",
            input_term_hash=root_h.hex(),
            env_hashes=(),
            expected_nf_hash=V.H_K.hex(),
        )
        res, ckpt = ex.execute(task, SP.Budget(atp=0, fetches=0, spawns=0, depth=0))
        self.assertEqual(res.outcome, "NOT_ASSESSED")
        self.assertEqual(res.partiality.execution, "CHECKPOINTED")
        self.assertEqual(res.partiality.stop_reason, "ATP_EXHAUSTED")
        self.assertIsNotNone(ckpt)
        self.assertEqual(ckpt.stop_reason, "ATP_EXHAUSTED")

    def test_06_separate_task_and_execution_identities(self):
        """AS-3: changing local budget changes execution_id, never task_id."""
        root_h, atoms, _ = _build_nested_i_k(1)
        ex = SP.SporeExecutor(_seed(6), local_atoms=atoms)
        task = SP.TaskSpec(
            subject="reduce/id-sep",
            rules_hash=V.H_LENS_KERNEL_V2.hex(),
            runtime="book1/sigma-resume",
            input_term_hash=root_h.hex(),
            env_hashes=(),
        )
        r1, _ = ex.execute(task, SP.Budget(atp=10, fetches=0, spawns=0, depth=0))
        r2, _ = ex.execute(task, SP.Budget(atp=50, fetches=0, spawns=0, depth=0))
        self.assertEqual(r1.task_id, r2.task_id)
        self.assertNotEqual(r1.execution_id, r2.execution_id)
        self.assertEqual(r1.nf_term_hash, r2.nf_term_hash)

    def test_07_partiality_lattice_and_no_retelling_inflation(self):
        """AS-4 & AS-5: retell() never inflates, never preserves VERIFIED_HERE, is idempotent; meet <= operands."""
        p_full = SP.PartialityVector("VERIFIED", "VERIFIED", "COMPLETE", "COMPLETED", "VERIFIED_HERE", "RELIABLE")
        p_part = SP.PartialityVector("VERIFIED", "VERIFIED", "PARTIAL", "CHECKPOINTED", "WITNESSED", "CONDITIONAL", ("aa" * 32,))
        rt1 = p_full.retell()
        rt2 = rt1.retell()
        self.assertTrue(rt1.le(p_full))
        self.assertEqual(rt1.history_link, "WITNESSED")
        self.assertEqual(rt1.reliance, "CONDITIONAL")
        self.assertEqual(rt1, rt2)
        m = p_full.meet(p_part)
        self.assertTrue(m.le(p_full))
        self.assertTrue(m.le(p_part))
        self.assertEqual(m.slice_completeness, "PARTIAL")
        self.assertEqual(m.history_link, "WITNESSED")

    def test_08_receive_result_refuses_context_substitution_and_bad_sig(self):
        """AS-3 & AS-5: substituting subject, rules, trust_context or untrusted key is refused."""
        root_h, atoms, _ = _build_nested_i_k(1)
        ex = SP.SporeExecutor(_seed(8), local_atoms=atoms, trust_context="org-a/prod")
        task = SP.TaskSpec(
            subject="subj-A",
            rules_hash=V.H_LENS_KERNEL_V2.hex(),
            runtime="book1/sigma-resume",
            input_term_hash=root_h.hex(),
            env_hashes=(),
        )
        res, _ = ex.execute(task, SP.Budget(atp=50, fetches=0, spawns=0, depth=0))
        trusted = {ex.pub_hex}

        ok, code, pv = SP.receive_result(res, expected_task=task, trusted_executors=trusted, expected_trust_context="org-a/prod")
        self.assertTrue(ok)
        self.assertEqual(code, "OK")
        self.assertEqual(pv.history_link, "WITNESSED")
        self.assertEqual(pv.reliance, "CONDITIONAL")

        # Substitute subject -> TASK_MISMATCH
        task_other_subj = SP.TaskSpec("subj-B", V.H_LENS_KERNEL_V2.hex(), "book1/sigma-resume", root_h.hex(), ())
        ok2, code2, _ = SP.receive_result(res, expected_task=task_other_subj, trusted_executors=trusted)
        self.assertFalse(ok2)
        self.assertEqual(code2, "TASK_MISMATCH")

        # Substitute trust context -> TRUST_CONTEXT_MISMATCH
        ok3, code3, _ = SP.receive_result(res, expected_task=task, trusted_executors=trusted, expected_trust_context="org-b/prod")
        self.assertFalse(ok3)
        self.assertEqual(code3, "TRUST_CONTEXT_MISMATCH")

        # Untrusted executor -> UNTRUSTED_EXECUTOR
        ok4, code4, pv4 = SP.receive_result(res, expected_task=task, trusted_executors=set())
        self.assertFalse(ok4)
        self.assertEqual(code4, "UNTRUSTED_EXECUTOR")
        self.assertEqual(pv4.authenticity, "UNTRUSTED")

        # Tampered signature -> BAD_SIGNATURE
        res_tampered = SP.SporeResult(**{**res.__dict__, "sig": "00" * 64})
        ok5, code5, pv5 = SP.receive_result(res_tampered, expected_task=task, trusted_executors=trusted)
        self.assertFalse(ok5)
        self.assertEqual(code5, "BAD_SIGNATURE")
        self.assertEqual(pv5.integrity, "FAILED")

    def test_09_refuses_native_code_and_ungranted_capabilities(self):
        """AS-8: native runtime or ungranted capability is refused before any fetch or execution."""
        fetch_calls = []
        root_h, atoms, _ = _build_nested_i_k(1)

        def spy_fetch(h):
            fetch_calls.append(h)
            return atoms.get(h)

        ex = SP.SporeExecutor(_seed(9), local_atoms={}, remote_fetch=spy_fetch)
        native_task = SP.TaskSpec("bad", V.H_LENS_KERNEL_V2.hex(), "native/python", root_h.hex(), ())
        r_nat, c_nat = ex.execute(native_task, SP.Budget(atp=50, fetches=5, spawns=0, depth=0))
        self.assertEqual(r_nat.outcome, "REFUSED")
        self.assertTrue((r_nat.partiality.stop_reason or "").startswith("UNSUPPORTED_RUNTIME:"))
        self.assertIsNone(c_nat)
        self.assertEqual(fetch_calls, [])

        cap_task = SP.TaskSpec("bad2", V.H_LENS_KERNEL_V2.hex(), "book1/sigma-resume", root_h.hex(), (),
                               capabilities=("fetch_by_hash", "raw_network"))
        r_cap, c_cap = ex.execute(cap_task, SP.Budget(atp=50, fetches=5, spawns=0, depth=0))
        self.assertEqual(r_cap.outcome, "REFUSED")
        self.assertTrue((r_cap.partiality.stop_reason or "").startswith("CAPABILITY_REFUSED:"))
        self.assertIsNone(c_cap)
        self.assertEqual(fetch_calls, [])

    def test_10_deterministic_across_independent_executors(self):
        """AS-8: two independent executors with the same spore and budget reach identical state and spent ATP."""
        root_h, atoms, _ = _build_nested_i_k(3)
        task = SP.TaskSpec("det", V.H_LENS_KERNEL_V2.hex(), "book1/sigma-resume", root_h.hex(), ())
        b = SP.Budget(atp=2, fetches=0, spawns=0, depth=0)
        ex1 = SP.SporeExecutor(_seed(10), local_atoms=atoms)
        ex2 = SP.SporeExecutor(_seed(11), local_atoms=atoms)
        r1, c1 = ex1.execute(task, b)
        r2, c2 = ex2.execute(task, b)
        self.assertEqual(c1.state_bytes_hex, c2.state_bytes_hex)
        self.assertEqual(c1.spent_atp, c2.spent_atp)
        self.assertEqual(r1.outcome, r2.outcome)
        self.assertEqual(r1.nf_term_hash, r2.nf_term_hash)

    def test_11_end_to_end_three_agent_handover_and_counterexample_revision(self):
        """AGENT-SPORE-DIRECTION.md end-to-end experiment:
        Agent A hands minimal spore -> Agent B (small budget) fetches needed atoms and returns paused checkpoint ->
        Agent C verifies context, resumes without recomputing B's work to NORMAL_FORM ->
        Counterexample arrives on a dependency -> C revises dependent conclusion while keeping prior result."""
        root_h, atoms, chain = _build_nested_i_k(4)
        # Measure full ATP needed from scratch first
        scratch_ex = SP.SporeExecutor(_seed(99), local_atoms=atoms)
        task = SP.TaskSpec(
            subject="exp/3-agent-handover",
            rules_hash=V.H_LENS_KERNEL_V2.hex(),
            runtime="book1/sigma-resume",
            input_term_hash=root_h.hex(),
            env_hashes=(),
            expected_nf_hash=V.H_K.hex(),
        )
        r_full, _ = scratch_ex.execute(task, SP.Budget(atp=500, fetches=0, spawns=0, depth=0))
        self.assertEqual(r_full.outcome, "NORMAL_FORM")
        total_atp_needed = r_full.spent_atp
        self.assertGreater(total_atp_needed, 1)

        # Remote store holds the needed atoms (plus unrelated atoms that B must never fetch)
        remote = SP.ContentStore(atoms)
        unrelated_h = remote.put(b"unrelated-graph-branch-payload-never-fetched")

        seed_b, seed_c = _seed(21), _seed(22)
        pub_b = V.ed25519_pubkey(seed_b).hex()

        # Agent B: minimal starting atoms (empty!), small ATP budget (< total_atp_needed)
        small_atp = max(1, total_atp_needed // 2)
        agent_b = SP.SporeExecutor(seed_b, local_atoms={}, remote_fetch=remote.get_raw, trust_context="mesh/v1")
        res_b, ckpt_b = agent_b.execute(task, SP.Budget(atp=small_atp, fetches=10, spawns=0, depth=0))
        self.assertEqual(res_b.outcome, "NOT_ASSESSED")
        self.assertEqual(ckpt_b.stop_reason, "ATP_EXHAUSTED")
        self.assertGreater(res_b.spent_atp, 0)
        self.assertLess(res_b.spent_atp, total_atp_needed)
        self.assertEqual(res_b.spent_fetches, 4)
        self.assertNotIn(unrelated_h.hex(), res_b.deps_used)

        # Agent C: trusts B, receives B's checkpoint + fetched atoms, resumes without recomputing B's spent ATP
        agent_c = SP.SporeExecutor(
            seed_c,
            local_atoms=dict(agent_b.local_atoms),
            remote_fetch=remote.get_raw,
            trust_context="mesh/v1",
            trusted_executors={pub_b, V.ed25519_pubkey(seed_c).hex()},
        )
        ok_b, code_b, pv_b = SP.receive_result(res_b, expected_task=task, trusted_executors={pub_b}, expected_trust_context="mesh/v1")
        self.assertTrue(ok_b)
        self.assertEqual(code_b, "OK")
        self.assertEqual(pv_b.history_link, "WITNESSED")

        res_c, ckpt_c = agent_c.execute(task, SP.Budget(atp=total_atp_needed, fetches=0, spawns=0, depth=0), resume_from=ckpt_b)
        self.assertEqual(res_c.outcome, "NORMAL_FORM")
        self.assertEqual(res_c.nf_term_hash, V.H_K.hex())
        self.assertEqual(res_c.spent_fetches, 0)
        # Zero recomputation of B's work: B's spent + C's spent == total from scratch!
        self.assertEqual(res_b.spent_atp + res_c.spent_atp, total_atp_needed)
        self.assertLess(res_c.spent_atp, total_atp_needed)
        # Honest provenance: C resumed from B's checkpoint -> WITNESSED + CONDITIONAL + ckpt_b named
        self.assertEqual(res_c.partiality.history_link, "WITNESSED")
        self.assertEqual(res_c.partiality.reliance, "CONDITIONAL")
        self.assertIn(ckpt_b.checkpoint_id, res_c.taken_on_witness)

        # AS-6: Counterexample arrives on inner dependency chain[0] -> C revises dependent conclusion
        prior_id = res_c.result_id
        dep_graph = {
            task.task_id: [chain[3].hex()],
            chain[3].hex(): [chain[2].hex()],
            chain[2].hex(): [chain[1].hex()],
            chain[1].hex(): [chain[0].hex()],
        }
        rev = SP.revise_on_counterexample(res_c, chain[0].hex(), dep_graph)
        self.assertEqual(rev.status, "REASSESS_REQUIRED")
        self.assertEqual(rev.prior_result_id, prior_id)
        self.assertEqual(rev.causal_path[0], chain[0].hex())
        self.assertEqual(rev.causal_path[-1], task.task_id)
        self.assertEqual(len(rev.causal_path), 5)
        # Prior result stayed immutable history
        self.assertEqual(res_c.result_id, prior_id)
        # Unrelated counterexample -> UNAFFECTED
        rev_ok = SP.revise_on_counterexample(res_c, unrelated_h.hex(), dep_graph)
        self.assertEqual(rev_ok.status, "UNAFFECTED")

    def test_12_child_spore_composition_never_inflates_partiality(self):
        """AS-2 & AS-4: composing a complete parent with a partial child keeps parent PARTIAL & propagates deps."""
        root_h, atoms, chain = _build_nested_i_k(2)
        ex = SP.SporeExecutor(_seed(30), local_atoms=atoms)
        # Child with missing dependency -> PARTIAL
        missing_dep = V.sha256(b"child-missing-dep")
        child_task = SP.TaskSpec("child", V.H_LENS_KERNEL_V2.hex(), "book1/sigma-resume", root_h.hex(), (),
                                 required_deps=(missing_dep.hex(),))
        parent_b = SP.Budget(atp=100, fetches=5, spawns=2, depth=2)
        child_b = SP.Budget(atp=30, fetches=1, spawns=0, depth=1)
        parent_rem = parent_b.spawn_partition(child_b)
        child_res, _ = ex.execute(child_task, child_b)
        self.assertEqual(child_res.partiality.slice_completeness, "PARTIAL")

        parent_task = SP.TaskSpec("parent", V.H_LENS_KERNEL_V2.hex(), "book1/sigma-resume", root_h.hex(), ())
        parent_res, _ = ex.execute(parent_task, parent_rem, child_results=(child_res,))
        self.assertEqual(parent_res.partiality.slice_completeness, "PARTIAL")
        self.assertEqual(parent_res.partiality.history_link, "WITNESSED")
        self.assertIn(missing_dep.hex(), parent_res.deps_used)
        rev = SP.revise_on_counterexample(parent_res, missing_dep.hex())
        self.assertEqual(rev.status, "REASSESS_REQUIRED")


# ---------------------------------------------------------------- Curated Spore Mutants (--mutants)

MUTANTS = [
    ("SP-M1", "if child.atp > self.atp:", "if False:", "test_04_budget_conservation_and_bounded_recursion"),
    ("SP-M2", "if child.depth > self.depth - 1:", "if False:", "test_04_budget_conservation_and_bounded_recursion"),
    ("SP-M3", "if V.sha256(got) != h:", "if False:", "test_03_corrupted_fetch_fails_integrity"),
    ("SP-M4", "if task.runtime not in ALLOWED_RUNTIMES:", "if False:", "test_09_refuses_native_code_and_ungranted_capabilities"),
    ("SP-M5", "if ungranted:", "if False:", "test_09_refuses_native_code_and_ungranted_capabilities"),
    ("SP-M6", 'hl = "WITNESSED" if self.history_link == "VERIFIED_HERE" else self.history_link',
     "hl = self.history_link", "test_07_partiality_lattice_and_no_retelling_inflation"),
    ("SP-M7", 'rel = "CONDITIONAL" if self.reliance == "RELIABLE" else self.reliance',
     "rel = self.reliance", "test_07_partiality_lattice_and_no_retelling_inflation"),
    ("SP-M8", "if not result.verify_signature():", "if False:", "test_08_receive_result_refuses_context_substitution_and_bad_sig"),
    ("SP-M9", "if result.task_id != expected_task.task_id:", "if False:", "test_08_receive_result_refuses_context_substitution_and_bad_sig"),
    ("SP-M10", "if expected_trust_context is not None and result.trust_context != expected_trust_context:",
     "if False:", "test_08_receive_result_refuses_context_substitution_and_bad_sig"),
    ("SP-M11", "if result.executor_pub not in trusted_executors:", "if False:",
     "test_08_receive_result_refuses_context_substitution_and_bad_sig"),
    ("SP-M12", "if path is not None:", "if False:", "test_11_end_to_end_three_agent_handover_and_counterexample_revision"),
]


def run_mutants() -> int:
    src_path = ROOT / "spore.py"
    orig = src_path.read_text(encoding="utf-8")
    # Baseline check: unmutated suite must pass first (BASELINE_RED guard)
    base = subprocess.run(
        [sys.executable, "-B", "-m", "unittest", "test_spore"],
        cwd=ROOT, capture_output=True, text=True, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
    )
    if base.returncode != 0:
        print("BASELINE_RED:\n" + base.stdout + base.stderr)
        return 2
    killed, survived = 0, []
    with tempfile.TemporaryDirectory(prefix="minds-spore-mutants-") as td:
        tmp = Path(td)
        shutil.copy2(ROOT / "test_spore.py", tmp / "test_spore.py")
        for mid, find, repl, test_name in MUTANTS:
            if orig.count(find) != 1:
                print(f"{mid} BAD_MUTANT: find occurred {orig.count(find)} times")
                survived.append(mid)
                continue
            (tmp / "spore.py").write_text(orig.replace(find, repl, 1), encoding="utf-8")
            env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1",
                   "PYTHONPATH": f"{tmp}{os.pathsep}{ROOT}"}
            p = subprocess.run(
                [sys.executable, "-B", "-m", "unittest", f"test_spore.TestSpores.{test_name}"],
                cwd=tmp, capture_output=True, text=True, env=env, timeout=60,
            )
            out = p.stdout + p.stderr
            if p.returncode != 0 and "AssertionError" in out:
                print(f"{mid} KILLED by {test_name}")
                killed += 1
            else:
                print(f"{mid} SURVIVED ({test_name}): rc={p.returncode}\n{out[-400:]}")
                survived.append(mid)
    print(f"spore mutants: {killed}/{len(MUTANTS)} killed")
    return 0 if not survived else 1


if __name__ == "__main__":
    if "--mutants" in sys.argv:
        sys.exit(run_mutants())
    unittest.main()
