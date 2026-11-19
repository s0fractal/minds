#!/usr/bin/env python3
"""Tests & surgical mutant harness for `coalition.py` and `proofs/Vars1/Coalition.lean` (`CV01..CV11`).

    python3 test_coalition.py
"""
import importlib.util
from pathlib import Path
import tempfile
import unittest

import coalition as CO


class TestCoalition(unittest.TestCase):
    def test_cv01_f6_toy_countermodel_exact_separation(self):
        """CV01: Exact F6 separation: K_viab^∃ = {0,1,2,3} vs K_viab^⟨⟨C⟩⟩ = {0,1,2} with witness on state 3."""
        g, safe = CO.f6_toy_game()
        live, dead = CO.check_live_env(g)
        self.assertTrue(live)
        self.assertEqual(dead, [])
        bp = CO.blocking_power(g, safe)
        self.assertEqual(bp.get("angelic_viability"), ["0", "1", "2", "3"])
        self.assertEqual(bp.get("controllable_viability"), ["0", "1", "2"])
        self.assertEqual(bp.get("blocked_states"), ["3"])
        self.assertEqual(bp.get("blocking_count"), 1)
        w3 = bp.get("witnesses", {}).get("3", {}).get("act", {})
        self.assertEqual(w3.get("env_move"), "block")
        self.assertEqual(w3.get("exits_control_kernel_to"), ["4"])

    def test_cv02_live_env_prevents_vacuous_controllability(self):
        """CV02: Dead environment (zero successors) must NOT pass CPre vacuously when require_live=True."""
        g = CO.make_game(
            states=["a", "b"],
            act_ok={"a": ["go"], "b": ["go"]},
            env_ok={"a": [], "b": ["e"]},
            step={("b", "go", "e"): ["b"]},
        )
        live, dead = CO.check_live_env(g)
        self.assertFalse(live)
        self.assertEqual(dead, [("a", "go")])
        self.assertEqual(CO.cpre(g, {"a", "b"}, require_live=True), frozenset({"b"}))
        self.assertEqual(CO.controllable_viability(g, {"a", "b"}, require_live=True), frozenset({"b"}))
        self.assertIn("a", CO.cpre(g, {"a", "b"}, require_live=False))

    def test_cv03_controllable_reach_sub_angelic_reach(self):
        """CV03: Controllable reachability is strictly contained in angelic reachability when env can block."""
        g = CO.make_game(
            states=["start", "mid", "goal", "trap"],
            act_ok={"start": ["left", "right"], "mid": ["go"], "goal": ["stay"], "trap": ["stay"]},
            env_ok={"start": ["e1", "e2"], "mid": ["e1", "e2"], "goal": ["e1"], "trap": ["e1"]},
            step={
                ("start", "left", "e1"): ["goal"],
                ("start", "left", "e2"): ["trap"],
                ("start", "right", "e1"): ["mid"],
                ("start", "right", "e2"): ["mid"],
                ("mid", "go", "e1"): ["goal"],
                ("mid", "go", "e2"): ["goal"],
                ("goal", "stay", "e1"): ["goal"],
                ("trap", "stay", "e1"): ["trap"],
            },
        )
        g_weak = CO.make_game(
            states=g.states,
            act_ok={**g.act_ok, "start": frozenset({"left"})},
            env_ok=g.env_ok,
            step=g.step,
        )
        self.assertEqual(CO.controllable_reach(g, {"goal"}), frozenset({"start", "mid", "goal"}))
        self.assertEqual(CO.angelic_reach(g_weak, {"goal"}), frozenset({"start", "mid", "goal"}))
        self.assertEqual(CO.controllable_reach(g_weak, {"goal"}), frozenset({"mid", "goal"}))
        self.assertTrue(CO.controllable_reach(g_weak, {"goal"}) < CO.angelic_reach(g_weak, {"goal"}))
        self.assertTrue(CO.controllable_reach(g_weak, {"goal"}) <= CO.controllable_reach(g, {"goal"}))

    def test_cv04_policy_synthesis_and_independent_verification(self):
        """CV04: Synthesized survival policy passes independent verifier; sabotaged policy fails."""
        g, safe = CO.f6_toy_game()
        pol = CO.synthesize_survival_policy(g, safe)
        self.assertEqual(sorted(pol.keys()), ["0", "1", "2"])
        ok, info = CO.verify_survival_policy(g, safe, pol)
        self.assertTrue(ok)
        self.assertEqual(info.get("verified_states"), 3)
        bad_pol = {**pol, "3": "act"}
        ok_bad, info_bad = CO.verify_survival_policy(g, safe, bad_pol)
        self.assertFalse(ok_bad)
        self.assertEqual(info_bad.get("reason"), "ESCAPED_KERNEL")
        self.assertEqual(info_bad.get("state"), "3")
        ok_inadm, info_inadm = CO.verify_survival_policy(g, safe, {"0": "fly"})
        self.assertFalse(ok_inadm)
        self.assertEqual(info_inadm.get("reason"), "INADMISSIBLE_ACTION")

    def test_cv05_alternating_simulation_zero_dynamic_loss(self):
        """CV05: Faithful alternating simulation (quotient collapsing {0,1,2} -> 'safe') has zero dynamic loss."""
        g1, safe1 = CO.f6_toy_game()
        g2 = CO.make_game(
            states=["safe", "edge", "fail"],
            act_ok={"safe": ["act"], "edge": ["act"], "fail": ["act"]},
            env_ok={"safe": ["coop", "block"], "edge": ["coop", "block"], "fail": ["coop", "block"]},
            step={
                ("safe", "act", "coop"): ["safe"],
                ("safe", "act", "block"): ["safe"],
                ("edge", "act", "coop"): ["safe"],
                ("edge", "act", "block"): ["fail"],
                ("fail", "act", "coop"): ["fail"],
                ("fail", "act", "block"): ["fail"],
            },
        )
        phi = {"0": "safe", "1": "safe", "2": "safe", "3": "edge", "4": "fail"}
        rep = CO.translation_loss_report(g1, g2, phi, safe1, {"safe", "edge"})
        self.assertTrue(rep.get("alt_sim", {}).get("is_alt_sim"))
        self.assertEqual(rep.get("static_lost"), [])
        self.assertEqual(rep.get("lost_dyn_control_viab"), [])
        self.assertEqual(rep.get("lost_dyn_angelic"), [])
        self.assertTrue(rep.get("faithful_control_transport"))

    def test_cv06_f5_static_preserving_translation_catches_dynamic_loss(self):
        """CV06: F5 countermodel — translation preserves static safety yet drops reachability/viability."""
        g1 = CO.make_game(
            states=["a", "b"],
            act_ok={"a": ["go"], "b": ["go"]},
            env_ok={"a": ["e"], "b": ["e"]},
            step={("a", "go", "e"): ["b"], ("b", "go", "e"): ["a"]},
        )
        g2 = CO.make_game(
            states=["a", "b", "out"],
            act_ok={"a": ["go"], "b": ["go"], "out": ["go"]},
            env_ok={"a": ["e"], "b": ["e"], "out": ["e"]},
            step={("a", "go", "e"): ["b"], ("b", "go", "e"): ["out"], ("out", "go", "e"): ["out"]},
        )
        phi = {"a": "a", "b": "b"}
        rep = CO.translation_loss_report(g1, g2, phi, {"a", "b"}, {"a", "b"})
        self.assertEqual(rep.get("static_lost"), [])
        self.assertFalse(rep.get("alt_sim", {}).get("is_alt_sim"))
        self.assertIn(["b", "a"], rep.get("lost_dyn_angelic", []))
        self.assertEqual(rep.get("lost_dyn_control_viab"), ["a", "b"])
        self.assertFalse(rep.get("faithful_control_transport"))

    def test_cv07_partial_translation_and_spurious_reach(self):
        """CV07: Partial morphism reports uncovered states; extra transitions in g2 report introduced_dyn_angelic."""
        g1 = CO.make_game(
            states=["a", "b", "c"],
            act_ok={"a": ["stay"], "b": ["stay"], "c": ["stay"]},
            env_ok={"a": ["e"], "b": ["e"], "c": ["e"]},
            step={("a", "stay", "e"): ["a"], ("b", "stay", "e"): ["b"], ("c", "stay", "e"): ["c"]},
        )
        g2 = CO.make_game(
            states=["a", "b"],
            act_ok={"a": ["jump"], "b": ["stay"]},
            env_ok={"a": ["e"], "b": ["e"]},
            step={("a", "jump", "e"): ["b"], ("b", "stay", "e"): ["b"]},
        )
        rep = CO.translation_loss_report(g1, g2, {"a": "a", "b": "b"}, {"a", "b", "c"}, {"a", "b"})
        self.assertEqual(rep.get("uncovered_states"), ["c"])
        self.assertIn(["a", "b"], rep.get("introduced_dyn_angelic", []))
        self.assertFalse(rep.get("faithful_control_transport"))

    def test_cv08_spore_fuel_game_depletion_vs_replenishment(self):
        """CV08: Spore ATP fuel game — without guaranteed replenishment, controllable viability collapses to empty."""
        g_burn, safe_burn = CO.spore_fuel_game(max_atp=3, step_cost=1, replenish_delta=0)
        bp_burn = CO.blocking_power(g_burn, safe_burn)
        self.assertEqual(bp_burn.get("angelic_viability"), [])
        self.assertEqual(bp_burn.get("controllable_viability"), [])

        g_deny, safe_deny = CO.spore_fuel_game(max_atp=3, step_cost=1, replenish_delta=1, env_can_deny_replenish=True)
        bp_deny = CO.blocking_power(g_deny, safe_deny)
        self.assertEqual(bp_deny.get("angelic_viability"), ["atp_1", "atp_2", "atp_3"])
        self.assertEqual(bp_deny.get("controllable_viability"), [])
        self.assertEqual(bp_deny.get("blocked_states"), ["atp_1", "atp_2", "atp_3"])

        g_sov, safe_sov = CO.spore_fuel_game(max_atp=3, step_cost=1, replenish_delta=1, env_can_deny_replenish=False)
        bp_sov = CO.blocking_power(g_sov, safe_sov)
        self.assertEqual(bp_sov.get("controllable_viability"), ["atp_1", "atp_2", "atp_3"])
        self.assertEqual(bp_sov.get("blocked_states"), [])

    def test_cv09_certificate_determinism_and_content_addressing(self):
        """CV09: Viability certificates are deterministic and content-addressed (SHA-256)."""
        g, safe = CO.f6_toy_game()
        c1 = CO.viability_certificate(g, safe, label="f6")
        c2 = CO.viability_certificate(g, safe, label="f6")
        c3 = CO.viability_certificate(g, safe, label="f6-other")
        self.assertEqual(c1.get("digest"), c2.get("digest"))
        self.assertEqual(len(c1.get("digest", "")), 64)
        self.assertNotEqual(c1.get("digest"), c3.get("digest"))
        self.assertTrue(c1.get("certificate", {}).get("policy_verified"))

    def test_cv10_make_game_rejects_malformed_inputs(self):
        """CV10: make_game fails closed on empty states or transitions leaving state space."""
        with self.assertRaises(ValueError):
            CO.make_game([], {}, {}, {})
        with self.assertRaises(ValueError):
            CO.make_game(["a"], {"a": ["go"]}, {"a": ["e"]}, {("a", "go", "e"): ["ghost"]})

    def test_cv11_mutants_all_killed_on_assertion(self):
        """CV11: Surgical mutants of coalition.py (8 guards) all fail on assertion (not crash)."""
        src_path = Path(__file__).resolve().parent / "coalition.py"
        orig = src_path.read_text(encoding="utf-8")
        mutants = [
            ("CV-M1-live-check", "            if not has_succ:", "            if False:",
             "test_cv02_live_env_prevents_vacuous_controllability"),
            ("CV-M2-cpre-all-env", "                    if not (succs <= target):", "                    if False:",
             "test_cv01_f6_toy_countermodel_exact_separation"),
            ("CV-M3-cpre-require-live",
             "            if ok and (not require_live or saw_succ):\n                out.add(s)",
             "            if ok:\n                out.add(s)",
             "test_cv02_live_env_prevents_vacuous_controllability"),
            ("CV-M4-viab-gfp", "        nxt = cur & cpre(game, cur, require_live=require_live)", "        nxt = cur",
             "test_cv01_f6_toy_countermodel_exact_separation"),
            ("CV-M5-policy-escape", "                if escaped:", "                if False:",
             "test_cv04_policy_synthesis_and_independent_verification"),
            ("CV-M6-altsim-reflect", "                        if s2p not in g1_succ_images:", "                        if False:",
             "test_cv06_f5_static_preserving_translation_catches_dynamic_loss"),
            ("CV-M7-lost-dyn-ang", "            if r1 and not r2:", "            if False:",
             "test_cv06_f5_static_preserving_translation_catches_dynamic_loss"),
            ("CV-M8-lost-dyn-ctrl", "    lost_dyn_ctrl = sorted(s for s in dom if s in cv1 and phi[s] not in cv2)",
             "    lost_dyn_ctrl = []",
             "test_cv06_f5_static_preserving_translation_catches_dynamic_loss"),
        ]
        for mid, find, repl, test_name in mutants:
            self.assertEqual(orig.count(find), 1, f"{mid}: find must match uniquely")
            mutated = orig.replace(find, repl, 1)
            with tempfile.TemporaryDirectory() as td:
                mp = Path(td) / "coalition.py"
                mp.write_text(mutated, encoding="utf-8")
                spec = importlib.util.spec_from_file_location("_coalition_mut", mp)
                mod = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(mod)
                saved = globals()["CO"]
                globals()["CO"] = mod
                try:
                    res = unittest.TestResult()
                    TestCoalition(test_name).run(res)
                finally:
                    globals()["CO"] = saved
                self.assertEqual(len(res.errors), 0, f"{mid} crashed instead of failing assertion: {res.errors}")
                self.assertEqual(len(res.failures), 1, f"{mid} SURVIVED {test_name}!")


if __name__ == "__main__":
    unittest.main()
