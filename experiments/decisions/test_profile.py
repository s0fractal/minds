#!/usr/bin/env python3
"""Tests of `profile.py` (the decision profile lens).

    .venv/bin/python experiments/decisions/test_profile.py [-v]

Test 01 builds one chain through the gate with a goal for each kind of tension, and one for none, and checks what the
lens names: the kind, the evidence, the trajectories, the blast radius, the budget, and that a recorded precedent
silences what it resolved and nothing else. Test 02 is silence: two healthy goals beside a hundred cells that do not
touch them (unsettled decisions, verdicts that disagree, fragile quorums, killed cells), and readings on both; the
lens names no tension, lists every reading on the background silent, and the gate confirms that no silent reading
moves a goal. Test 03 runs the lens on the live chain.
"""
import itertools
import json
import os
import sys
import time
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))
import vars1 as V  # noqa: E402
import fold as F  # noqa: E402
import profile as PF  # noqa: E402
import test_decisions as TD  # noqa: E402

SCOPE = TD.SCOPE


class Chain(TD.Chain):
    """`test_decisions`' chain, with INVALID verdicts, notices, and cells sealed by several members."""

    def invalid(self, on: V.Cell, name: str, verifier: str) -> V.Cell:
        self.atoms[V.H_VERDICT_INVALID] = V.atom_utf8("INVALID")
        return V.Cell(V.H_SCHEMA["verdict"], self.put(self.atoms, V.atom_utf8(f"{SCOPE}/{name}")), on.id,
                      h_attests=self.put(self.atoms, V.atom_hvec([on.id])),
                      slots=(V.H_EMPTY, V.H_VERDICT_INVALID, self.put(self.atoms, V.atom_utf8(verifier))))

    def notice(self, name: str, target: V.Cell) -> V.Cell:
        return V.Cell(V.H_SCHEMA["axiom"], self.put(self.atoms, V.atom_utf8(f"{SCOPE}/{name}")),
                      self.put(self.atoms, V.atom_utf8(name)),
                      h_invalidates=self.put(self.atoms, V.atom_hvec([target.id])))

    def fallback(self, name: str) -> V.Cell:
        """A decision with no policy of its own: it reads the governing scope's admission policy."""
        return V.Cell(V.H_SCHEMA["decision"], self.put(self.atoms, V.atom_utf8(f"{SCOPE}/{name}")),
                      self.put(self.atoms, V.atom_utf8(name)), slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, V.H_EMPTY))

    def wide(self, name: str, thr: int, keys) -> V.Cell:
        """A decision whose own policy is `thr` of `keys`."""
        pol = self.put(self.atoms, V.atom_pol1(thr, self.put(self.atoms, V.atom_hvec(sorted(keys)))))
        return V.Cell(V.H_SCHEMA["decision"], self.put(self.atoms, V.atom_utf8(f"{SCOPE}/{name}")),
                      self.put(self.atoms, V.atom_utf8(name)), slots=(V.H_PROVISIONAL, V.H_EMPTY, V.H_EMPTY, pol))

    def rotate(self, thr: int, keys=None) -> None:
        """Supersede the scope by one whose rosters are `thr` of `keys` (the three members by default), sealed by ana
        under the governing scope; under v1 it governs from the next commit, whose seals are made under it."""
        keys = sorted(keys or [self.pk[m] for m in TD.MEMBERS])
        pol = self.put(self.atoms, V.atom_pol1(thr, self.put(self.atoms, V.atom_hvec(keys))))
        s1 = V.Cell(V.H_SCHEMA["scope"], self.put(self.atoms, V.atom_utf8(f"{SCOPE}/SCOPE")),
                    self.put(self.atoms, V.atom_utf8(f"rotation/{thr}/{len(keys)}")),
                    h_supersedes=self.put(self.atoms, V.atom_hvec([self.scope.id])),
                    h_loss=self.put(self.atoms, V.atom_utf8("rotation")), slots=(pol, pol, self.scope.slots[2]))
        self.commit((s1, "ana"))
        self.scope = s1

    def commit(self, *pairs) -> str:
        cells = list({c.id: c for c, _ in pairs}.values())
        seals = [V.Seal.sign(self.sk[m], c.id, self.scope.id) for c, ms in pairs
                 for m in ((ms,) if isinstance(ms, str) else ms)]
        tip = self.repo.build_candidate_commit(SCOPE, self.atoms, cells, seals, parent_commit=self.tip)
        self.repo.admit_and_advance(SCOPE, tip, expected_old=self.tip)
        self.tip, self.atoms = tip, {}
        return tip


def profile(goals, **kw) -> dict:
    return {"format": PF.PROFILE, "goals": [g.id.hex() for g in goals], **kw}


def by_goal(out) -> dict:
    kinds: dict = {}
    for t in out["tensions"]:
        kinds.setdefault(t["target_goal"], []).append(t["kind"])
    return {g: sorted(k) for g, k in kinds.items()}


class T(unittest.TestCase):
    def test_01_the_lens_names_four_kinds_of_tension(self):
        """Goals under a profile that asks for two withdrawals: gF (1 of 3, one verdict: FRAGILITY), gS (1 of 3, two
        verdicts: none), gH (relies on gF, one verdict: FRAGILITY; gF's blast radius is 2), gI1 (3 of 3, two verdicts:
        INCOMPLETENESS, one way to close it, a missing fact), gI2 (2 of 3, no verdict: INCOMPLETENESS, three ways, a
        missing criterion), gC (an ATTESTED and an INVALID verdict under other verifier ids: CONTRADICTION, and fragile),
        gN (a notice kills it: CONTRADICTION, not live), gE1 (Settled, relying on gE0 that no one attested:
        INCOMPLETENESS of its support), gP (3 of 3, no verdict at `since`, two after: UNREALIZED_POSSIBILITY); an
        obligation oK that a notice kills (CONTRADICTION). A budget of one step leaves gI2 out of budget. A precedent
        silences gI2's tension and no other; with other evidence it would ask again."""
        c = Chain()
        mk = lambda n, thr, relies=(): c.decision(f"decision/{n}", thr, relies)  # noqa: E731
        gF, gS, gI1, gI2, gC, gN, gE0, gP, oK = (mk("gF", 1), mk("gS", 1), mk("gI1", 3), mk("gI2", 2), mk("gC", 1),
                                                  mk("gN", 1), mk("gE0", 1), mk("gP", 3), mk("oK", 1))
        c.commit(*((x, "ana") for x in (gF, gS, gI1, gI2, gC, gN, gE0, gP, oK)))
        gH, gE1 = mk("gH", 1, [gF]), mk("gE1", 1, [gE0])
        v = lambda d, who: c.verdict(d, f"decision/{d.id.hex()[:6]}/by-{who}", who)  # noqa: E731
        yes, no = v(gC, "ana"), c.invalid(gC, "decision/gC/no-by-bo", "bo")
        c.commit((gH, "ana"), (gE1, "ana"), (v(gF, "ana"), "ana"), (v(gS, "ana"), "ana"), (v(gS, "bo"), "bo"),
                 (v(gH, "bo"), "bo"), (v(gI1, "ana"), "ana"), (v(gI1, "bo"), "bo"), (yes, "ana"), (no, "bo"),
                 (v(gN, "ana"), "ana"), (v(gE1, "ana"), "ana"), (v(oK, "ana"), "ana"))
        since = c.tip
        c.commit((v(gP, "ana"), "ana"), (v(gP, "bo"), "bo"), (c.notice("notice/gN", gN), "ana"),
                 (c.notice("notice/oK", oK), "ana"))
        goals = [gF, gS, gH, gI1, gI2, gC, gN, gE1, gP]
        prof = profile(goals, obligations=[oK.id.hex()], preferences={"min_cut_threshold": 2})
        out = PF.filter_tensions(c.repo, SCOPE, prof, since=since)
        h = lambda x: x.id.hex()  # noqa: E731
        self.assertEqual(by_goal(out), {
            h(gF): ["FRAGILITY"], h(gH): ["FRAGILITY"], h(gI1): ["INCOMPLETENESS"], h(gI2): ["INCOMPLETENESS"],
            h(gC): ["CONTRADICTION", "FRAGILITY"], h(gN): ["CONTRADICTION"], h(gE1): ["INCOMPLETENESS"],
            h(gP): ["UNREALIZED_POSSIBILITY"], h(oK): ["CONTRADICTION"]})
        t = {(x["target_goal"], x["kind"]): x for x in out["tensions"]}
        self.assertEqual((t[(h(gF), "FRAGILITY")]["blast_radius_on_goals"], t[(h(gH), "FRAGILITY")]["blast_radius_on_goals"]),
                         (2, 1))
        fact, criterion = t[(h(gI1), "INCOMPLETENESS")], t[(h(gI2), "INCOMPLETENESS")]
        self.assertEqual((fact["evidence_gap"], fact["competing_trajectories"]),
                         ([c.pk["cy"].hex()], [{"keys": [c.pk["cy"].hex()]}]))
        self.assertIn("missing fact", fact["question_prompt"])
        self.assertEqual((len(criterion["competing_trajectories"]), criterion["detail"]["trajectories"]), (3, 3))
        self.assertIn("missing criterion", criterion["question_prompt"])
        self.assertEqual(t[(h(gE1), "INCOMPLETENESS")]["evidence_gap"], [h(gE0)])
        self.assertEqual(t[(h(gP), "UNREALIZED_POSSIBILITY")]["detail"], {"deficit": 1, "deficit_before": 3,
                                                                        "trajectories": 1})
        self.assertEqual(t[(h(gC), "CONTRADICTION")]["evidence_gap"], sorted([h(yes), h(no)]))
        self.assertEqual(t[(h(gN), "CONTRADICTION")]["detail"], {"reason": "goal not live"})
        self.assertEqual(t[(h(oK), "CONTRADICTION")]["detail"], {"reason": "obligation not live"})
        # a budget of one step: gI2 is two keys away, out of budget, not a question
        tight = PF.filter_tensions(c.repo, SCOPE, {**prof, "max_deficit": 1}, since=since)
        self.assertEqual(tight["over_budget"], [h(gI2)])
        self.assertNotIn(h(gI2), by_goal(tight))
        # a precedent silences what it resolved, and nothing else
        resolved = PF.record_resolution(prof, criterion, {"keys": criterion["competing_trajectories"][0]["keys"]})
        self.assertEqual(prof.get("precedents"), None)  # the profile given is not changed
        again = PF.filter_tensions(c.repo, SCOPE, resolved, since=since)
        self.assertEqual(again["suppressed"], [criterion["signature"]])
        self.assertEqual(len(again["tensions"]), len(out["tensions"]) - 1)
        self.assertNotIn(h(gI2), by_goal(again))
        # a profile that reads two ways is refused
        with self.assertRaises(PF.Bad):
            PF.read_profile(b'{"format": "minds.decisions.profile@1", "goals": [], "goals": []}')
        with self.assertRaises(PF.Bad):
            PF.check_profile({**prof, "preferences": {"min_cut_threshold": 0}})

    def test_04_a_resolution_holds_only_under_its_conditions(self):
        """A precedent stays in force only while what its tension was judged under is unchanged. gF (its own policy, 1
        of 3, one verdict) is FRAGILITY under a minimum cut of 2, gD (the scope's policy, 1 of 3, no verdict)
        INCOMPLETENESS; both are resolved, and the same profile then asks nothing. Under a minimum cut of 3 the lens
        asks of gF again, with the same evidence, and not of gD; after the scope rotates to 2 of 3, it asks of gD again
        (the same three keys missing, now two of them needed), and not of gF, whose policy is its own."""
        c = Chain()
        gF, gD = c.decision("decision/gF", 1), c.fallback("decision/gD")
        c.commit((gF, "ana"), (gD, "ana"))
        c.commit((c.verdict(gF, "decision/gF/by-ana", "ana"), "ana"))
        h = lambda x: x.id.hex()  # noqa: E731
        prof = profile([gF, gD], preferences={"min_cut_threshold": 2})
        out = PF.filter_tensions(c.repo, SCOPE, prof)
        self.assertEqual(by_goal(out), {h(gF): ["FRAGILITY"], h(gD): ["INCOMPLETENESS"]})
        resolved = prof
        for t in out["tensions"]:
            resolved = PF.record_resolution(resolved, t, "accepted")
        self.assertEqual(PF.filter_tensions(c.repo, SCOPE, resolved)["tensions"], [])
        stricter = PF.filter_tensions(c.repo, SCOPE, {**resolved, "preferences": {"min_cut_threshold": 3}})
        self.assertEqual(by_goal(stricter), {h(gF): ["FRAGILITY"]})
        self.assertEqual({t["kind"]: t["evidence_gap"] for t in stricter["tensions"]},
                         {t["kind"]: t["evidence_gap"] for t in out["tensions"] if t["target_goal"] == h(gF)})
        c.rotate(2)
        rotated = PF.filter_tensions(c.repo, SCOPE, resolved)
        self.assertEqual(by_goal(rotated), {h(gD): ["INCOMPLETENESS"]})
        self.assertEqual(rotated["tensions"][0]["detail"]["deficit"], 2)

    def test_05_trajectories_cost_what_is_shown(self):
        """A roster rotated to six keys and a decision under its own policy, 3 of the 6, with no verdict: twenty sets of
        three keys would close it. The lens counts them (`trajectories`: 20) and draws from the generator only the eight it
        lists, so the cost does not grow with the number of ways."""
        c = Chain()
        keys = [c.pk[m] for m in ("ana", "bo", "cy", "dee")] + [V.ed25519_pubkey(bytes([i]) * 32) for i in (7, 8)]
        c.rotate(1, keys)
        gW = c.wide("decision/gW", 3, keys)
        c.commit((gW, "ana"))
        real, drawn = itertools.combinations, [0]

        def counting(*args):
            for x in real(*args):
                drawn[0] += 1
                yield x
        with mock.patch.object(PF.itertools, "combinations", counting):
            out = PF.filter_tensions(c.repo, SCOPE, profile([gW]))
        t = out["tensions"][0]
        self.assertEqual((t["kind"], t["detail"]["trajectories"], len(t["competing_trajectories"])),
                         ("INCOMPLETENESS", 20, PF.TRAJECTORIES))
        self.assertLessEqual(drawn[0], PF.TRAJECTORIES)

    def test_02_absolute_silence(self):
        """Two goals, each Grounded with a key to spare, and a hundred cells that touch neither: decisions no one
        attested, verdicts that disagree, quorums of one, cells notices kill. The lens names no tension
        (`len(tensions) == 0`), though a profile of the background would name many. Readings: every one on the
        background is silent, the two on a goal are loud with that goal; and the gate (`fold.py`) finds that no silent
        reading changes a goal's Settled or Grounded (`Silence.lean`, `silence_outside_reads`)."""
        c = Chain()
        g1, g2 = c.decision("decision/g1", 1), c.decision("decision/g2", 1)
        c.commit((g1, "ana"), (g2, "ana"))
        c.commit(*((c.verdict(g, f"decision/{n}/by-{m}", m), m) for g, n in ((g1, "g1"), (g2, "g2")) for m in ("ana", "bo")))
        bg = []
        axioms = [c.axiom(f"bg/axiom/{i}") for i in range(30)]
        open_ = [c.decision(f"bg/open/{i}", 2, [axioms[i]]) for i in range(30)]
        c.commit(*((x, "ana") for x in axioms + open_))
        bg += axioms + open_
        fragile = [c.decision(f"bg/fragile/{i}", 1) for i in range(10)]
        c.commit(*((x, "ana") for x in fragile))
        verdicts = [c.verdict(d, f"bg/fragile/{i}/by-cy", "cy") for i, d in enumerate(fragile)]
        disagree = [c.invalid(d, f"bg/fragile/{i}/no-by-bo", "bo") for i, d in enumerate(fragile[:5])]
        notices = [c.notice(f"bg/notice/{i}", axioms[i]) for i in range(15)]
        c.commit(*((x, "cy") for x in verdicts), *((x, "bo") for x in disagree), *((x, "ana") for x in notices))
        bg += fragile + verdicts + disagree + notices
        self.assertEqual(len(bg), 100)
        prof = profile([g1, g2], preferences={"min_cut_threshold": 2})
        self.assertEqual(PF.filter_tensions(c.repo, SCOPE, prof)["tensions"], [])
        noisy = PF.filter_tensions(c.repo, SCOPE, profile(open_ + fragile, preferences={"min_cut_threshold": 2}))
        self.assertGreater(len(noisy["tensions"]), 30)
        pk = lambda m: c.pk[m].hex()  # noqa: E731
        cands = []
        for i, x in enumerate(open_[:8] + fragile[:4]):
            cands.append({"id": f"att{i}", "keys": [pk("bo")],
                          "acts": [{"act": "verdict", "on": x.id.hex(), "code": "ATTESTED", "verifier": f"r{i}"}]})
        for i, x in enumerate(axioms[15:21] + verdicts[:2]):
            cands.append({"id": f"kill{i}", "keys": [pk("ana")],
                          "acts": [{"act": "notice", "edge": "invalidates", "target": x.id.hex()}]})
        cands.append({"id": "seal", "keys": [pk("cy")], "acts": [{"act": "seal", "target": verdicts[3].id.hex()}]})
        cands.append({"id": "none", "keys": [pk("cy")], "acts": [{"act": "none"}]})
        cands.append({"id": "on-g1", "keys": [pk("ana")], "acts": [{"act": "notice", "edge": "invalidates",
                                                                    "target": g1.id.hex()}]})
        cands.append({"id": "on-g2", "keys": [pk("bo")], "acts": [{"act": "verdict", "on": g2.id.hex(), "code": "INVALID",
                                                                   "verifier": "bo"}]})
        out = PF.filter_tensions(c.repo, SCOPE, prof, candidates=cands)
        self.assertEqual(out["tensions"], [])
        self.assertEqual(out["candidates"]["loud"], {"on-g1": [g1.id.hex()], "on-g2": [g2.id.hex()]})
        self.assertEqual(len(out["candidates"]["silent"]), len(cands) - 2)
        gate = F.fold_candidates(c.repo, SCOPE, [x for x in cands if x["id"] in out["candidates"]["silent"]])
        goals = {g1.id.hex(), g2.id.hex()}
        for row in gate["candidates"]:
            self.assertFalse(goals & set(row["flips"] or {}), row["id"])
        moved = {r["id"]: r for r in F.fold_candidates(c.repo, SCOPE, [x for x in cands if x["id"] == "on-g1"])["candidates"]}
        self.assertEqual(moved["on-g1"]["flipped_grounded"], [g1.id.hex()])

    def test_03_the_live_chain(self):
        """On refs/vars/heads/minds, a profile of every decision, held to the lens itself rather than to a count of the
        day: under `min_cut_threshold` 1 the profile names exactly the decisions the lens does not hold Settled and
        Grounded, each an INCOMPLETENESS (a release between its record and a second member's verdict, say), and
        nothing else; under 2 it adds a FRAGILITY for exactly the Grounded decisions at margin 0 (endorsers counted
        by Pass 3 equal to the threshold). Until 2026-11-13 this asserted silence under 1, which a release recorded
        and not yet witnessed turned red on every push in that window. A profile of five decisions lists
        silent the readings that touch none of them, and the gate confirms ten of those change none. Skipped when
        the chain is not fetched, unless MINDS_REQUIRE_CHAIN=1."""
        repo = V.GitVarsRepo(ROOT)
        if repo.ref_commit("minds") is None:
            if os.environ.get("MINDS_REQUIRE_CHAIN") == "1":
                self.fail("refs/vars/heads/minds is not fetched, and MINDS_REQUIRE_CHAIN=1 requires it")
            self.skipTest("refs/vars/heads/minds is not fetched in this clone")
        lens = repo.lens("minds")
        cells, atoms = lens["cells"], lens["atoms"]
        ds = sorted(x for x, y in cells.items() if y.h_schema == V.H_SCHEMA["decision"])
        prof = {"format": PF.PROFILE, "goals": [d.hex() for d in ds]}
        t0 = time.perf_counter()
        quiet = PF.filter_tensions(repo, "minds", {**prof, "preferences": {"min_cut_threshold": 1}})
        loud = PF.filter_tensions(repo, "minds", {**prof, "preferences": {"min_cut_threshold": 2}})
        self.assertLess(time.perf_counter() - t0, 30.0)
        held = [d for d in ds if lens["settled"].get(d) and lens["grounded"].get(d)]
        short = [d.hex() for d in ds if d not in held]
        margin0 = [d.hex() for d in held if len(lens["endorsers"][d]) == lens["evaluators"][d][0]]
        self.assertGreater(len(held), 40)  # the live chain holds its releases: an empty `held` would pass vacuously
        self.assertEqual(sorted((t["kind"], t["target_goal"]) for t in quiet["tensions"]),
                         [("INCOMPLETENESS", g) for g in short])
        self.assertEqual(sorted(t["target_goal"] for t in loud["tensions"] if t["kind"] == "FRAGILITY"), margin0)
        self.assertEqual(sorted((t["kind"], t["target_goal"]) for t in loud["tensions"] if t["kind"] != "FRAGILITY"),
                         [("INCOMPLETENESS", g) for g in short])
        keys = sorted(V.parse_hvec(atoms[V.parse_pol1(atoms[cells[lens["scope"]].slots[0]])[1]], require_sorted=True))
        five = ds[:5]
        others = [d for d in ds if d not in five]
        cands = [{"id": f"att{i}", "keys": [keys[i % len(keys)].hex()],
                  "acts": [{"act": "verdict", "on": d.hex(), "code": "ATTESTED", "verifier": f"profile/{i}"}]}
                 for i, d in enumerate(others[:20])]
        out = PF.filter_tensions(repo, "minds", {"format": PF.PROFILE, "goals": [d.hex() for d in five]},
                                 candidates=cands)
        silent = out["candidates"]["silent"]
        self.assertGreater(len(silent), 10)
        gate = F.fold_candidates(repo, "minds", [x for x in cands if x["id"] in silent[:10]])
        goals = {d.hex() for d in five}
        for row in gate["candidates"]:
            self.assertFalse(goals & set(row["flips"] or {}), row["id"])


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], *sys.argv[1:]], verbosity=1)
