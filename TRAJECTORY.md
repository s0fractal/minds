# Inductive Trajectory Safety (`D22`) & Horizon-Bounded Semantic Mass (`D26`)

`proofs/Vars1/Trajectory.lean` and `trajectory.py` constructively formalize the final two open
ontology pillars (`F3 / D22` and `F7 / D26`), closing the formal foundation for autonomous
error-learning organisms.

## 1. Three-Part Trajectory Safety Law (`D22 / F3`)

A `TrajectorySystem (S A E)` binds a constitutional invariant `inv : S → Prop`, an admissible
action guard `safeAct : S → A → Prop`, and an adversarial transition relation `step : S → A → E → S → Prop`
under the inductive step law:
$$\forall x, a, e, x': \; I(x) \land \text{SafeAct}(x, a) \land \text{Step}(x, a, e, x') \implies I(x')$$

`SafeRun` builds horizon-indexed trajectories from `nil` (base $I(x_0)$) and `cons` (guarded step),
proving `safeRun_end_inv`, `safeRun_compose`, `safeRun_snoc`, and `safeRun_no_unsafe_end`.

## 2. Horizon-Bounded Semantic Mass & Error-Driven Revision (`D26 / F7`)

Over a finite horizon $H \in \mathbb{N}$ with exact integer weights and deduplicated `actId`s:
- Only genuinely `verified`, non-`refuted` acts with `stepIdx ≤ H` contribute mass.
- `retold` and `forked` acts contribute `0` mass (`retold_zero_mass`, `forked_zero_mass`), and
  replaying an already-seen `actId` contributes `0` (`duplicate_act_zero_mass`).
- `semanticMass_mono_horizon`: $H_1 \le H_2 \implies M_{\text{sem}, H_1} \le M_{\text{sem}, H_2}$.
- `semanticMass_bounded`: $\forall H, \; M_{\text{sem}, H}(\text{acts}) \le \text{totalWeight}(\text{acts})$
  (guaranteed finite convergence; never diverges as $H \to \infty$).
- `refuteId_non_inflationary`: refuting an act with a counterexample never inflates mass
  ($M_{\text{sem}, H}(\text{refute}(id)) \le M_{\text{sem}, H}$).

## 3. Lean 4 Constructive Theorems (`proofs/Vars1/Trajectory.lean`)

All 15 theorems compile with zero `sorry` and zero `Classical.choice`:

| Theorem | Guarantee |
| :--- | :--- |
| `safeRun_start_inv`, `safeRun_end_inv` | Every safe trajectory of length $n$ starts and ends in $I$ |
| `safeRun_compose`, `safeRun_snoc` | Safe trajectories compose and extend under adversarial environment moves |
| `safeRun_no_unsafe_end` | No safe trajectory can reach a state violating $I$ |
| `retold_zero_mass`, `forked_zero_mass`, `refuted_zero_mass` | Retold, forked, and refuted acts contribute strictly `0` mass |
| `semanticMass_mono_horizon`, `semanticMass_bounded` | Monotonic in horizon $H$ and bounded above by `totalWeight` |
| `duplicate_act_zero_mass` | Anti-Sybil replay idempotence per `actId` |
| `refuteId_non_inflationary` | Error-driven counterexample revision never inflates mass |
| `d22_d26_witness` | Concrete finite witness verifying all properties constructively |
