# Strategic Coalitional Viability, Blocking Power & Alternating Simulation (`coalition.py`, `proofs/Vars1/Coalition.lean`)

`coalition.py` and `proofs/Vars1/Coalition.lean` separate **angelic** ($\exists$-trajectory) from
**controllable / strategic** ($\langle\langle C \rangle\rangle$, ATL-style) reachability and
viability, and provide constructive dynamic-loss auditing across domain translations.

## 1. Problem Solved (`F5 + F6` / `D24 + D25`)

An agency/power model computed solely on angelic reachability ($\text{Reach}^{\exists}$,
$K_{\text{viab}}^{\exists}$) fails two critical tests:

1. **Illusion of viability under resistance (`F6` / `D25`):** a state that stays safe *only* when the
   environment cooperates appears viable under $K_{\text{viab}}^{\exists}$, even when an adversary
   holds a forcing move to expel the agent. Computing Power, Rights, or Autonomy over may-reach
   systematically hides blocking power.
2. **Silent dynamic loss under translation (`F5` / `D24`):** a domain translation $\phi: S_1 \rightharpoonup S_2$
   that preserves static state invariants can collapse transitions in $S_2$, silently dropping
   $\Delta\text{Reach}$ and breaking downstream viability guarantees.

## 2. Lean 4 Constructive Theorems (`proofs/Vars1/Coalition.lean`)

All 13 theorems build cleanly with zero `sorry` and zero `Classical.choice` (10 axiom-free; 3 using
`[propext]` only):

| Theorem | Guarantee |
| :--- | :--- |
| `cpre_sub_apre` | Under `LiveEnv`, controlled predecessor implies angelic predecessor |
| `controlReach_sub_angelicReach` | $\text{Reach}^{\langle\langle C \rangle\rangle}_k(T) \subseteq \text{Reach}^{\exists}_k(T)$ |
| `controlViab_sub_angelicViab` | $K_{\text{viab}}^{\langle\langle C \rangle\rangle}(V, k) \subseteq K_{\text{viab}}^{\exists}(V, k)$ |
| `controlViab_anti_horizon` | $K_{\text{viab}}^{\langle\langle C \rangle\rangle}(V, k+1) \subseteq K_{\text{viab}}^{\langle\langle C \rangle\rangle}(V, k)$ |
| `controlViab_fixedpoint_inductive` | Any post-fixpoint $K \subseteq V \cap \text{CPre}(K)$ stays viable for all finite horizons $k$ (**Anti-Capture Autonomy Floor**) |
| `blocking_power_refutes_controlViab` | An environment forcing move out of $V$ refutes 1-step strategic viability |
| `f6_states012_control_viable` / `f6_state3_angelic_viable` / `f6_state3_not_control_viable` | Constructive `Fin 5` proof that $K_{\text{viab}}^{\langle\langle C \rangle\rangle} = \{0,1,2\} \subsetneq \{0,1,2,3\} = K_{\text{viab}}^{\exists}$ |
| `altSim_preserves_controlReach` | Alternating simulation $\phi$ transports $\text{Reach}^{\langle\langle C \rangle\rangle}$ with zero dynamic loss |
| `altSim_preserves_controlViab` | Alternating simulation preserving $V_1 \to V_2$ transports $K_{\text{viab}}^{\langle\langle C \rangle\rangle}$ faithfully |
| `coalition_reach_monotone` / `coalition_viab_monotone` | Expanding coalition capabilities never reduces guaranteed reachability or viability |

## 3. Executable Engine (`coalition.py`)

- `check_live_env(game)` — catches dead environments so `CPre` never succeeds vacuously.
- `angelic_reach` / `controllable_reach` / `angelic_viability` / `controllable_viability` — exact finite-state fixpoints.
- `blocking_power(game, safe)` — computes $K_{\text{viab}}^{\exists} \setminus K_{\text{viab}}^{\langle\langle C \rangle\rangle}$ with explicit per-action adversarial exit witnesses.
- `synthesize_survival_policy` / `verify_survival_policy` — extracts and independently verifies a deterministic survival policy $\pi_C : K_{\text{viab}}^{\langle\langle C \rangle\rangle}(V) \to A$.
- `check_alternating_simulation` / `translation_loss_report` — computes static loss, `lost_dyn_angelic`, `introduced_dyn_angelic`, `lost_dyn_control_viab`, and exact alternating-simulation counterexamples.
- `spore_fuel_game` & `viability_certificate` — links metered ATP budgets (`spore.py`) to strategic viability and emits canonical SHA-256 certificates.
