/-!
# Strategic Coalitional Viability, Blocking Power & Alternating Simulation (F5 + F6 / D24 + D25)

Formalizes the separation between angelic (`∃`-trajectory) reachability/viability and
controllable (`⟨⟨C⟩⟩` ATL-style strategic) reachability/viability, plus dynamic transport
across domain translations via alternating simulation:

1. **Predecessor Monotonicity & Strict Ordering (`cpre_sub_apre`, `controlReach_sub_angelicReach`,
   `controlViab_sub_angelicViab`)**:
   Under a live environment (`LiveEnv`, forbidding vacuous controllability), every strategically
   guaranteed target or viability state is angelically reachable/viable, and viability shrinks
   monotonically with horizon (`controlViab_anti_horizon`).
2. **Anti-Capture Autonomy Floor (`controlViab_fixedpoint_inductive`)**:
   Any post-fixpoint `K` of `s ↦ V s ∧ CPre G K s` guarantees safety inside `V` for all finite
   horizons `k : Nat` regardless of adversarial environment choices.
3. **Blocking Power & Constructive F6 Countermodel (`blocking_power_refutes_controlViab`,
   `f6_state3_angelic_viable`, `f6_state3_not_control_viable`, `f6_states012_control_viable`)**:
   Explicit `Fin 5` witness proving `K_viab^⟨⟨C⟩⟩(V) = {0, 1, 2} ⊊ {0, 1, 2, 3} = K_viab^∃(V)`.
4. **Alternating Simulation & Zero Dynamic Loss (`altSim_preserves_controlReach`,
   `altSim_preserves_controlViab`)**:
   Any alternating simulation `φ : S₁ → S₂` transports controllable reachability and strategic
   viability with zero controllable dynamic loss (`Lost_dyn^⟨⟨C⟩⟩(φ) = ∅`), resolving F5.
5. **Coalition Capability Monotonicity (`coalition_reach_monotone`, `coalition_viab_monotone`)**:
   Expanding a coalition's admissible actions never reduces guaranteed reachability or viability.

Every theorem uses only Lean core (`propext` and `Quot.sound`, no `Classical.choice`, no `sorry`).
-/

namespace Vars1.Coalition

/-! ## 1. Two-Player Coalitional Transition Games -/

structure Game (S A E : Type) where
  actOk : S → A → Prop
  envOk : S → E → Prop
  step  : S → A → E → S → Prop

/-- Environment liveness: whenever the coalition can act at `s`, at least one admissible
environment response produces a successor state (prevents vacuous `CPre`). -/
def LiveEnv (G : Game S A E) : Prop :=
  ∀ s a, G.actOk s a → ∃ e s', G.envOk s e ∧ G.step s a e s'

/-- Angelic predecessor (`∃`-trajectory): cooperative pair `(a, e)` reaches `P`. -/
def APre (G : Game S A E) (P : S → Prop) (s : S) : Prop :=
  ∃ a e s', G.actOk s a ∧ G.envOk s e ∧ G.step s a e s' ∧ P s'

/-- Controllable predecessor (`⟨⟨C⟩⟩` strategic): coalition move `a` forces `P` against
every admissible environment response `e`. -/
def CPre (G : Game S A E) (P : S → Prop) (s : S) : Prop :=
  ∃ a, G.actOk s a ∧ ∀ e s', G.envOk s e → G.step s a e s' → P s'

theorem apre_monotone {G : Game S A E} {P Q : S → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ s, APre G P s → APre G Q s := by
  intro s ⟨a, e, s', ha, he, hs, hp⟩
  exact ⟨a, e, s', ha, he, hs, hPQ s' hp⟩

theorem cpre_monotone {G : Game S A E} {P Q : S → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ s, CPre G P s → CPre G Q s := by
  intro s ⟨a, ha, hall⟩
  exact ⟨a, ha, fun e s' he hs => hPQ s' (hall e s' he hs)⟩

theorem cpre_sub_apre {G : Game S A E} (hlive : LiveEnv G) {P : S → Prop} :
    ∀ s, CPre G P s → APre G P s := by
  intro s ⟨a, ha, hall⟩
  obtain ⟨e, s', he, hs⟩ := hlive s a ha
  exact ⟨a, e, s', ha, he, hs, hall e s' he hs⟩

/-! ## 2. Bounded-Horizon Reachability & Viability Kernels -/

def AngelicReach (G : Game S A E) (T : S → Prop) : Nat → S → Prop
  | 0, s     => T s
  | k + 1, s => T s ∨ APre G (AngelicReach G T k) s

def ControlReach (G : Game S A E) (T : S → Prop) : Nat → S → Prop
  | 0, s     => T s
  | k + 1, s => T s ∨ CPre G (ControlReach G T k) s

def AngelicViab (G : Game S A E) (V : S → Prop) : Nat → S → Prop
  | 0, s     => V s
  | k + 1, s => V s ∧ APre G (AngelicViab G V k) s

def ControlViab (G : Game S A E) (V : S → Prop) : Nat → S → Prop
  | 0, s     => V s
  | k + 1, s => V s ∧ CPre G (ControlViab G V k) s

theorem controlReach_sub_angelicReach {G : Game S A E} (hlive : LiveEnv G) (T : S → Prop) :
    ∀ k s, ControlReach G T k s → AngelicReach G T k s
  | 0, _, h => h
  | _ + 1, _, Or.inl ht => Or.inl ht
  | k + 1, s, Or.inr hc =>
      Or.inr (cpre_sub_apre hlive s (cpre_monotone (controlReach_sub_angelicReach hlive T k) s hc))

theorem controlViab_sub_angelicViab {G : Game S A E} (hlive : LiveEnv G) (V : S → Prop) :
    ∀ k s, ControlViab G V k s → AngelicViab G V k s
  | 0, _, h => h
  | k + 1, s, ⟨hv, hc⟩ =>
      ⟨hv, cpre_sub_apre hlive s (cpre_monotone (controlViab_sub_angelicViab hlive V k) s hc)⟩

theorem controlViab_anti_horizon {G : Game S A E} (V : S → Prop) :
    ∀ k s, ControlViab G V (k + 1) s → ControlViab G V k s
  | 0, _, ⟨hv, _⟩ => hv
  | _ + 1, _, ⟨hv, hc⟩ =>
      ⟨hv, cpre_monotone (controlViab_anti_horizon V _) _ hc⟩

/-- A post-fixpoint `K` of `s ↦ V s ∧ CPre G K s` is a sovereign viability kernel
(anti-capture autonomy floor). -/
def IsControlViabKernel (G : Game S A E) (V K : S → Prop) : Prop :=
  ∀ s, K s → V s ∧ CPre G K s

/-- **Anti-Capture Autonomy Floor Theorem**: every state in a sovereign viability kernel `K`
remains strategically viable inside `V` for every finite horizon `k : Nat`. -/
theorem controlViab_fixedpoint_inductive {G : Game S A E} {V K : S → Prop}
    (hk : IsControlViabKernel G V K) :
    ∀ k s, K s → ControlViab G V k s
  | 0, s, hs => (hk s hs).1
  | k + 1, s, hs =>
      let ⟨hv, hc⟩ := hk s hs
      ⟨hv, cpre_monotone (controlViab_fixedpoint_inductive hk k) s hc⟩

/-! ## 3. Blocking Power & Constructive F6 Countermodel -/

/-- Environment forcing block at state `s`: against every admissible coalition move `a`,
the environment has an admissible response exiting `V`. -/
def ForcingBlock (G : Game S A E) (V : S → Prop) (s : S) : Prop :=
  ∀ a, G.actOk s a → ∃ e s', G.envOk s e ∧ G.step s a e s' ∧ ¬ V s'

theorem blocking_power_refutes_controlViab {G : Game S A E} {V : S → Prop} {s : S}
    (hb : ForcingBlock G V s) : ¬ ControlViab G V 1 s := by
  intro ⟨_, a, ha, hall⟩
  obtain ⟨e, s', he, hstep, hnotv⟩ := hb a ha
  exact hnotv (hall e s' he hstep)

/-- Concrete 5-state game witnessing F6: `V = {0, 1, 2, 3}`, failure state `4`.
From `{0, 1, 2}` coalition transitions safely to `0` regardless of `e : Bool`.
From `3`, cooperative `e = false` moves to `2 ∈ V`, while adversarial `e = true` forces `4 ∉ V`. -/
def f6Step (s : Fin 5) (_a : Bool) (e : Bool) : Fin 5 :=
  if s.val < 3 then ⟨0, by decide⟩
  else if s.val = 3 then
    if e then ⟨4, by decide⟩ else ⟨2, by decide⟩
  else ⟨4, by decide⟩

def f6Game : Game (Fin 5) Bool Bool where
  actOk _ _ := True
  envOk _ _ := True
  step s a e s' := s' = f6Step s a e

def f6Safe (s : Fin 5) : Prop := s.val < 4

theorem f6_liveEnv : LiveEnv f6Game := by
  intro s a _
  exact ⟨false, f6Step s a false, trivial, rfl⟩

/-- States `{0, 1, 2}` form a sovereign viability kernel in `f6Game`. -/
theorem f6_kernel_012 : IsControlViabKernel f6Game f6Safe (fun s => s.val < 3) := by
  intro s hs
  refine ⟨Nat.lt_trans hs (by decide), true, trivial, ?_⟩
  intro e s' _ hst
  subst hst
  simp [f6Step, hs]

theorem f6_states012_control_viable (s : Fin 5) (hs : s.val < 3) (k : Nat) :
    ControlViab f6Game f6Safe k s :=
  controlViab_fixedpoint_inductive f6_kernel_012 k s hs

/-- State `3` is angelically viable for EVERY horizon `k` (cooperative `e = false` moves `3 → 2`). -/
theorem f6_state3_angelic_viable : ∀ k, AngelicViab f6Game f6Safe k ⟨3, by decide⟩
  | 0 => by simp [AngelicViab, f6Safe]
  | k + 1 => by
      refine ⟨by simp [f6Safe], true, false, ⟨2, by decide⟩, trivial, trivial, ?_, ?_⟩
      · rfl
      · exact controlViab_sub_angelicViab f6_liveEnv f6Safe k ⟨2, by decide⟩
          (f6_states012_control_viable ⟨2, by decide⟩ (by decide) k)

/-- Yet state `3` is NOT strategically viable even at horizon `1`: adversary plays `e = true` → `4 ∉ V`. -/
theorem f6_state3_not_control_viable : ¬ ControlViab f6Game f6Safe 1 ⟨3, by decide⟩ := by
  apply blocking_power_refutes_controlViab
  intro a _
  refine ⟨true, ⟨4, by decide⟩, trivial, rfl, ?_⟩
  simp [f6Safe]

/-! ## 4. Alternating Simulation & Dynamic Transport (Solving F5) -/

/-- Alternating simulation morphism `φ : S₁ → S₂` from `G₁` to `G₂`:
every coalition strategy move `a₁` in `G₁` has a matching move `a₂` at `φ s₁` in `G₂`
such that every environment response in `G₂` reflects back to an admissible response in `G₁`. -/
def AltSim (G₁ : Game S₁ A₁ E₁) (G₂ : Game S₂ A₂ E₂) (φ : S₁ → S₂) : Prop :=
  ∀ s₁ a₁, G₁.actOk s₁ a₁ →
    ∃ a₂, G₂.actOk (φ s₁) a₂ ∧
      ∀ e₂ s₂', G₂.envOk (φ s₁) e₂ → G₂.step (φ s₁) a₂ e₂ s₂' →
        ∃ e₁ s₁', G₁.envOk s₁ e₁ ∧ G₁.step s₁ a₁ e₁ s₁' ∧ φ s₁' = s₂'

/-- Image predicate of `P : S₁ → Prop` along `φ : S₁ → S₂`. -/
def Img (φ : S₁ → S₂) (P : S₁ → Prop) (s₂ : S₂) : Prop :=
  ∃ s₁, P s₁ ∧ φ s₁ = s₂

/-- **F5 Dynamic Transport Theorem (Reachability)**: an alternating simulation transports
controllable reachability with zero dynamic loss (`Lost_dyn^⟨⟨C⟩⟩(φ) = ∅`). -/
theorem altSim_preserves_controlReach {G₁ : Game S₁ A₁ E₁} {G₂ : Game S₂ A₂ E₂} {φ : S₁ → S₂}
    (hsim : AltSim G₁ G₂ φ) (T : S₁ → Prop) :
    ∀ k s₁, ControlReach G₁ T k s₁ → ControlReach G₂ (Img φ T) k (φ s₁)
  | 0, s₁, ht => ⟨s₁, ht, rfl⟩
  | k + 1, s₁, Or.inl ht => Or.inl ⟨s₁, ht, rfl⟩
  | k + 1, s₁, Or.inr ⟨a₁, ha₁, hall₁⟩ => by
      obtain ⟨a₂, ha₂, hrefl⟩ := hsim s₁ a₁ ha₁
      refine Or.inr ⟨a₂, ha₂, ?_⟩
      intro e₂ s₂' he₂ hstep₂
      obtain ⟨e₁, s₁', he₁, hstep₁, hφ⟩ := hrefl e₂ s₂' he₂ hstep₂
      rw [← hφ]
      exact altSim_preserves_controlReach hsim T k s₁' (hall₁ e₁ s₁' he₁ hstep₁)

/-- **F5 Dynamic Transport Theorem (Strategic Viability)**: an alternating simulation that
preserves the safe predicate (`V₁ s₁ → V₂ (φ s₁)`) transports controllable viability faithfully. -/
theorem altSim_preserves_controlViab {G₁ : Game S₁ A₁ E₁} {G₂ : Game S₂ A₂ E₂} {φ : S₁ → S₂}
    {V₁ : S₁ → Prop} {V₂ : S₂ → Prop}
    (hsim : AltSim G₁ G₂ φ) (hV : ∀ s₁, V₁ s₁ → V₂ (φ s₁)) :
    ∀ k s₁, ControlViab G₁ V₁ k s₁ → ControlViab G₂ V₂ k (φ s₁)
  | 0, s₁, hv => hV s₁ hv
  | k + 1, s₁, ⟨hv, a₁, ha₁, hall₁⟩ => by
      obtain ⟨a₂, ha₂, hrefl⟩ := hsim s₁ a₁ ha₁
      refine ⟨hV s₁ hv, a₂, ha₂, ?_⟩
      intro e₂ s₂' he₂ hstep₂
      obtain ⟨e₁, s₁', he₁, hstep₁, hφ⟩ := hrefl e₂ s₂' he₂ hstep₂
      rw [← hφ]
      exact altSim_preserves_controlViab hsim hV k s₁' (hall₁ e₁ s₁' he₁ hstep₁)

/-! ## 5. Coalition Capability Monotonicity -/

/-- Expanding a coalition's admissible actions while keeping `envOk` and `step` fixed
never shrinks controllable reachability. -/
theorem coalition_reach_monotone {G₁ G₂ : Game S A E}
    (hact : ∀ s a, G₁.actOk s a → G₂.actOk s a)
    (henv : ∀ s e, G₂.envOk s e → G₁.envOk s e)
    (hstep : ∀ s a e s', G₂.step s a e s' → G₁.step s a e s')
    (T : S → Prop) :
    ∀ k s, ControlReach G₁ T k s → ControlReach G₂ T k s
  | 0, _, ht => ht
  | _ + 1, _, Or.inl ht => Or.inl ht
  | k + 1, s, Or.inr ⟨a, ha, hall⟩ =>
      Or.inr ⟨a, hact s a ha, fun e s' he hs =>
        coalition_reach_monotone hact henv hstep T k s' (hall e s' (henv s e he) (hstep s a e s' hs))⟩

/-- Expanding a coalition's admissible actions never shrinks controllable viability. -/
theorem coalition_viab_monotone {G₁ G₂ : Game S A E}
    (hact : ∀ s a, G₁.actOk s a → G₂.actOk s a)
    (henv : ∀ s e, G₂.envOk s e → G₁.envOk s e)
    (hstep : ∀ s a e s', G₂.step s a e s' → G₁.step s a e s')
    (V : S → Prop) :
    ∀ k s, ControlViab G₁ V k s → ControlViab G₂ V k s
  | 0, _, hv => hv
  | _ + 1, _, ⟨hv, a, ha, hall⟩ =>
      ⟨hv, a, hact _ a ha, fun e s' he hs =>
        coalition_viab_monotone hact henv hstep V _ s' (hall e s' (henv _ e he) (hstep _ a e s' hs))⟩

end Vars1.Coalition
