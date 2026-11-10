/-
# TD : premiers pas en Lean, corrigé

École CIMPA, Bénin, octobre 2026. Une solution possible pour chaque exercice
de `Exercices.lean`. D'autres preuves sont tout aussi bonnes.
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! ## Exercice 1 -/

-- (a) `ring` échoue sur `(x - 1) * (x + 1) ^ 2` : la factorisation est fausse
--     (développer donne `x³ + x² - x - 1`). La bonne factorisation :
example (x : ℝ) : x ^ 3 - x ^ 2 - x + 1 = (x - 1) ^ 2 * (x + 1) := by
  ring

-- (b)
example (x : ℝ) (hx : -1 ≤ x) : 0 ≤ x ^ 3 - x ^ 2 - x + 1 := by
  have h : x ^ 3 - x ^ 2 - x + 1 = (x - 1) ^ 2 * (x + 1) := by ring
  rw [h]
  have : 0 ≤ x + 1 := by linarith
  positivity

/-! ## Exercice 2 -/

theorem lipschitz_unif_continue (f : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y, |x - y| < δ → |f x - f y| < ε := by
  intro ε hε
  use ε / K
  constructor
  · positivity
  · intro x y hxy
    calc |f x - f y| ≤ K * |x - y| := hf x y
      _ < K * (ε / K) := by gcongr
      _ = ε := by field_simp

/-! ## Exercice 3 -/

theorem Heine_Cantor' (X Y : Type) [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] (f : X → Y) (hf : Continuous f) :
    UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intros ε ε_pos
  let K := { (p₁, p₂) : X × X | ε ≤ dist (f p₁) (f p₂) }
  have K_closed : IsClosed K := by
    apply isClosed_le
    · continuity
    · continuity
  -- (a)
  have K_cpct : IsCompact K := by
    exact IsClosed.isCompact K_closed
  rcases K.eq_empty_or_nonempty with h | h
  -- (b) tout `δ > 0` convient, par exemple `δ = 1`
  · use 1, by grind
    intros x y
    have : (x, y) ∉ K := by grind
    grind
  obtain ⟨p, p_in, H⟩ : ∃ p ∈ K, ∀ q ∈ K, dist p.1 p.2 ≤ dist q.1 q.2
  · exact K_cpct.exists_isMinOn h continuous_dist.continuousOn
  use dist p.1 p.2
  constructor
  · simp
    intro eq
    apply lt_irrefl ε
    calc
      ε ≤ 0 := by simpa [eq, K] using p_in
      _ < ε := ε_pos
  -- (c) si `ε ≤ dist (f x) (f x')`, alors `(x, x') ∈ K`, donc `H` s'applique
  · intros x x'
    contrapose!
    intro hxx'
    exact H (x, x') hxx'

/-! ## Exercice 4 -/

open Filter Topology in
example (u v : ℕ → ℝ) (ℓ : ℝ) (hu : Tendsto u atTop (𝓝[>] ℓ))
    (hv : Tendsto v atTop atBot) :
    Tendsto (fun n ↦ u n + v n) atTop atBot := by
  have hu' : Tendsto u atTop (𝓝 ℓ) := hu.mono_right nhdsWithin_le_nhds
  exact hu'.add_atBot hv
