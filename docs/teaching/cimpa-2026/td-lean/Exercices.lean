/-
# TD : premiers pas en Lean

École CIMPA, Bénin, octobre 2026.

Remplacez chaque `sorry` par une preuve. Un `sorry` restant est signalé par un
avertissement jaune. Une preuve terminée n'affiche plus rien, et l'Infoview
indique « No goals ».

Tactiques utiles :

* `intro x` : introduit une variable ou une hypothèse (`∀`, `→`).
* `use a` : fournit le témoin d'un `∃`.
* `constructor` : coupe un `∧` en deux buts.
* `rw [h]` : réécrit avec l'égalité `h`.
* `ring` : démontre une identité entre polynômes.
* `linarith` : conclut à partir d'inégalités linéaires dans les hypothèses.
* `positivity` : démontre `0 ≤ e` ou `0 < e` quand c'est « évident ».
* `gcongr` : « multiplier une inégalité des deux côtés ».
* `field_simp` : simplifie les fractions (dénominateurs non nuls).
* `calc` : chaîne d'égalités et d'inégalités, comme au tableau.
* `exact?` : demande à Lean de chercher le lemme qui conclut.
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

/-! ## Exercice 1 (échauffement) : une inégalité polynomiale

Soit `p(x) = x³ - x² - x + 1`. On veut montrer que `p(x) ≥ 0` pour `x ≥ -1`.

Une « preuve » circule : `p(x) = (x - 1)(x + 1)² ≥ 0`. -/

-- (a) Essayez de prouver cette factorisation avec `ring`. Que se passe-t-il ?
--     Remplacez ensuite l'énoncé par la bonne factorisation, puis prouvez-la.
example (x : ℝ) : x ^ 3 - x ^ 2 - x + 1 = (x - 1) * (x + 1) ^ 2 := by
  sorry

-- (b) Démontrez l'inégalité.
--     Indication : `have h : x ^ 3 - x ^ 2 - x + 1 = ... := by ring`, puis
--     `rw [h]`, puis `have : 0 ≤ x + 1 := by linarith`, et `positivity`.
example (x : ℝ) (hx : -1 ≤ x) : 0 ≤ x ^ 3 - x ^ 2 - x + 1 := by
  sorry

/-! ## Exercice 2 : une fonction lipschitzienne est uniformément continue

Preuve sur papier : soit `ε > 0`, on pose `δ = ε / K`. Si `|x - y| < δ`, alors
`|f x - f y| ≤ K |x - y| < K δ = ε`. -/

theorem lipschitz_unif_continue (f : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y, |x - y| < δ → |f x - f y| < ε := by
  intro ε hε
  use ε / K
  constructor
  · -- le but est `ε / K > 0`
    sorry
  · intro x y hxy
    calc |f x - f y| ≤ K * |x - y| := by sorry
      _ < K * (ε / K) := by sorry
      _ = ε := by sorry

/-! ## Exercice 3 : Heine–Cantor à trous

La preuve vue en cours (fichier `HeineCantor.lean`), avec trois trous. -/

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
  -- (a) Un fermé d'un espace compact est compact. Essayez `exact?`.
  have K_cpct : IsCompact K := by
    sorry
  rcases K.eq_empty_or_nonempty with h | h
  -- (b) Le cas `K = ∅` : quel `δ` choisir ? Écrivez `use ...`, puis
  --     inspirez-vous de `HeineCantor.lean`.
  · sorry
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
  -- (c) Si `dist x x' < dist p.1 p.2`, alors `dist (f x) (f x') < ε`.
  --     Indication : `contrapose!` transforme le but en sa contraposée.
  · sorry

/-! ## Exercice 4 (bonus) : les filtres

Si `uₙ → ℓ⁺` et `vₙ → -∞`, alors `uₙ + vₙ → -∞`. Dans mathlib, « `u` tend vers
`ℓ` par valeurs supérieures » s'écrit `Tendsto u atTop (𝓝[>] ℓ)`.

Indications : `Filter.Tendsto.add_atBot` traite le cas `u → ℓ`. Pour passer de
`𝓝[>] ℓ` à `𝓝 ℓ`, cherchez un lemme avec `exact?` ou utilisez
`Filter.Tendsto.mono_right`. -/

open Filter Topology in
example (u v : ℕ → ℝ) (ℓ : ℝ) (hu : Tendsto u atTop (𝓝[>] ℓ))
    (hv : Tendsto v atTop atBot) :
    Tendsto (fun n ↦ u n + v n) atTop atBot := by
  sorry
