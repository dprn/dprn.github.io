/-
# Le théorème de Heine–Cantor, démonstration en direct

École CIMPA, Bénin, octobre 2026. Preuve reprise de l'exposé de Riccardo Brasca,
*Around Formalization* (https://riccardobrasca.github.io/Presentations/patavina/).

Placez le curseur à la fin de chaque ligne : le panneau « Lean Infoview »
affiche le but courant (après `⊢`) et les hypothèses disponibles.

**Théorème.** Soient `X`, `Y` deux espaces métriques, `X` compact. Toute
application continue `f : X → Y` est uniformément continue.

**Preuve sur papier.** Soit `ε > 0` et `K = {(x, y) | d(f x, f y) ≥ ε}`.
`K` est fermé dans le compact `X × X`, donc compact. Soit `(p, q) ∈ K` qui
minimise `d(p, q)` et `δ = d(p, q)`. Alors `δ > 0`, car `p = q` donnerait
`ε ≤ 0`. Si `d(x, y) < δ`, la minimalité donne `(x, y) ∉ K`, donc
`d(f x, f y) < ε`.

Question : où la preuve sur papier suppose-t-elle `K` non vide ?
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

theorem Heine_Cantor (X Y : Type) [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] (f : X → Y) (hf : Continuous f) :
    UniformContinuous f := by
  -- la définition `∀ ε > 0, ∃ δ > 0, ...`
  rw [Metric.uniformContinuous_iff]
  intros ε ε_pos
  -- l'ensemble des couples « mauvais »
  let K := { (p₁, p₂) : X × X | ε ≤ dist (f p₁) (f p₂) }
  have K_closed : IsClosed K := by
    apply isClosed_le
    · continuity
    · continuity
  have K_cpct : IsCompact K := by exact IsClosed.isCompact K_closed
  -- Lean nous oblige à traiter le cas `K = ∅`, oublié sur papier
  rcases K.eq_empty_or_nonempty with h | h
  · use 1, by grind
    intros x y
    have : (x, y) ∉ K := by grind
    grind
  -- un couple qui minimise la distance sur le compact non vide `K`
  obtain ⟨p, p_in, H⟩ : ∃ p ∈ K, ∀ q ∈ K, dist p.1 p.2 ≤ dist q.1 q.2
  · exact K_cpct.exists_isMinOn h continuous_dist.continuousOn
  use dist p.1 p.2
  constructor
  -- `δ > 0`, car `p.1 = p.2` donnerait `ε ≤ 0`
  · simp
    intro eq
    apply lt_irrefl ε
    calc
      ε ≤ 0 := by simpa [eq, K] using p_in
      _ < ε := ε_pos
  -- la minimalité de `p`
  · intros x x'
    contrapose!
    aesop

-- Les axiomes utilisés par la preuve : seulement les trois axiomes standards.
#print axioms Heine_Cantor

-- mathlib contient déjà ce théorème, sous une forme plus générale.
#check CompactSpace.uniformContinuous_of_continuous
