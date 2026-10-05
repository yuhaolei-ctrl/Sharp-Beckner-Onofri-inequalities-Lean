module

public import BecknerOnofri.EntropyShearer.Deletion

@[expose] public section

noncomputable section
open MeasureTheory Function
open scoped BigOperators

namespace BecknerOnofri.HighDim.EntropyShearer

theorem avg_continuous {d : ℕ} (s : Finset (Fin d)) {f : Torus d → ℝ}
    (hf : Continuous f) : Continuous (avg s f) := by
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.norm.continuousOn
  apply continuous_of_dominated (bound := fun _ => ‖f xmax‖)
  · intro x
    exact (hf.measurable.comp measurable_updateFinset).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y => hmax (Set.mem_univ _))
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro y
    apply hf.comp
    apply continuous_pi
    intro i
    by_cases hi : i ∈ s
    · simpa only [updateFinset_def, dif_pos hi] using
        (continuous_const : Continuous (fun _ : Torus d => y ⟨i, hi⟩))
    · simpa only [updateFinset_def, dif_neg hi] using (continuous_apply i : Continuous (fun x : Torus d => x i))

/-- An actual ambient-coordinate marginal probability density. -/
def marginalDensity {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : Continuous ρ.value) (hpos : ∀ x, 0 < ρ.value x) (s : Finset (Fin d)) :
    ProbabilityDensity d where
  value := avg s ρ.value
  nonneg := Filter.Eventually.of_forall (fun x =>
    ((positiveBounded_of_continuous_pos hρ hpos).avg s |>.pos x).le)
  integrable := ((positiveBounded_of_continuous_pos hρ hpos).avg s).bounded.integrable
  mass := (integral_avg s (positiveBounded_of_continuous_pos hρ hpos).bounded).trans ρ.mass

theorem marginalDensity_continuous {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : Continuous ρ.value) (hpos : ∀ x, 0 < ρ.value x) (s : Finset (Fin d)) :
    Continuous (marginalDensity ρ hρ hpos s).value := avg_continuous s hρ

theorem marginalDensity_pos {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : Continuous ρ.value) (hpos : ∀ x, 0 < ρ.value x) (s : Finset (Fin d)) (x : Torus d) :
    0 < (marginalDensity ρ hρ hpos s).value x :=
  ((positiveBounded_of_continuous_pos hρ hpos).avg s).pos x

theorem marginalDensity_finiteEntropy {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : Continuous ρ.value) (hpos : ∀ x, 0 < ρ.value x) (s : Finset (Fin d)) :
    (marginalDensity ρ hρ hpos s).FiniteEntropy := by
  have hp := (positiveBounded_of_continuous_pos hρ hpos).avg s
  exact (hp.bounded.mul hp.logBounded).integrable

/-- Shearer in terms of the actual marginal probability-density objects. -/
theorem marginalDensity_entropy_sum_le {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : Continuous ρ.value) (hpos : ∀ x, 0 < ρ.value x) :
    (∑ i : Fin d, entropy (marginalDensity ρ hρ hpos {i})) ≤ ((d : ℝ) - 1) * entropy ρ :=
  deletion_of_continuous_pos ρ hρ hpos

#print axioms marginalDensity_entropy_sum_le

end BecknerOnofri.HighDim.EntropyShearer
