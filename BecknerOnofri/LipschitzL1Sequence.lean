import BecknerOnofri.LipschitzL1Approximation
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open MeasureTheory Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.RearrangementApproximation

theorem exists_lipschitz_l1_sequence {d : ℕ} {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) :
    ∃ u : ℕ → Torus d →ᵇ ℝ,∃ K : ℕ → ℝ≥0,(∀ n,LipschitzWith (K n) (u n)) ∧
      Tendsto (fun n => ∫ x,‖u n x-f x‖ ∂torusMeasure d) atTop (𝓝 0) := by
  have h (n : ℕ) := exists_lipschitz_l1_approx hf (ε := 1/((n : ℝ)+1)) (by positivity)
  choose u hu he using h
  choose K hK using hu
  refine ⟨u,K,hK,?_⟩
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) ?_
    tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  simpa only [norm_sub_rev] using he n

theorem exists_nonnegative_lipschitz_l1_sequence {d : ℕ} {f : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (hf0 : ∀ᵐ x ∂torusMeasure d,0≤f x) :
    ∃ u : ℕ → Torus d →ᵇ ℝ,∃ K : ℕ → ℝ≥0,(∀ n,LipschitzWith (K n) (u n)) ∧
      (∀ n x,0≤u n x) ∧
      Tendsto (fun n => ∫ x,‖u n x-f x‖ ∂torusMeasure d) atTop (𝓝 0) := by
  have h (n : ℕ) := exists_nonnegative_lipschitz_l1_approx hf hf0
    (ε := 1/((n : ℝ)+1)) (by positivity)
  choose u hu h0 he using h
  choose K hK using hu
  refine ⟨u,K,hK,h0,?_⟩
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) ?_
    tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  simpa only [norm_sub_rev] using he n

#print axioms exists_lipschitz_l1_sequence
#print axioms exists_nonnegative_lipschitz_l1_sequence
end BecknerOnofri.RearrangementApproximation
