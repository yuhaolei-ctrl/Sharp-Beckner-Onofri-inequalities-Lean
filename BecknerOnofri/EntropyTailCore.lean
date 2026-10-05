import BecknerOnofri.EntropyTailMellin
import BecknerOnofri.EntropyTailMonotone
import BecknerOnofri.EntropyHeatFarTail

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

theorem heat_integrable {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun s : ℝ => (s-η)^5 * heatComplement s) (Ioi η) := by
  change Integrable (fun s : ℝ => (s-η)^5 * heatComplement s) (volume.restrict (Ioi η))
  have h := (normalized_heat_integrable hη).mul_const 120
  simpa only [div_mul_cancel₀ _ (by norm_num : (120 : ℝ) ≠ 0)] using h

theorem heatIntegral_antitone : AntitoneOn heatIntegral (Ioi (0 : ℝ)) := by
  intro η hη ξ hξ hηξ
  rw [heatIntegral_eq_gaussianTail hη, heatIntegral_eq_gaussianTail hξ]
  apply (gaussianTail_summable hξ).tsum_le_tsum _ (gaussianTail_summable hη)
  intro k
  apply mul_le_mul_of_nonneg_left _ (scalarTailWeight_nonneg k)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hηξ) (Finset.sum_nonneg (fun i _ => sq_nonneg _))

#print axioms heat_integrable
#print axioms heatIntegral_antitone
end BecknerOnofri.HighDim.EntropyTail
