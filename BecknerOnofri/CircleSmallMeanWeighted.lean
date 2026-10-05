import BecknerOnofri.CircleSmallMeanAlgebra
import BecknerOnofri.CircleWeightSeries

/-! The small-mean scalar margin with the source's actual infinite-series
weights. The only remaining analytic input here is the rate-function bound. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar

theorem small_mean_weighted_candidate_lower (t I m₂ m₃ : ℝ)
    (ht : 0≤t) (ht1 : t≤1/16) (hI : t^2+t^4/4≤I) :
    (3/40:ℝ)*t^4≤(13/40)*I+(27/40)*t^2-2*Spin.binaryCost t+
      candidateMinimum (633/2000) ((27/40)*weight 1 t) ((27/40)*weight 2 t)
        (6-t) (6*m₂-m₃) (t^2) m₂ := by
  have hb := weight_initial_lower 1 ht (by linarith : t<1)
  have hc := weight_initial_lower 2 ht (by linarith : t<1)
  norm_num at hb hc
  apply small_mean_candidate_lower t I _ _ _ _ m₂ ht ht1 hI <;> linarith

#print axioms small_mean_weighted_candidate_lower
end BecknerOnofri.HighDim.CircleScalar
