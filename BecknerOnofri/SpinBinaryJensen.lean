import BecknerOnofri.ConditionalJensen
import BecknerOnofri.ConditionalMomentBounds
import BecknerOnofri.SpinBinaryCost

noncomputable section
open MeasureTheory Set

namespace BecknerOnofri.HighDim.Spin

theorem binaryCost_convex : ConvexOn ℝ (Icc (-1 : ℝ) 1) binaryCost := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := binaryCostSlope)
    (f'' := binaryCostHessian) (convex_Icc _ _)
  · exact binaryCost_continuous.continuousOn
  · intro t ht
    rw [interior_Icc] at ht
    exact (binaryCost_derivative t ht.1 ht.2).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (binaryCost_second_derivative t ht.1 ht.2).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    unfold binaryCostHessian
    apply one_div_nonneg.mpr
    have h := mul_pos (show 0 < 1 + t by linarith [ht.1])
      (show 0 < 1 - t by linarith [ht.2])
    nlinarith

theorem binaryCost_weighted_jensen {d : ℕ} {f u : Torus d → ℝ}
    (hf : EntropyShearer.BoundedMeasurable f) (hpos : ∀ x, 0 ≤ f x)
    (hm : (∫ x, f x ∂torusMeasure d) = 1)
    (hu : EntropyShearer.BoundedMeasurable u) (hr : ∀ x, |u x| ≤ 1) :
    binaryCost (∫ x, f x * u x ∂torusMeasure d) ≤
      ∫ x, f x * binaryCost (u x) ∂torusMeasure d :=
  ConditionalEntropy.weighted_jensen_of_nonneg hf hpos hm hu
    (fun x => abs_le.mp (hr x)) binaryCost binaryCost_continuous.continuousOn binaryCost_convex

#print axioms binaryCost_weighted_jensen

end BecknerOnofri.HighDim.Spin
