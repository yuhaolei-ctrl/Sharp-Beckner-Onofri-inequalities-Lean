module

public import BecknerOnofri.SpinExactArithmetic

@[expose] public section

/-! The exact small-mean constants of §5.2.5, generated from the same weights.
This file certifies the finite rational expressions, not the entropy reduction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem small_mean_denominator_bound :
    5*smallMeanQ^2*oscillationConstantQ < 191/1000 := by
  decide +kernel

theorem small_mean_margin_bound : (1/50:ℚ) ≤ smallMarginQ := by
  decide +kernel

theorem small_mean_reported_margin : (2498/100000:ℚ) < smallMarginQ := by
  decide +kernel

#print axioms small_mean_margin_bound
end BecknerOnofri.HighDim.Spin
