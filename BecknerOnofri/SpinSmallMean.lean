import BecknerOnofri.SpinSmallGradientBounds
import BecknerOnofri.SpinProductGibbs
import BecknerOnofri.SpinProductFunctional
import BecknerOnofri.SpinCenteredMoment

/-! The complete small-mean finite-state inequality, with the actual
probability law, entropy and interaction matrix of the manuscript. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem improved_small_margin : (1/50:ℝ)≤
    2-(∑ s : Order,if 2≤s.val+1 then weight s*(1/16)^(2*(s.val+1)-4) else 0)+9/10-832/1155 := by
  have h : (1/50:ℚ)≤
      2-(∑ s : Order,if 2≤s.val+1 then weightQ s*(1/16)^(2*(s.val+1)-4) else 0)+9/10-832/1155 := by
    decide +kernel
  have hc := Rat.cast_le (K:=ℝ).mpr h
  push_cast at hc
  simpa [weight,apply_ite] using hc

/-- The manuscript's small-mean conclusion, on every feasible count law. -/
theorem small_mean_spin_inequality (t : ℝ) (q : Count → ℝ)
    (ht : 0≤t) (ht1 : t≤1/16) (hq : FeasibleAt t q) :
    t^4/50≤functional q+12*((3/40)*t^4) := by
  have htlt : t<1 := by linarith
  have hp := productProbability_pos (by linarith : -1<t) htlt
  have hb := productGradientCorrection_small_bounds ht ht1
  have ht2 : t^2≤(1/256:ℝ) := by nlinarith
  have habs (j : Count) : |productGradientCorrection t j|≤5/256 := by
    have h := hb.1 j
    linarith
  have hm := finite_centered_log_mgf (productProbability t) (productGradientCorrection t) (5/256)
    hp (productProbability_mass t) (productGradientCorrection_centered t)
    (by norm_num) (by norm_num) habs
  norm_num at hm
  have hvar := mul_le_mul_of_nonneg_left hb.2 (by norm_num : (0:ℝ)≤640/231)
  have hg := product_gibbs_lower t q ht htlt hq
  have hf := productProbability_quartic_baseline ht ht1 (by norm_num : (1/16:ℝ)<1)
  have hc := mul_le_mul_of_nonneg_right improved_small_margin (pow_nonneg ht 4)
  nlinarith

#print axioms small_mean_spin_inequality
end BecknerOnofri.HighDim.Spin
