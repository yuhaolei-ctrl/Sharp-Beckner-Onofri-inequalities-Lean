import BecknerOnofri.EntropyHeatSmall
import BecknerOnofri.EntropyHeatGlobalLarge

noncomputable section
namespace BecknerOnofri.HighDim.EntropyTail

theorem heatComplement_global_upper {s : ℝ} (hs : 0 < s) :
    heatComplement s ≤ Real.pi^6/s^6 := by
  by_cases hs1 : s ≤ 1
  · exact heatComplement_small_upper hs hs1
  · have h := heatComplement_weighted_large (le_of_not_ge hs1)
    have hp : (300 : ℝ) < Real.pi^6 := by
      have hh := pow_lt_pow_left₀ Real.pi_gt_three (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : 6 ≠ 0)
      norm_num at hh
      linarith
    apply (le_div_iff₀ (pow_pos hs 6)).mpr
    nlinarith

#print axioms heatComplement_global_upper
end BecknerOnofri.HighDim.EntropyTail
