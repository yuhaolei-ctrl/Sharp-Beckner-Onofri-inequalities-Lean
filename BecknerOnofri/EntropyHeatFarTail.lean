import BecknerOnofri.EntropyHeatLarge

noncomputable section
namespace BecknerOnofri.HighDim.EntropyTail

theorem exp_neg_twenty_upper {s : ℝ} (hs : 20 ≤ s) :
    Real.exp (-s) ≤ 1/(2:ℝ)^20 := by
  have h := exp_neg_integer_upper 20 (s := s/20) (by linarith)
  have he : -(20 : ℝ)*(s/20) = -s := by ring
  norm_num only [Nat.cast_ofNat] at h
  rw [he] at h
  exact h.trans (by norm_num)

theorem heatComplement_far_upper {s : ℝ} (hs : 20 ≤ s) :
    heatComplement s < 26*Real.exp (-4*s) := by
  have h := heatComplement_large_upper (show 1 ≤ s by linarith)
  have he := exp_neg_twenty_upper hs
  have hp : (1+(2101/1000)*Real.exp (-s))^11 ≤
      (1+(2101/1000)/(2:ℝ)^20)^11 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hnum : (12 : ℝ)*(1007/500)*(1+(2101/1000)/(2:ℝ)^20)^11 < 26 := by norm_num
  have hprod := mul_le_mul_of_nonneg_left hp
    (show (0 : ℝ) ≤ 12*(1007/500)*Real.exp (-4*s) by positivity)
  have hstrict := mul_lt_mul_of_pos_right hnum (Real.exp_pos (-4*s))
  nlinarith

#print axioms heatComplement_far_upper
end BecknerOnofri.HighDim.EntropyTail
