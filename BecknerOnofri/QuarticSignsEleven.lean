import BecknerOnofri.QuarticBranches

/-! The signs and branch-energy ordering used by the manuscript's local
analysis hold already in dimension eleven, independently of global endpoint rigidity. -/
noncomputable section
namespace BecknerOnofri.HighDim.LocalQuartic

lemma half_power_eleven_lower : (44:ℝ) ≤ (2:ℝ)^((11:ℝ)/2) := by
  have hs : (7/5:ℝ) ≤ (2:ℝ)^((1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  rw [show (11:ℝ)/2 = (5:ℕ)+(1:ℝ)/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_natCast]
  norm_num only [pow_succ,pow_zero,mul_one] at ⊢
  nlinarith

lemma kappa_eleven_pos : 0 < kappa 11 := by
  have hh := half_power_eleven_lower
  have hp : 0 < (2:ℝ)^((11:ℝ)/2)-1 := by linarith
  have hcross : 20/((2:ℝ)^((11:ℝ)/2)-1) ≤ 20/43 := by
    apply (div_le_iff₀ hp).mpr
    linarith
  have he : kappa 11 = (1/2:ℝ)-1/(2*((2:ℝ)^11-1))-20/((2:ℝ)^((11:ℝ)/2)-1) := by
    unfold kappa quarticA quarticB
    norm_num
    ring
  rw [he]
  norm_num only [pow_succ,pow_zero,mul_one] at ⊢
  linarith

lemma kappa_positive {d : ℕ} (hd : 11 ≤ d) : 0 < kappa d := by
  rcases eq_or_lt_of_le hd with rfl | hd'
  · exact kappa_eleven_pos
  · exact kappa_pos d (by omega)

lemma quarticA_negative {d : ℕ} (hd : 11 ≤ d) : quarticA d < 0 := by
  rcases eq_or_lt_of_le hd with rfl | hd'
  · norm_num [quarticA]
  · exact quarticA_neg (by omega)

lemma quarticB_positive {d : ℕ} (hd : 11 ≤ d) : 0 < quarticB d := by
  rcases eq_or_lt_of_le hd with rfl | hd'
  · unfold quarticB
    have h := half_power_eleven_lower
    apply div_pos (by norm_num)
    norm_num only [Nat.cast_ofNat]
    linarith
  · exact quarticB_pos (by omega)

lemma coefficient_strictMono {d m n : ℕ} (hd : 11 ≤ d) (hm : 0 < m) (hmn : m < n) :
    branchQuarticCoefficient d m < branchQuarticCoefficient d n := by
  have hm' : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr (hm.trans hmn)
  have hmn' : (m:ℝ)<n := Nat.cast_lt.mpr hmn
  have ha := quarticA_negative hd
  have hb := quarticB_positive hd
  unfold branchQuarticCoefficient
  apply (div_lt_div_iff₀ hm' hn').mpr
  nlinarith [mul_pos (sub_pos.mpr hmn') (sub_pos.mpr (show quarticA d < quarticB d/2 by linarith))]

lemma coefficient_negative {d n : ℕ} (hd : 11 ≤ d) (hn : 0 < n) (hnd : n ≤ d) :
    branchQuarticCoefficient d n < 0 := by
  have hfull : branchQuarticCoefficient d d < 0 := by
    rw [branchQuarticCoefficient_full (by omega : 0 < d)]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (kappa_positive hd))
      (mul_pos (by norm_num) (Nat.cast_pos.mpr (by omega)))
  rcases eq_or_lt_of_le hnd with rfl | hlt
  · exact hfull
  · exact (coefficient_strictMono hd hn hlt).trans hfull

lemma branch_pressure_strictMono {d m n : ℕ} (hd : 11 ≤ d)
    (hm : 0 < m) (hmn : m < n) (hnd : n ≤ d) :
    -1/(4*branchQuarticCoefficient d m) < -1/(4*branchQuarticCoefficient d n) := by
  have hmQ := coefficient_negative hd hm (hmn.le.trans hnd)
  have hnQ := coefficient_negative hd (hm.trans hmn) hnd
  have hlt := coefficient_strictMono hd hm hmn
  have he (q : ℝ) : -1/(4*q) = 1/(-4*q) := by ring
  rw [he,he]
  exact div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)

#print axioms kappa_positive
#print axioms coefficient_negative
#print axioms branch_pressure_strictMono
end BecknerOnofri.HighDim.LocalQuartic
