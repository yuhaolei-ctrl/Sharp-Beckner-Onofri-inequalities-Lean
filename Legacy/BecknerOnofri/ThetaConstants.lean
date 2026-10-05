import Legacy.BecknerOnofri.ThetaCertificate
namespace Legacy.BecknerOnofri.ThetaCertificate

 theorem a_pos : (0 : ℝ) < (a : ℝ) := by norm_num [a]
 theorem r_pos : (0 : ℝ) < (r : ℝ) := by norm_num [r]
 theorem a_lt_pi : (a : ℝ) < Real.pi := by
  norm_num [a]
  linarith [Real.pi_gt_d20]

 theorem inverse_r_lt_exp_a : 1 / (r : ℝ) < Real.exp (a : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg a_pos.le 24
  norm_num [a, Finset.sum_range_succ] at h
  norm_num [r, a]
  linarith

 theorem exp_neg_pi_lt_r : Real.exp (-Real.pi) < (r : ℝ) := by
  have h := inverse_r_lt_exp_a.trans (Real.exp_lt_exp.mpr a_lt_pi)
  have hmul := (div_lt_iff₀ r_pos).mp h
  rw [Real.exp_neg]
  rw [← one_div]
  apply (div_lt_iff₀ (Real.exp_pos _)).2
  simpa [mul_comm] using hmul

#print axioms a_lt_pi
#print axioms exp_neg_pi_lt_r
end Legacy.BecknerOnofri.ThetaCertificate
