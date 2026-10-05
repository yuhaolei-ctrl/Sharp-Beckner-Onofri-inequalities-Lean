import BecknerOnofri.RadialE1

/-! A lower logarithmic estimate retaining the exact singular coefficient.
This is an auxiliary ingredient toward the still-missing Adams endpoint. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.RadialE1

theorem logarithmic_lower {z : ℝ} (hz : 0<z) : -Real.log z-1≤E1 z := by
  by_cases hz1 : z≤1
  · rw [split hz hz1]
    have hzero (t : ℝ) (ht : t∈uIcc z 1) : t≠0 := by
      rw [uIcc_of_le hz1] at ht
      exact (hz.trans_le ht.1).ne'
    have hf : IntervalIntegrable (fun t : ℝ => Real.exp (-t)/t) volume z 1 :=
      ((Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id hzero).intervalIntegrable
    have hg : IntervalIntegrable (fun t : ℝ => 1/t) volume z 1 :=
      (continuousOn_const.div continuousOn_id hzero).intervalIntegrable
    have h := intervalIntegral.integral_mono_on hz1 (hg.sub intervalIntegrable_const) hf
      (fun t ht => by
        have htp := hz.trans_le ht.1
        have he := Real.add_one_le_exp (-t)
        have hd := div_le_div_of_nonneg_right he htp.le
        change 1/t-1≤Real.exp (-t)/t
        calc
          _ = (-t+1)/t := by field_simp; ring
          _ ≤ _ := hd)
    rw [intervalIntegral.integral_sub hg intervalIntegrable_const,
      integral_one_div_of_pos hz zero_lt_one,intervalIntegral.integral_const] at h
    simp only [one_div,Real.log_inv,smul_eq_mul,mul_one] at h
    have hE := nonneg (by norm_num : (0 : ℝ)<1)
    linarith
  · have hlog : 0≤Real.log z := Real.log_nonneg (le_of_not_ge hz1)
    exact (by linarith : -Real.log z-1≤0).trans (nonneg hz)

#print axioms logarithmic_lower
end BecknerOnofri.HighDim.RadialE1
