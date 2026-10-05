import BecknerOnofri.EntropyHeatLogGrowth
import BecknerOnofri.EntropyTailScalarBasic
import BecknerOnofri.EntropyHeatConstants
import Legacy.TorusEndpoint.CertifiedExp

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.EntropyTail

theorem log_hundred_half_lower : (23/5 : ℝ) < Real.log (201/2) := by
  have hr : (Legacy.TorusEndpoint.CertifiedExp.taylor (23/25) 32 +
      Legacy.TorusEndpoint.CertifiedExp.remainder (23/25) 32 : ℚ) < 251/100 := by
    decide +kernel
  have he := (Legacy.TorusEndpoint.CertifiedExp.point_enclosure (23/25) 32
    (by norm_num) (by norm_num)).2
  have he' : Real.exp (23/25 : ℝ) < 251/100 := by
    have hr' := (Rat.cast_lt (K := ℝ)).mpr hr
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_add] at he hr'
    exact he.trans_lt hr'
  have hp := pow_lt_pow_left₀ he' (Real.exp_pos _).le (by norm_num : 5 ≠ 0)
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith

/-- The all-large-index step, with the one numerical heat value exposed.
The finite certificate must discharge `hbase` before this proves a scalar bound. -/
theorem scalarTail_lt_budget_large_of_base
    (hbase : heatIntegral (2/201) < 65701/4000)
    {n : ℕ} (hn : 100 ≤ n) : scalarTail n < scalarBudget n := by
  have hn0 : 0 < n := by omega
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hη : (0 : ℝ) < 1/((n : ℝ)+1/2) := by positivity
  have hηξ : 1/((n : ℝ)+1/2) ≤ (2/201 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)+1/2)).mpr
    linarith
  have hg := heatIntegral_log_growth hη hηξ
  have heq : (2/201 : ℝ)/(1/((n : ℝ)+1/2)) = ((n : ℝ)+1/2)/(201/2) := by
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    ring
  rw [heq, Real.log_div (by positivity) (by norm_num)] at hg
  have hln : 0 ≤ Real.log ((n : ℝ)+1/2) := Real.log_nonneg (by linarith)
  have hpi := pi_six_scale_bounds
  have hlarge := tailBudget_log_lower hn
  have hprod := mul_le_mul_of_nonneg_right hpi.2.le hln
  have hbaseLog : (184/5 : ℝ) < (Real.pi^6/120)*Real.log (201/2) := by
    have hlog := log_hundred_half_lower
    nlinarith
  have ht := scalarTail_le_heatIntegral hn0
  rw [scalarBudget_eq]
  nlinarith

#print axioms scalarTail_lt_budget_large_of_base
end BecknerOnofri.HighDim.EntropyTail
