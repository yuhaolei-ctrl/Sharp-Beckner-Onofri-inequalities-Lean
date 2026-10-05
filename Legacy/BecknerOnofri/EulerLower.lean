import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The strict lower enclosure of Euler's constant

The trapezoid correction H_n-log(n)-1/(2n) is increasing to gamma.
Its value at 100 and an exact positive exponential Taylor sum prove the
manuscript's bound gamma > 5772/10000.
-/

namespace Legacy.BecknerOnofri.EulerLower

open Filter Topology Finset

theorem log_step_le_trapezoid (x : ℝ) (hx : 0 < x) :
    Real.log ((x + 1) / x) ≤ 1 / (2 * x) + 1 / (2 * (x + 1)) := by
  have hden : 0 < 2 * x + 1 := by positivity
  have ht0 : 0 ≤ 1 / (2 * x + 1) := by positivity
  have ht1 : 1 / (2 * x + 1) < 1 := by
    apply (div_lt_iff₀ hden).2
    linarith
  have hminus : 1 - 1 / (2 * x + 1) ≠ 0 := by linarith
  have hsq : 1 - (1 / (2 * x + 1)) ^ 2 ≠ 0 := by
    have hs := mul_self_lt_mul_self ht0 ht1
    nlinarith
  have h := Real.log_div_le_sum_range_add ht0 ht1 0
  norm_num only [sum_range_zero, mul_zero, zero_add, pow_one] at h
  have harg : (1 + 1 / (2 * x + 1)) / (1 - 1 / (2 * x + 1)) = (x + 1) / x := by
    field_simp
    <;> ring
  rw [harg] at h
  have hval : 2 * (1 / (2 * x + 1) / (1 - (1 / (2 * x + 1)) ^ 2)) =
      1 / (2 * x) + 1 / (2 * (x + 1)) := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hsq).2
    field_simp
    <;> ring
  linarith

noncomputable def corrected (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1))

theorem corrected_monotone : Monotone corrected := by
  apply monotone_nat_of_le_succ
  intro n
  have hx : (0 : ℝ) < n + 1 := by positivity
  have hx1 : (0 : ℝ) < (n + 1 : ℝ) + 1 := by positivity
  have hlog := log_step_le_trapezoid ((n : ℝ) + 1) hx
  rw [Real.log_div hx1.ne' hx.ne'] at hlog
  unfold corrected
  rw [harmonic_succ (n + 1)]
  push_cast
  have hc : ((n : ℝ) + 1 + 1)⁻¹ = 2 * (1 / (2 * ((n : ℝ) + 1 + 1))) := by
    field_simp
  linarith

theorem corrected_tendsto : Tendsto corrected atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hH := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hR := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
  have ht := hH.sub hR
  convert ht using 1
  · funext n
    simp only [corrected, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have hn : (0 : ℝ) < n + 1 := by positivity
    field_simp
  · simp

theorem corrected_le_gamma (n : ℕ) : corrected n ≤ Real.eulerMascheroniConstant :=
  corrected_monotone.ge_of_tendsto corrected_tendsto n

theorem log_hundred_upper : Real.log 100 < (4605171 / 1000000 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 100)).2
  have h := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 4605171 / 1000000) 19
  norm_num [sum_range_succ] at h
  linarith

theorem gamma_lower : (5772 / 10000 : ℝ) < Real.eulerMascheroniConstant := by
  have h := corrected_le_gamma 99
  norm_num only [corrected, Nat.reduceAdd, Nat.cast_ofNat] at h
  have hh : (5772 / 10000 : ℝ) <
      (harmonic 100 : ℝ) - 4605171 / 1000000 - 1 / 200 := by
    norm_num [harmonic, sum_range_succ]
  linarith [log_hundred_upper]

end Legacy.BecknerOnofri.EulerLower

#print axioms Legacy.BecknerOnofri.EulerLower.gamma_lower
