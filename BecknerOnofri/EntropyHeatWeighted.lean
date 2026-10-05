import BecknerOnofri.EntropyHeatLarge
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

/-- Global maximum of the sixth-degree exponential moment. -/
theorem sixth_exp_global {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) :
    s^6*Real.exp (-c*s) ≤ (6/c)^6*Real.exp (-6) := by
  have hx : 0 ≤ c*s/6*Real.exp (-(c*s/6)) := by positivity
  have h := pow_le_pow_left₀ hx (Real.mul_exp_neg_le_exp_neg_one (c*s/6)) 6
  rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  have he1 : 6 * -(c*s/6) = -c*s := by ring
  rw [he1] at h
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ (6/c)^6 by positivity)
  convert! hmul using 1
  · field_simp

/-- On s≥1, the sixth moment times exp(-cs) decreases when c≥6. -/
theorem sixth_exp_after_one {c s : ℝ} (hc : 6 ≤ c) (hs : 1 ≤ s) :
    s^6*Real.exp (-c*s) ≤ Real.exp (-c) := by
  have h6 := sixth_exp_global (c := 6) (s := s) (by norm_num) (by linarith)
  norm_num only [div_self (by norm_num : (6 : ℝ) ≠ 0), one_pow, one_mul] at h6
  have he : Real.exp (-(c-6)*s) ≤ Real.exp (-(c-6)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hp := mul_le_mul h6 he (Real.exp_pos _).le (Real.exp_pos _).le
  calc
    s^6*Real.exp (-c*s) = (s^6*Real.exp (-6*s))*Real.exp (-(c-6)*s) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-6)*Real.exp (-(c-6)) := hp
    _ = Real.exp (-c) := by rw [← Real.exp_add]; congr 1; ring

#print axioms sixth_exp_global
#print axioms sixth_exp_after_one
end BecknerOnofri.HighDim.EntropyTail
