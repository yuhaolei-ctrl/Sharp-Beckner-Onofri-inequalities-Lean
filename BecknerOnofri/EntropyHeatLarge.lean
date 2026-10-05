import BecknerOnofri.EntropyThetaEnclosure
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Ring.Abs

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.ThetaDomination

theorem exp_neg_integer_upper (m : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    Real.exp (-(m : ℝ)*s) ≤ (500/1359 : ℝ)^m := by
  have he : (1359/500 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc
    _ ≤ Real.exp (-(m : ℝ)) := Real.exp_le_exp.mpr (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    _ = 1/(Real.exp 1)^m := by
      rw [Real.exp_neg, ← Real.exp_nat_mul]
      simp
    _ ≤ 1/(1359/500 : ℝ)^m := one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) he m)
    _ = _ := by rw [one_div, ← inv_pow]; norm_num

theorem theta_cube_lower {s : ℝ} (hs : 0 < s) :
    1+2*Real.exp (-s) ≤ realTheta s := by
  have h := (summable_realTheta hs).sum_le_tsum (Finset.Icc (-1 : ℤ) 1)
    (fun j _ => (Real.exp_pos _).le)
  have he : Finset.Icc (-1 : ℤ) 1 = {-1,0,1} := by decide +kernel
  rw [he] at h
  norm_num at h
  change _ ≤ ∑' j : ℤ, Real.exp (-s*(j : ℝ)^2)
  ring_nf at h ⊢
  linarith

theorem theta_cube_remainder_large {s : ℝ} (hs : 1 ≤ s) :
    realTheta s - (1+2*Real.exp (-s)) ≤ (1007/500)*Real.exp (-4*s) := by
  have hs0 : 0 < s := by linarith
  have he : Real.exp (-5*s) ≤ 7/1007 := by
    have h := exp_neg_integer_upper 5 hs
    norm_num at h
    ring_nf at h ⊢
    linarith
  have hd : 0 < 1-Real.exp (-5*s) := by linarith
  apply (theta_cube_remainder hs0).trans
  apply (div_le_iff₀ hd).mpr
  have hp := Real.exp_pos (-4*s)
  nlinarith [mul_le_mul_of_nonneg_left he hp.le]

theorem theta_large_upper {s : ℝ} (hs : 1 ≤ s) :
    realTheta s ≤ 1+(2101/1000)*Real.exp (-s) := by
  have h := theta_cube_remainder_large hs
  have he : Real.exp (-3*s) ≤ 1/20 := by
    have h := exp_neg_integer_upper 3 hs
    norm_num at h
    ring_nf at h ⊢
    linarith
  have hr : Real.exp (-4*s) ≤ Real.exp (-s)/20 := by
    rw [show -4*s = -s + -3*s by ring, Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left he (Real.exp_pos (-s)).le]
  nlinarith [Real.exp_pos (-s)]

theorem heatComplement_large_upper {s : ℝ} (hs : 1 ≤ s) :
    heatComplement s ≤ 12*(1007/500)*Real.exp (-4*s)*(1+(2101/1000)*Real.exp (-s))^11 := by
  have hs0 : 0 < s := by linarith
  have hlow := theta_cube_lower hs0
  have hθ0 : 0 ≤ realTheta s := (by positivity : (0 : ℝ) ≤ 1+2*Real.exp (-s)).trans hlow
  have hdiff := abs_pow_sub_pow_le (a := realTheta s) (b := 1+2*Real.exp (-s)) (n := 12)
  rw [abs_of_nonneg hθ0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1+2*Real.exp (-s)),
    max_eq_left hlow, abs_of_nonneg (sub_nonneg.mpr hlow)] at hdiff
  norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hdiff
  have hp : (realTheta s)^11 ≤ (1+(2101/1000)*Real.exp (-s))^11 :=
    pow_le_pow_left₀ hθ0 (theta_large_upper hs) 11
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_right (theta_cube_remainder_large hs) (by norm_num : (0 : ℝ) ≤ 12))
    hp (pow_nonneg hθ0 _) (by positivity : (0 : ℝ) ≤ (1007/500)*Real.exp (-4*s)*12)
  change (realTheta s)^12-(1+2*Real.exp (-s))^12 ≤ _
  exact (le_abs_self _).trans (hdiff.trans (hb.trans_eq (by ring)))

#print axioms heatComplement_large_upper
end BecknerOnofri.HighDim.EntropyTail
