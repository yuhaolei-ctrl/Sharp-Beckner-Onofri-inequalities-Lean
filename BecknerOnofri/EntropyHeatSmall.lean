import BecknerOnofri.EntropyHeatConstants
import BecknerOnofri.EntropyHeatWeighted
import BecknerOnofri.RadialHeatTail
import BecknerOnofri.SpectralSlice

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.ThetaDomination

theorem theta_near_one {t : ℝ} (ht : 0 < t)
    (hq : Real.exp (-t) ≤ 1/19000) :
    realTheta t ≤ 1+(2001/1000)*Real.exp (-t) := by
  have h := theta_remainder_upper ht 0
  norm_num only [Finset.sum_range_zero, Nat.cast_zero, zero_add, zero_mul, one_pow,
    mul_one, mul_zero, add_zero] at h
  have he : Real.exp (-t*3) = Real.exp (-t)^3 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at h
  have hp := pow_le_pow_left₀ (Real.exp_pos (-t)).le hq 3
  have hd : 0 < 1-Real.exp (-t)^3 := by norm_num at hp; linarith
  have hcoef : 2/(1-Real.exp (-t)^3) ≤ (2001/1000 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    norm_num at hp
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-t)).le
  have heq : 2*Real.exp (-t)/(1-Real.exp (-t)^3) =
      (2/(1-Real.exp (-t)^3))*Real.exp (-t) := by ring
  rw [heq] at h
  linarith

theorem theta_twelfth_near_one {t : ℝ} (ht : 0 < t)
    (hq : Real.exp (-t) ≤ 1/19000) :
    (realTheta t)^12-1 ≤ (241/10)*Real.exp (-t) := by
  have hθ0 : 0 ≤ realTheta t := zero_le_one.trans (one_le_realTheta ht)
  have hpow := pow_le_pow_left₀ hθ0 (theta_near_one ht hq) 12
  have hb := RadialThetaTail.pow_twelve_sub_one_le
    (show (0 : ℝ) ≤ (2001/1000)*Real.exp (-t) by positivity)
  have hp := pow_le_pow_left₀
    (show (0 : ℝ) ≤ 1+(2001/1000)*Real.exp (-t) by positivity)
    (show 1+(2001/1000)*Real.exp (-t) ≤ 1+(2001/1000)/19000 by nlinarith) 11
  have hnum : (12 : ℝ)*(2001/1000)*(1+(2001/1000)/19000)^11 ≤ 241/10 := by norm_num
  have h1 := mul_le_mul_of_nonneg_left hp
    (show (0 : ℝ) ≤ 12*((2001/1000)*Real.exp (-t)) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hnum (Real.exp_pos (-t)).le
  nlinarith

theorem reciprocal_gaussian_small {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (1/s)^6 * Real.exp (-(Real.pi^2/s)) ≤ Real.exp (-(Real.pi^2)) := by
  have hp : (6 : ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hi : (1 : ℝ) ≤ 1/s := (le_div_iff₀ hs).mpr (by simpa using hs1)
  have h := sixth_exp_after_one hp hi
  convert! h using 1 <;> congr 1 <;> ring

theorem exp_reciprocal_pi_upper {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.exp (-(Real.pi^2/s)) < 1/19000 := by
  have harg : Real.pi^2 ≤ Real.pi^2/s := (le_div_iff₀ hs).mpr (mul_le_of_le_one_right (sq_nonneg _) hs1)
  have he := Real.exp_le_exp.mpr (neg_le_neg harg)
  have hnum : Real.exp (-(Real.pi^2)) < 1/19000 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) exp_pi_square_lower
  exact he.trans_lt hnum

theorem theta_small_excess {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (realTheta s)^12-(Real.pi/s)^6 < 2 := by
  have ht : 0 < Real.pi^2/s := by positivity
  have hq := exp_reciprocal_pi_upper hs hs1
  have hθ := theta_twelfth_near_one ht hq.le
  have hj : (realTheta s)^12 = (Real.pi/s)^6*(realTheta (Real.pi^2/s))^12 := by
    rw [SpectralSlice.theta_jacobi hs, mul_pow]
    congr 1
    rw [show (Real.sqrt (Real.pi/s))^12 = ((Real.sqrt (Real.pi/s))^2)^6 by ring,
      Real.sq_sqrt (by positivity)]
  have hp := mul_le_mul_of_nonneg_left hθ (show 0 ≤ (Real.pi/s)^6 by positivity)
  have hg := reciprocal_gaussian_small hs hs1
  have hscale := mul_le_mul_of_nonneg_left hg (show (0 : ℝ) ≤ (241/10)*Real.pi^6 by positivity)
  have hnum : Real.exp (-(Real.pi^2)) < 1/19000 := by
    simpa only [div_one] using exp_reciprocal_pi_upper (s := 1) (by norm_num) le_rfl
  have hstrict := mul_lt_mul_of_pos_left hnum (show (0 : ℝ) < (241/10)*Real.pi^6 by positivity)
  have hpi := pi_six_upper
  rw [hj]
  have heq : (Real.pi/s)^6 = Real.pi^6*(1/s)^6 := by ring
  rw [heq] at hp ⊢
  nlinarith

theorem cube_heat_lower_small {s : ℝ} (hs1 : s ≤ 1) :
    (2 : ℝ) < (1+2*Real.exp (-s))^12 := by
  have hnum : (1/3 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (Real.exp_pos _) Real.exp_one_lt_three
  have he := Real.exp_le_exp.mpr (neg_le_neg hs1)
  have hp := pow_lt_pow_left₀ (show (5/3 : ℝ) < 1+2*Real.exp (-s) by linarith)
    (by norm_num : (0 : ℝ) ≤ 5/3) (by norm_num : 12 ≠ 0)
  norm_num at hp
  linarith

theorem heatComplement_small_upper {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    heatComplement s ≤ Real.pi^6/s^6 := by
  have hθ := theta_small_excess hs hs1
  have hc := cube_heat_lower_small hs1
  change (realTheta s)^12-(1+2*Real.exp (-s))^12 ≤ _
  rw [div_pow] at hθ
  linarith

#print axioms heatComplement_small_upper
end BecknerOnofri.HighDim.EntropyTail
