module

public import Legacy.BecknerOnofri.ThetaDomination
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

/-! Integrability of the manuscript's actual theta integrals, without numerical hypotheses. -/

open MeasureTheory Set
open scoped BigOperators

namespace Legacy.BecknerOnofri.ThetaDomination

set_option maxHeartbeats 100000

/-- The Gaussian theta series with its zero-frequency contribution removed. -/
noncomputable def thetaTail (t : ℝ) (j : ℤ) : ℝ :=
  if j = 0 then 0 else Real.exp (-t * (j : ℝ) ^ 2)

theorem thetaTail_nonneg (t : ℝ) (j : ℤ) : 0 ≤ thetaTail t j := by
  unfold thetaTail
  split_ifs <;> positivity

theorem summable_thetaTail {t : ℝ} (ht : 0 < t) : Summable (thetaTail t) := by
  apply Summable.of_nonneg_of_le (thetaTail_nonneg t) _ (summable_realTheta ht)
  intro j
  by_cases hj : j = 0
  · simp [thetaTail, hj]
  · simp [thetaTail, hj]

theorem tsum_thetaTail {t : ℝ} (ht : 0 < t) :
    ∑' j, thetaTail t j = realTheta t - 1 := by
  have h := (summable_realTheta ht).tsum_eq_add_tsum_ite (0 : ℤ)
  simp only [Int.cast_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, Real.exp_zero] at h
  change realTheta t = 1 + ∑' j, thetaTail t j at h
  linarith

/-- Exponential decay of the nonconstant theta contribution away from zero. -/
theorem realTheta_sub_one_le {t : ℝ} (ht : Real.pi ≤ t) :
    realTheta t - 1 ≤ Real.exp (Real.pi - t) * (realTheta Real.pi - 1) := by
  have htpos : 0 < t := lt_of_lt_of_le Real.pi_pos ht
  rw [← tsum_thetaTail htpos, ← tsum_thetaTail Real.pi_pos, ← tsum_mul_left]
  apply (summable_thetaTail htpos).tsum_le_tsum _
    ((summable_thetaTail Real.pi_pos).mul_left _)
  intro j
  unfold thetaTail
  split_ifs with hj
  · simp
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
      exact_mod_cast (Int.add_one_le_iff.mpr (sq_pos_of_ne_zero hj) : (0 : ℤ) + 1 ≤ j ^ 2)
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hj2)]

/-- Theta is decreasing on positive arguments. -/
theorem realTheta_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    realTheta t ≤ realTheta s := by
  apply (summable_realTheta (lt_of_lt_of_le hs hst)).tsum_le_tsum _ (summable_realTheta hs)
  intro j
  apply Real.exp_le_exp.mpr
  simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hst (sq_nonneg (j : ℝ)))

/-- A finite constant majorizing the ten-dimensional theta power. -/
noncomputable def thetaTenDecayConstant : ℝ :=
  (∑ i ∈ Finset.range 10, realTheta Real.pi ^ i) *
    (Real.exp Real.pi * (realTheta Real.pi - 1))

theorem thetaTenDecayConstant_nonneg : 0 ≤ thetaTenDecayConstant := by
  unfold thetaTenDecayConstant
  exact mul_nonneg (Finset.sum_nonneg (fun i _ ↦ pow_nonneg
    (le_trans zero_le_one (one_le_realTheta Real.pi_pos)) _))
    (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (one_le_realTheta Real.pi_pos)))

theorem realTheta_pow_ten_sub_one_le {t : ℝ} (ht : Real.pi ≤ t) :
    realTheta t ^ 10 - 1 ≤ thetaTenDecayConstant * Real.exp (-t) := by
  have htpos : 0 < t := lt_of_lt_of_le Real.pi_pos ht
  have ht1 := one_le_realTheta htpos
  have hmono := realTheta_antitone Real.pi_pos ht
  have hs : (∑ i ∈ Finset.range 10, realTheta t ^ i) ≤
      ∑ i ∈ Finset.range 10, realTheta Real.pi ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ (le_trans zero_le_one ht1) hmono i
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range 10, realTheta Real.pi ^ i :=
    Finset.sum_nonneg (fun i _ ↦ pow_nonneg
      (le_trans zero_le_one (one_le_realTheta Real.pi_pos)) _)
  calc
    realTheta t ^ 10 - 1 = (∑ i ∈ Finset.range 10, realTheta t ^ i) * (realTheta t - 1) :=
      (geom_sum_mul (realTheta t) 10).symm
    _ ≤ (∑ i ∈ Finset.range 10, realTheta Real.pi ^ i) * (realTheta t - 1) :=
      mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr ht1)
    _ ≤ (∑ i ∈ Finset.range 10, realTheta Real.pi ^ i) *
        (Real.exp (Real.pi - t) * (realTheta Real.pi - 1)) :=
      mul_le_mul_of_nonneg_left (realTheta_sub_one_le ht) hsum0
    _ = thetaTenDecayConstant * Real.exp (-t) := by
      rw [sub_eq_add_neg, Real.exp_add]
      unfold thetaTenDecayConstant
      ring

/-- A polynomial times an exponential bounds the dimension-ten integrand. -/
theorem thetaIntegrand_ten_le_decay {r : ℝ} (hr : 1 ≤ r) :
    thetaIntegrand realTheta 10 r ≤
      thetaTenDecayConstant * ((r ^ (4 : ℕ) + 1) * Real.exp (-Real.pi * r)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have harg : Real.pi ≤ Real.pi * r := by nlinarith [Real.pi_pos]
  have hp := realTheta_pow_ten_sub_one_le harg
  have hz : 0 ≤ realTheta (Real.pi * r) ^ 10 - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (one_le_realTheta (mul_pos Real.pi_pos hr0)))
  have hi : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  unfold thetaIntegrand
  norm_num only [Nat.cast_ofNat, show (10 : ℝ) / 2 - 1 = 4 by norm_num,
    show r ^ (4 : ℝ) = r ^ (4 : ℕ) from Real.rpow_natCast r 4]
  calc
    (r ^ (4 : ℕ) + r⁻¹) * (realTheta (Real.pi * r) ^ 10 - 1)
        ≤ (r ^ (4 : ℕ) + 1) * (realTheta (Real.pi * r) ^ 10 - 1) :=
      mul_le_mul_of_nonneg_right (add_le_add_right hi _) hz
    _ ≤ (r ^ (4 : ℕ) + 1) * (thetaTenDecayConstant * Real.exp (-(Real.pi * r))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = thetaTenDecayConstant * ((r ^ (4 : ℕ) + 1) * Real.exp (-Real.pi * r)) := by
      rw [neg_mul]
      ring

/-- Integrability of the simple decay majorant, obtained from the gamma integral. -/
theorem integrableOn_thetaTenDecay :
    IntegrableOn (fun r : ℝ ↦ thetaTenDecayConstant *
      ((r ^ (4 : ℕ) + 1) * Real.exp (-Real.pi * r))) (Ici (1 : ℝ)) := by
  have hp : IntegrableOn (fun r : ℝ ↦ r ^ (4 : ℕ) * Real.exp (-Real.pi * r)) (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (by norm_num : (-1 : ℝ) < 4) (by norm_num : (1 : ℝ) ≤ 1) Real.pi_pos
    simpa only [Real.rpow_one, show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl, Real.rpow_natCast] using h
  have he : IntegrableOn (fun r : ℝ ↦ Real.exp (-Real.pi * r)) (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (by norm_num : (-1 : ℝ) < 0) (by norm_num : (1 : ℝ) ≤ 1) Real.pi_pos
    simpa only [Real.rpow_one, Real.rpow_zero, one_mul] using h
  have h := (hp.add he).const_mul thetaTenDecayConstant
  apply (IntegrableOn.mono_set h (show Ici (1 : ℝ) ⊆ Ioi (0 : ℝ) from
    fun r hr ↦ (show (0 : ℝ) < r from lt_of_lt_of_le zero_lt_one hr))).congr_fun _ measurableSet_Ici
  intro r hr
  dsimp
  ring

/-- The actual dimension-ten theta integral is integrable, independently of its numerical bound. -/
theorem integrableOn_realThetaIntegrand_ten :
    IntegrableOn (thetaIntegrand realTheta 10) (Ici (1 : ℝ)) := by
  refine integrableOn_thetaTenDecay.mono'
    (aestronglyMeasurable_thetaIntegrand measurable_realTheta 10) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
  have ht := one_le_realTheta (mul_pos Real.pi_pos (lt_of_lt_of_le zero_lt_one hr))
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaIntegrand_nonneg hr ht)]
  exact thetaIntegrand_ten_le_decay hr

/-- Every theta integral in the requested dimensions is integrable. -/
theorem integrableOn_realThetaIntegrand {d : ℕ} (hd : d ≤ 10) :
    IntegrableOn (thetaIntegrand realTheta d) (Ici (1 : ℝ)) := by
  refine integrableOn_thetaIntegrand hd ?_
    (aestronglyMeasurable_thetaIntegrand measurable_realTheta d) integrableOn_realThetaIntegrand_ten
  intro r hr
  exact one_le_realTheta (mul_pos Real.pi_pos (lt_of_lt_of_le zero_lt_one hr))

/-- Unconditional dimension reduction for the actual infinite theta series and improper integral. -/
theorem realThetaIntegral_le_tenth_unconditional {d : ℕ} (hd : d ≤ 10) :
    thetaIntegral realTheta d ≤ (d : ℝ) / 10 * thetaIntegral realTheta 10 :=
  realThetaIntegral_le_tenth hd integrableOn_realThetaIntegrand_ten

end Legacy.BecknerOnofri.ThetaDomination
