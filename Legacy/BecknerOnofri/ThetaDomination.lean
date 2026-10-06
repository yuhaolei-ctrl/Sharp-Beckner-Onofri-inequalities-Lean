module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! Dimension reduction for the theta integral in the manuscript.

The pointwise estimate is independent of how the theta function is constructed.
The integration theorem explicitly requires integrability; a second theorem derives
lower-dimensional integrability from measurability and dimension-ten integrability.
-/

open MeasureTheory Set

namespace Legacy.BecknerOnofri.ThetaDomination

/-- Convexity in the exponent, including the endpoint `d = 0`. -/
theorem pow_sub_one_le_tenth {y : ℝ} (hy : 1 ≤ y) {d : ℕ} (hd : d ≤ 10) :
    y ^ d - 1 ≤ (d : ℝ) / 10 * (y ^ 10 - 1) := by
  have hdR : (d : ℝ) ≤ 10 := by exact_mod_cast hd
  have h := (convexOn_rpow_left (by linarith : 0 < y)).2
    (show (0 : ℝ) ∈ univ from mem_univ _) (show (10 : ℝ) ∈ univ from mem_univ _)
    (show 0 ≤ 1 - (d : ℝ) / 10 by linarith)
    (show 0 ≤ (d : ℝ) / 10 by positivity) (by ring)
  have he : (1 - (d : ℝ) / 10) • (0 : ℝ) + ((d : ℝ) / 10) • (10 : ℝ) = (d : ℝ) := by
    simp only [smul_eq_mul]; ring
  dsimp only at h
  rw [he, Real.rpow_natCast] at h
  norm_num only [Real.rpow_zero, smul_eq_mul] at h
  have hten : y ^ (10 : ℝ) = y ^ (10 : ℕ) := by exact Real.rpow_natCast y 10
  rw [hten] at h
  linarith

/-- The radial power in dimension at most ten is bounded by the dimension-ten power. -/
theorem radial_power_le_four {r : ℝ} (hr : 1 ≤ r) {d : ℕ} (hd : d ≤ 10) :
    r ^ ((d : ℝ) / 2 - 1) ≤ r ^ (4 : ℕ) := by
  have hdR : (d : ℝ) ≤ 10 := by exact_mod_cast hd
  have h := Real.rpow_le_rpow_of_exponent_le hr
    (show (d : ℝ) / 2 - 1 ≤ (4 : ℝ) by linarith)
  simpa only [show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl, Real.rpow_natCast] using h

/-- The integrand defining `J_d`; `theta` takes the manuscript argument `πr`. -/
noncomputable def thetaIntegrand (theta : ℝ → ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  (r ^ ((d : ℝ) / 2 - 1) + r⁻¹) * (theta (Real.pi * r) ^ d - 1)

/-- The manuscript integral over `[1, ∞)`, represented as a restricted Lebesgue integral. -/
noncomputable def thetaIntegral (theta : ℝ → ℝ) (d : ℕ) : ℝ :=
  ∫ r in Ici (1 : ℝ), thetaIntegrand theta d r

theorem thetaIntegrand_nonneg {theta : ℝ → ℝ} {d : ℕ} {r : ℝ}
    (hr : 1 ≤ r) (htheta : 1 ≤ theta (Real.pi * r)) :
    0 ≤ thetaIntegrand theta d r := by
  unfold thetaIntegrand
  exact mul_nonneg
    (add_nonneg (Real.rpow_nonneg (by linarith) _) (inv_nonneg.mpr (by linarith)))
    (sub_nonneg.mpr (one_le_pow₀ htheta))

/-- Pointwise domination of the actual integrand on its integration domain. -/
theorem thetaIntegrand_le_tenth {theta : ℝ → ℝ} {d : ℕ} (hd : d ≤ 10)
    {r : ℝ} (hr : 1 ≤ r) (htheta : 1 ≤ theta (Real.pi * r)) :
    thetaIntegrand theta d r ≤ (d : ℝ) / 10 * thetaIntegrand theta 10 r := by
  have hp := pow_sub_one_le_tenth htheta hd
  have hw := radial_power_le_four hr hd
  have hz : 0 ≤ theta (Real.pi * r) ^ d - 1 := sub_nonneg.mpr (one_le_pow₀ htheta)
  have hw0 : 0 ≤ r ^ (4 : ℕ) + r⁻¹ := by positivity
  unfold thetaIntegrand
  have he : ((10 : ℕ) : ℝ) / 2 - 1 = (4 : ℝ) := by norm_num
  rw [he, show r ^ (4 : ℝ) = r ^ (4 : ℕ) from Real.rpow_natCast r 4]
  calc
    (r ^ ((d : ℝ) / 2 - 1) + r⁻¹) * (theta (Real.pi * r) ^ d - 1)
        ≤ (r ^ (4 : ℕ) + r⁻¹) * (theta (Real.pi * r) ^ d - 1) :=
      mul_le_mul_of_nonneg_right (add_le_add_left hw _) hz
    _ ≤ (r ^ (4 : ℕ) + r⁻¹) * ((d : ℝ) / 10 * (theta (Real.pi * r) ^ 10 - 1)) :=
      mul_le_mul_of_nonneg_left hp hw0
    _ = (d : ℝ) / 10 * ((r ^ (4 : ℕ) + r⁻¹) * (theta (Real.pi * r) ^ 10 - 1)) := by ring

/-- `J_d ≤ (d/10) J_10`, with both integrability requirements visible. -/
theorem thetaIntegral_le_tenth {theta : ℝ → ℝ} {d : ℕ} (hd : d ≤ 10)
    (htheta : ∀ r ∈ Ici (1 : ℝ), 1 ≤ theta (Real.pi * r))
    (hintd : IntegrableOn (thetaIntegrand theta d) (Ici (1 : ℝ)))
    (hint10 : IntegrableOn (thetaIntegrand theta 10) (Ici (1 : ℝ))) :
    thetaIntegral theta d ≤ (d : ℝ) / 10 * thetaIntegral theta 10 := by
  unfold thetaIntegral
  rw [← integral_const_mul]
  exact setIntegral_mono_on hintd (hint10.const_mul _) measurableSet_Ici
    (fun r hr ↦ thetaIntegrand_le_tenth hd hr (htheta r hr))

/-- A summable dimension-ten majorant supplies every lower-dimensional integral,
provided the lower-dimensional integrand is measurable. -/
theorem integrableOn_thetaIntegrand {theta : ℝ → ℝ} {d : ℕ} (hd : d ≤ 10)
    (htheta : ∀ r ∈ Ici (1 : ℝ), 1 ≤ theta (Real.pi * r))
    (hmeas : AEStronglyMeasurable (thetaIntegrand theta d) (volume.restrict (Ici (1 : ℝ))))
    (hint10 : IntegrableOn (thetaIntegrand theta 10) (Ici (1 : ℝ))) :
    IntegrableOn (thetaIntegrand theta d) (Ici (1 : ℝ)) := by
  refine (hint10.const_mul ((d : ℝ) / 10)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaIntegrand_nonneg hr (htheta r hr))]
  exact thetaIntegrand_le_tenth hd hr (htheta r hr)

/-- Dimension reduction using only dimension-ten integrability and lower-dimensional measurability.
-/
theorem thetaIntegral_le_tenth_of_measurable {theta : ℝ → ℝ} {d : ℕ} (hd : d ≤ 10)
    (htheta : ∀ r ∈ Ici (1 : ℝ), 1 ≤ theta (Real.pi * r))
    (hmeas : AEStronglyMeasurable (thetaIntegrand theta d) (volume.restrict (Ici (1 : ℝ))))
    (hint10 : IntegrableOn (thetaIntegrand theta 10) (Ici (1 : ℝ))) :
    thetaIntegral theta d ≤ (d : ℝ) / 10 * thetaIntegral theta 10 :=
  thetaIntegral_le_tenth hd htheta (integrableOn_thetaIntegrand hd htheta hmeas hint10) hint10

/-- The real theta series used in the manuscript, without changing its normalization. -/
noncomputable def realTheta (t : ℝ) : ℝ :=
  ∑' j : ℤ, Real.exp (-t * (j : ℝ) ^ 2)

/-- The Gaussian theta series is summable for every positive argument. -/
theorem summable_realTheta {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ ↦ Real.exp (-t * (j : ℝ) ^ 2)) := by
  have hnat : Summable (fun n : ℕ ↦ Real.exp (-t * (n : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n ↦ (Real.exp_pos _).le) ?_
      (Real.summable_exp_nat_mul_iff.mpr (show -t < 0 by linarith))
    intro n
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by omega : 2 ≠ 0) n
    nlinarith
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [Int.cast_natCast] using hnat
  · simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hnat

/-- The zero lattice point contributes one; all other summands are nonnegative. -/
theorem one_le_realTheta {t : ℝ} (ht : 0 < t) : 1 ≤ realTheta t := by
  have h := (summable_realTheta ht).le_tsum (0 : ℤ) (fun j _ ↦ (Real.exp_pos _).le)
  simpa only [Int.cast_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, Real.exp_zero,
    realTheta] using h

/-- Global measurability does not require restricting to the convergence half-line. -/
theorem measurable_realTheta : Measurable realTheta := by
  apply Measurable.tsum
  intro j
  exact (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).measurable

/-- Measurability of theta suffices for measurability of every integrand on `[1, ∞)`. -/
theorem aestronglyMeasurable_thetaIntegrand {theta : ℝ → ℝ} (htheta : Measurable theta)
    (d : ℕ) :
    AEStronglyMeasurable (thetaIntegrand theta d) (volume.restrict (Ici (1 : ℝ))) := by
  have hr : ContinuousOn (fun r : ℝ ↦ r ^ ((d : ℝ) / 2 - 1)) (Ici (1 : ℝ)) :=
    continuousOn_id.rpow_const (fun r hr ↦ Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hr)))
  have hm : AEStronglyMeasurable (fun r : ℝ ↦ r ^ ((d : ℝ) / 2 - 1))
      (volume.restrict (Ici (1 : ℝ))) := hr.aestronglyMeasurable measurableSet_Ici
  unfold thetaIntegrand
  refine (hm.add measurable_inv.aestronglyMeasurable).mul ?_
  exact ((htheta.comp (measurable_const.mul measurable_id)).pow_const d |>.sub measurable_const).aestronglyMeasurable

/-- The manuscript dimension reduction specialized to its actual theta series.
Only the dimension-ten integrability remains as an explicit analytic hypothesis. -/
theorem realThetaIntegral_le_tenth {d : ℕ} (hd : d ≤ 10)
    (hint10 : IntegrableOn (thetaIntegrand realTheta 10) (Ici (1 : ℝ))) :
    thetaIntegral realTheta d ≤ (d : ℝ) / 10 * thetaIntegral realTheta 10 := by
  refine thetaIntegral_le_tenth_of_measurable hd ?_
    (aestronglyMeasurable_thetaIntegrand measurable_realTheta d) hint10
  intro r hr
  exact one_le_realTheta (mul_pos Real.pi_pos (by have : 1 ≤ r := hr; linarith))

end Legacy.BecknerOnofri.ThetaDomination
