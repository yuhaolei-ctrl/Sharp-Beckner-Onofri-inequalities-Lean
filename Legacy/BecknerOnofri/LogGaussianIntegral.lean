module

public import Legacy.BecknerOnofri.GaussianCentral

@[expose] public section

/-! A logarithmic bound for the small-time Gaussian Green integral.

The coefficient of the logarithm is kept exactly, as required by the
subcritical exponential-integrability argument. Integrability is proved
before comparing the integrals.
-/
namespace Legacy.BecknerOnofri.LogGaussianIntegral
open MeasureTheory Set

noncomputable def integrand (A t : ℝ) : ℝ := Real.exp (-A / t) / t

theorem integrand_nonneg {A t : ℝ} (ht : 0 ≤ t) : 0 ≤ integrand A t :=
  div_nonneg (Real.exp_pos _).le ht

theorem integrand_le_reciprocal {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    integrand A t ≤ 1 / (A + t) := by
  have he : A + t ≤ t * Real.exp (A / t) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (A / t)) ht.le
    field_simp at h
    nlinarith
  have h := one_div_le_one_div_of_le (add_pos hA ht) he
  calc
    integrand A t = 1 / (t * Real.exp (A / t)) := by
      unfold integrand
      rw [show -A / t = -(A / t) by ring, Real.exp_neg]
      simp [div_eq_mul_inv, mul_comm]
    _ ≤ _ := h

theorem reciprocal_integrable {A T : ℝ} (hA : 0 < A) (_hT : 0 ≤ T) :
    IntegrableOn (fun t : ℝ => 1 / (A + t)) (Ioo 0 T) := by
  apply (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
  apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
  intro t ht
  exact ne_of_gt (add_pos_of_pos_of_nonneg hA ht.1)

theorem integrable {A T : ℝ} (hA : 0 < A) (hT : 0 ≤ T) :
    IntegrableOn (integrand A) (Ioo 0 T) := by
  have hc : ContinuousOn (integrand A) (Ioo 0 T) := by
    apply ContinuousOn.div _ continuousOn_id (fun t ht => ne_of_gt ht.1)
    apply Real.continuous_exp.comp_continuousOn
    exact (continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht.1))
  apply (reciprocal_integrable hA hT).mono' (hc.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg ht.1.le)]
  exact integrand_le_reciprocal hA ht.1

theorem reciprocal_integral {A T : ℝ} (hA : 0 < A) (hT : 0 ≤ T) :
    (∫ t in Ioo 0 T, 1 / (A + t)) = Real.log (A + T) - Real.log A := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_comp_add_left (f := fun t : ℝ => 1 / t) A]
  rw [add_zero, integral_one_div_of_pos hA (add_pos_of_pos_of_nonneg hA hT),
    Real.log_div (ne_of_gt (add_pos_of_pos_of_nonneg hA hT)) (ne_of_gt hA)]

theorem integral_le_log {A T : ℝ} (hA : 0 < A) (hT : 0 ≤ T) :
    (∫ t in Ioo 0 T, integrand A t) ≤ Real.log (A + T) - Real.log A := by
  rw [← reciprocal_integral hA hT]
  apply integral_mono_ae (integrable hA hT) (reciprocal_integrable hA hT)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact integrand_le_reciprocal hA ht.1

/-- After the Green normalization, the logarithmic singularity has coefficient one. -/
theorem half_integral_le_neg_log_sqrt {q Q T : ℝ} (hq : 0 < q) (hqQ : q ≤ Q)
    (hT : 0 ≤ T) :
    (1 / 2 : ℝ) * (∫ t in Ioo 0 T, integrand (Real.pi * q) t) ≤
      -Real.log (Real.sqrt q) + (Real.log (Real.pi * Q + T) - Real.log Real.pi) / 2 := by
  have h := integral_le_log (mul_pos Real.pi_pos hq) hT
  have hl : Real.log (Real.pi * q + T) ≤ Real.log (Real.pi * Q + T) :=
    Real.log_le_log (add_pos_of_pos_of_nonneg (mul_pos Real.pi_pos hq) hT)
      (by nlinarith [Real.pi_pos])
  rw [Real.log_mul (ne_of_gt Real.pi_pos) (ne_of_gt hq)] at h
  rw [Real.log_sqrt hq.le]
  linarith

#print axioms integral_le_log
#print axioms half_integral_le_neg_log_sqrt
end Legacy.BecknerOnofri.LogGaussianIntegral
