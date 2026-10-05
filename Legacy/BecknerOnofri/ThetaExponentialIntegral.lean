import Legacy.BecknerOnofri.LaplaceReciprocal
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Algebra.BigOperators.Field

/-!
An analytic integral bound for each exponential term in the theta polynomial
majorant. The affine change of variables, all moment integrals, and the
reciprocal term are proved for actual Lebesgue integrals.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Legacy.BecknerOnofri.ThetaExponentialIntegral

noncomputable def weight (A r : ℝ) : ℝ :=
  (r ^ 4 + r⁻¹) * Real.exp (-A * r)

noncomputable def weightIntegral (A : ℝ) : ℝ :=
  ∫ r : ℝ in Ici 1, weight A r

theorem scaled_moment_integral (n : ℕ) {A : ℝ} (hA : 0 < A) :
    (∫ r : ℝ in Ioi 0, r ^ n * Real.exp (-A * r)) =
      (1 / A) ^ (n + 1) * (n.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := A) (by positivity) hA
  have hn : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
  simp only [add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] at h
  rw [hn, Real.rpow_natCast] at h
  simpa only [neg_mul] using h

theorem scaled_moment_integrable (n : ℕ) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun r : ℝ => r ^ n * Real.exp (-A * r)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [scaled_moment_integral n hA]
  exact mul_ne_zero (pow_ne_zero _ (one_div_ne_zero hA.ne'))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

theorem integrable_polynomial {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun r : ℝ => r ^ 4 * Real.exp (-A * r)) (Ici 1) := by
  apply (scaled_moment_integrable 4 hA).mono_set
  intro r hr
  change 0 < r
  change 1 ≤ r at hr
  linarith

theorem integrable_reciprocal {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun r : ℝ => r⁻¹ * Real.exp (-A * r)) (Ici 1) := by
  have he : IntegrableOn (fun r : ℝ => Real.exp (-A * r)) (Ici 1) := by
    simpa only [pow_zero, one_mul] using
      (scaled_moment_integrable 0 hA).mono_set
        (show Ici (1 : ℝ) ⊆ Ioi 0 by intro r hr; change 0 < r; change 1 ≤ r at hr; linarith)
  have hm : Measurable (fun r : ℝ => r⁻¹ * Real.exp (-A * r)) := by fun_prop
  apply he.mono' hm.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with r hr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hri : r⁻¹ ≤ 1 := by simpa only [one_div] using (div_le_one hrp).mpr hr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hrp.le) (Real.exp_pos _).le)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hri (Real.exp_pos _).le

theorem integrable_weight {A : ℝ} (hA : 0 < A) :
    IntegrableOn (weight A) (Ici 1) := by
  have he : weight A =
      (fun r : ℝ => r ^ 4 * Real.exp (-A * r)) +
      (fun r : ℝ => r⁻¹ * Real.exp (-A * r)) := by
    funext r
    simp only [weight, Pi.add_apply, add_mul]
  rw [he]
  exact (integrable_polynomial hA).add (integrable_reciprocal hA)

/-- Translation followed by positive dilation. This identity does not silently
assume integrability; the concrete uses below also prove integrability. -/
theorem integral_affine (f : ℝ → ℝ) {A : ℝ} (hA : 0 < A) :
    (∫ r : ℝ in Ioi 1, f r) =
      A⁻¹ * ∫ v : ℝ in Ioi 0, f (v / A + 1) := by
  have hshift := (measurePreserving_add_right (volume : Measure ℝ) 1).setIntegral_preimage_emb
    (MeasurableEquiv.addRight (1 : ℝ)).measurableEmbedding
      f (Ioi 1)
  rw [preimage_add_const_Ioi, sub_self] at hshift
  rw [← hshift]
  have hscale := integral_comp_mul_left_Ioi (fun v : ℝ => f (v / A + 1)) 0 hA
  simpa only [mul_zero, smul_eq_mul, mul_div_cancel_left₀ _ hA.ne'] using hscale

theorem affine_exp {A : ℝ} (hA : 0 < A) (v : ℝ) :
    Real.exp (-A * (v / A + 1)) = Real.exp (-A) * Real.exp (-v) := by
  rw [show -A * (v / A + 1) = -A + -v by field_simp [hA.ne']; ring,
    Real.exp_add]

theorem shifted_polynomial_expansion (A v : ℝ) :
    (v / A + 1) ^ 4 * Real.exp (-v) =
      ∑ n ∈ Finset.range 5,
        ((Nat.choose 4 n : ℝ) / A ^ n) * (v ^ n * Real.exp (-v)) := by
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

theorem integral_polynomial {A : ℝ} (hA : 0 < A) :
    (∫ r : ℝ in Ici 1, r ^ 4 * Real.exp (-A * r)) =
      Real.exp (-A) * (1 / A + 4 / A ^ 2 + 12 / A ^ 3 + 24 / A ^ 4 + 24 / A ^ 5) := by
  rw [integral_Ici_eq_integral_Ioi, integral_affine _ hA]
  have he : (fun v : ℝ => (v / A + 1) ^ 4 * Real.exp (-A * (v / A + 1))) =
      (fun v : ℝ => Real.exp (-A) * ∑ n ∈ Finset.range 5,
        ((Nat.choose 4 n : ℝ) / A ^ n) * (v ^ n * Real.exp (-v))) := by
    funext v
    rw [affine_exp hA, ← shifted_polynomial_expansion]
    ring
  rw [he, integral_const_mul, integral_finsetSum (Finset.range 5)
    (fun n _ => (LaplaceReciprocal.moment_integrable n).const_mul _)]
  simp only [integral_const_mul, LaplaceReciprocal.moment_integral]
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.factorial]
  ring

theorem integral_reciprocal {A : ℝ} (hA : 0 < A) :
    (∫ r : ℝ in Ici 1, r⁻¹ * Real.exp (-A * r)) =
      Real.exp (-A) * ∫ v : ℝ in Ioi 0, Real.exp (-v) / (A + v) := by
  rw [integral_Ici_eq_integral_Ioi, integral_affine _ hA]
  have he : (∫ v : ℝ in Ioi 0,
      (v / A + 1)⁻¹ * Real.exp (-A * (v / A + 1))) =
      ∫ v : ℝ in Ioi 0, (A * Real.exp (-A)) * (Real.exp (-v) / (A + v)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [affine_exp hA]
    have hshift : v / A + 1 = (A + v) / A := by
      field_simp [hA.ne']
      ring
    rw [hshift, inv_div]
    ring
  rw [he, integral_const_mul]
  field_simp [hA.ne']

/-- Analytic bound used term-by-term for the theta exponential polynomial. -/
theorem integral_upper {A : ℝ} (hA : 0 < A) :
    weightIntegral A ≤ Real.exp (-A) *
      (1 / A + 4 / A ^ 2 + 12 / A ^ 3 + 24 / A ^ 4 + 24 / A ^ 5 +
        (A ^ 2 + 5 * A + 2) / (A * (A ^ 2 + 6 * A + 6))) := by
  unfold weightIntegral
  simp_rw [weight, add_mul]
  rw [integral_add (integrable_polynomial hA) (integrable_reciprocal hA),
    integral_polynomial hA, integral_reciprocal hA]
  have h := mul_le_mul_of_nonneg_left (LaplaceReciprocal.integral_upper hA)
    (Real.exp_pos (-A)).le
  linarith

end Legacy.BecknerOnofri.ThetaExponentialIntegral
