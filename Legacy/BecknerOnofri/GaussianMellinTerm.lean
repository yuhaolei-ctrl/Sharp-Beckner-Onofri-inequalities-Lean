import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Actual shifted Mellin integrals of individual Gaussian lattice terms.
The exponent is any positive real number, including the half-integer
exponents arising in odd dimensions. The shift can be any real number.
No exchange of an infinite lattice sum and an integral is asserted here.
-/

open MeasureTheory Set

namespace Legacy.BecknerOnofri.GaussianMellinTerm

noncomputable def shiftedIntegrand (s R a t : ℝ) : ℝ :=
  (t - a) ^ (s - 1) * Real.exp (-t * R)

/-- Exact translation of an integral over an open half-line. -/
theorem integral_shift (f : ℝ → ℝ) (a : ℝ) :
    (∫ t : ℝ in Ioi a, f t) = ∫ u : ℝ in Ioi 0, f (u + a) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) a).setIntegral_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding f (Ioi a)
  rw [preimage_add_const_Ioi, sub_self] at h
  exact h.symm

theorem shifted_integrand_translation (s R a u : ℝ) :
    shiftedIntegrand s R a (u + a) =
      Real.exp (-a * R) * (u ^ (s - 1) * Real.exp (-(R * u))) := by
  unfold shiftedIntegrand
  rw [add_sub_cancel_right,
    show -(u + a) * R = -a * R + -(R * u) by ring, Real.exp_add]
  ring

/-- The shifted Mellin formula for arbitrary real `s > 0` and `R > 0`.
Its validity for all real shifts includes the desired case `a ≥ 0`. -/
theorem shifted_integral {s R : ℝ} (hs : 0 < s) (hR : 0 < R) (a : ℝ) :
    (∫ t : ℝ in Ioi a, (t - a) ^ (s - 1) * Real.exp (-t * R)) =
      Real.exp (-a * R) * Real.Gamma s / R ^ s := by
  change (∫ t : ℝ in Ioi a, shiftedIntegrand s R a t) = _
  rw [integral_shift]
  simp_rw [shifted_integrand_translation]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hs hR,
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hR.le, Real.one_rpow]
  ring

/-- Integrability is proved, so the Mellin formula cannot be an artefact of
the default value assigned to a nonintegrable Bochner integral. -/
theorem shifted_integrable {s R : ℝ} (hs : 0 < s) (hR : 0 < R) (a : ℝ) :
    IntegrableOn (fun t : ℝ => (t - a) ^ (s - 1) * Real.exp (-t * R)) (Ioi a) := by
  apply Integrable.of_integral_ne_zero
  rw [shifted_integral hs hR a]
  exact ne_of_gt (div_pos (mul_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos hs))
    (Real.rpow_pos_of_pos hR _))

theorem normalized_shifted_integrable {s R : ℝ} (hs : 0 < s) (hR : 0 < R) (a : ℝ) :
    IntegrableOn (fun t : ℝ =>
      ((t - a) ^ (s - 1) * Real.exp (-t * R)) / Real.Gamma s) (Ioi a) :=
  (shifted_integrable hs hR a).div_const _

theorem normalized_shifted_integral {s R : ℝ} (hs : 0 < s) (hR : 0 < R) (a : ℝ) :
    (∫ t : ℝ in Ioi a,
      ((t - a) ^ (s - 1) * Real.exp (-t * R)) / Real.Gamma s) =
        Real.exp (-a * R) / R ^ s := by
  rw [integral_div, shifted_integral hs hR a]
  have hG := (Real.Gamma_pos_of_pos hs).ne'
  field_simp [hG]

theorem sqrt_pow_eq_rpow_half (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Real.sqrt (R ^ d) = R ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hR]
  congr 1
  ring

/-- Exact equality of the real-power Gaussian weight and the reciprocal
square-root convention used by the finite scalar certificates. -/
theorem rpow_neg_half_nat_eq_inv_sqrt (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    R ^ (-(d : ℝ) / 2) = 1 / Real.sqrt (R ^ d) := by
  rw [sqrt_pow_eq_rpow_half d hR, one_div, ← Real.rpow_neg hR]
  congr 1
  ring

theorem normalized_dimension_integrable {d : ℕ} (hd : 0 < d)
    {R : ℝ} (hR : 1 ≤ R) (a : ℝ) :
    IntegrableOn (fun t : ℝ =>
      ((t - a) ^ ((d : ℝ) / 2 - 1) * Real.exp (-t * R)) /
        Real.Gamma ((d : ℝ) / 2)) (Ioi a) := by
  apply normalized_shifted_integrable
  · exact div_pos (Nat.cast_pos.mpr hd) (by norm_num)
  · exact lt_of_lt_of_le zero_lt_one hR

/-- The dimension-dependent Gaussian multiplier, including odd dimensions,
with no assumption on a sum over frequencies. -/
theorem normalized_dimension_integral {d : ℕ} (hd : 0 < d)
    {R : ℝ} (hR : 1 ≤ R) (a : ℝ) :
    (∫ t : ℝ in Ioi a,
      ((t - a) ^ ((d : ℝ) / 2 - 1) * Real.exp (-t * R)) /
        Real.Gamma ((d : ℝ) / 2)) =
      Real.exp (-a * R) / Real.sqrt (R ^ d) := by
  rw [normalized_shifted_integral
    (div_pos (Nat.cast_pos.mpr hd) (by norm_num)) (lt_of_lt_of_le zero_lt_one hR),
    sqrt_pow_eq_rpow_half d (le_trans (by norm_num) hR)]

theorem raw_dimension_integrable {d : ℕ} (hd : 0 < d)
    {R : ℝ} (hR : 1 ≤ R) (a : ℝ) :
    IntegrableOn (fun t : ℝ =>
      (t - a) ^ ((d : ℝ) / 2 - 1) * Real.exp (-t * R)) (Ioi a) :=
  shifted_integrable (div_pos (Nat.cast_pos.mpr hd) (by norm_num))
    (lt_of_lt_of_le zero_lt_one hR) a

theorem raw_dimension_integral {d : ℕ} (hd : 0 < d)
    {R : ℝ} (hR : 1 ≤ R) (a : ℝ) :
    (∫ t : ℝ in Ioi a,
      (t - a) ^ ((d : ℝ) / 2 - 1) * Real.exp (-t * R)) =
      Real.Gamma ((d : ℝ) / 2) *
        (Real.exp (-a * R) / Real.sqrt (R ^ d)) := by
  rw [shifted_integral
    (div_pos (Nat.cast_pos.mpr hd) (by norm_num)) (lt_of_lt_of_le zero_lt_one hR),
    sqrt_pow_eq_rpow_half d (le_trans (by norm_num) hR)]
  ring

end Legacy.BecknerOnofri.GaussianMellinTerm
