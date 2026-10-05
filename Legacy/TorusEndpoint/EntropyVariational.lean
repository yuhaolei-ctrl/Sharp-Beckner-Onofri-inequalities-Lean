import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Entropy variational lower bound and finite quadratic optimization

This module proves common analytic ingredients, not the torus endpoint.
Entropy here is the real Bochner integral of `rho * log rho`; its
integrability is an explicit finite-entropy hypothesis. In particular, the
default value of the Bochner integral on a nonintegrable function is never
used to represent infinite entropy. Real.log 0 = 0 gives the usual 0 log 0
convention after multiplication by rho.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.TorusEndpoint

/-- Scalar entropy--exponential Young inequality, including a zero density. -/
theorem entropy_young (r u : ℝ) (hr : 0 ≤ r) :
    r * u ≤ r * Real.log r - r + Real.exp u := by
  by_cases hz : r = 0
  · simpa [hz] using (Real.exp_nonneg u)
  have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  have h := Real.add_one_le_exp (u - Real.log r)
  rw [Real.exp_sub, Real.exp_log hp] at h
  have hm := (le_div_iff₀ hp).mp h
  nlinarith

section Measure

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Gibbs' variational lower bound under explicit integrability assumptions.
Only the density is normalized; no boundedness of u is imposed in this form. -/
theorem entropy_variational_of_integrable [IsProbabilityMeasure μ]
    {rho u : X → ℝ}
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ rho x)
    (h_mass : (∫ x, rho x ∂μ) = 1)
    (h_rho : Integrable rho μ)
    (h_entropy : Integrable (fun x => rho x * Real.log (rho x)) μ)
    (h_product : Integrable (fun x => rho x * u x) μ)
    (h_exp : Integrable (fun x => Real.exp (u x)) μ) :
    (∫ x, rho x * u x ∂μ) - Real.log (∫ x, Real.exp (u x) ∂μ) ≤
      ∫ x, rho x * Real.log (rho x) ∂μ := by
  let Z : ℝ := ∫ x, Real.exp (u x) ∂μ
  have hZ : 0 < Z := integral_exp_pos h_exp
  have h_shift : Integrable (fun x => rho x * (u x - Real.log Z)) μ := by
    have h_eq : (fun x => rho x * (u x - Real.log Z)) =
        (fun x => rho x * u x) - (fun x => rho x * Real.log Z) := by
      funext x
      exact mul_sub (rho x) (u x) (Real.log Z)
    rw [h_eq]
    exact h_product.sub (h_rho.mul_const (Real.log Z))
  have h_normalized : Integrable (fun x => Real.exp (u x - Real.log Z)) μ := by
    simpa only [Real.exp_sub, Real.exp_log hZ, div_eq_mul_inv] using
      h_exp.mul_const Z⁻¹
  have h_normalized_mass : (∫ x, Real.exp (u x - Real.log Z) ∂μ) = 1 := by
    simp only [Real.exp_sub, Real.exp_log hZ, div_eq_mul_inv, integral_mul_const]
    change Z * Z⁻¹ = 1
    exact mul_inv_cancel₀ hZ.ne'
  have h_pointwise : ∀ᵐ x ∂μ,
      rho x * (u x - Real.log Z) ≤
        (rho x * Real.log (rho x) - rho x) + Real.exp (u x - Real.log Z) := by
    filter_upwards [h_nonneg] with x hx
    exact entropy_young (rho x) (u x - Real.log Z) hx
  have h_integral := integral_mono_ae h_shift
    ((h_entropy.sub h_rho).add h_normalized) h_pointwise
  rw [integral_add' (h_entropy.sub h_rho) h_normalized,
    integral_sub' h_entropy h_rho, h_normalized_mass, h_mass] at h_integral
  have h_shift_integral :
      (∫ x, rho x * (u x - Real.log Z) ∂μ) =
        (∫ x, rho x * u x ∂μ) - Real.log Z := by
    simp only [mul_sub]
    rw [integral_sub h_product (h_rho.mul_const (Real.log Z)), integral_mul_const,
      h_mass, one_mul]
  rw [h_shift_integral] at h_integral
  simpa only [sub_add_cancel] using h_integral

/-- For a bounded measurable real test, all additional integrability and
partition-function positivity conditions are discharged within the proof. -/
theorem entropy_variational_bounded [IsProbabilityMeasure μ]
    {rho u : X → ℝ} {B : ℝ}
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ rho x)
    (h_mass : (∫ x, rho x ∂μ) = 1)
    (h_rho : Integrable rho μ)
    (h_entropy : Integrable (fun x => rho x * Real.log (rho x)) μ)
    (h_u : Measurable u)
    (h_bound : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) :
    (∫ x, rho x * u x ∂μ) - Real.log (∫ x, Real.exp (u x) ∂μ) ≤
      ∫ x, rho x * Real.log (rho x) ∂μ := by
  have h_product : Integrable (fun x => rho x * u x) μ :=
    h_rho.mul_bdd h_u.aestronglyMeasurable h_bound
  have h_exp_meas : AEStronglyMeasurable (fun x => Real.exp (u x)) μ :=
    (Real.continuous_exp.measurable.comp h_u).aestronglyMeasurable
  have h_exp : Integrable (fun x => Real.exp (u x)) μ := by
    apply (integrable_const (Real.exp B)).mono' h_exp_meas
    filter_upwards [h_bound] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hx)
  exact entropy_variational_of_integrable h_nonneg h_mass h_rho h_entropy
    h_product h_exp

end Measure

section Quadratic

variable {ι : Type*}

/-- Completing the square gives the finite weighted quadratic upper bound. -/
theorem finite_quadratic_le (s : Finset ι) (a b t : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    (∑ i ∈ s, (2 * b i * t i - a i * (t i)^2)) ≤
      ∑ i ∈ s, (b i)^2 / a i := by
  apply Finset.sum_le_sum
  intro i hi
  apply (le_div_iff₀ (ha i hi)).mpr
  nlinarith [sq_nonneg (a i * t i - b i)]

/-- The finite upper bound is attained at the explicit optimizer b/a. -/
theorem finite_quadratic_optimizer (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    (∑ i ∈ s, (2 * b i * (b i / a i) - a i * (b i / a i)^2)) =
      ∑ i ∈ s, (b i)^2 / a i := by
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [(ha i hi).ne']
  ring

/-- If every finite quadratic test is bounded by E, optimize without
invoking any infinite-dimensional duality or exchanging limits. -/
theorem finite_quadratic_dual_bound (s : Finset ι) (a b : ι → ℝ) (E : ℝ)
    (ha : ∀ i ∈ s, 0 < a i)
    (h_tests : ∀ t : ι → ℝ,
      (∑ i ∈ s, (2 * b i * t i - a i * (t i)^2)) ≤ E) :
    (∑ i ∈ s, (b i)^2 / a i) ≤ E := by
  have h := h_tests (fun i => b i / a i)
  rw [finite_quadratic_optimizer s a b ha] at h
  exact h

end Quadratic

end Legacy.TorusEndpoint
