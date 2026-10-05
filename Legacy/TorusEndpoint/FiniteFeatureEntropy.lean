import Legacy.TorusEndpoint.EntropyVariational

/-!
# Finite real feature tests give a finite entropy lower bound

The exponential integral upper bound is an explicit hypothesis here.
The test functions, their pairing with the density, and the finite
optimization are constructed and proved, not supplied as opaque facts.
No torus Fourier estimate is asserted by this general-purpose module.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.TorusEndpoint

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Given a quadratic logarithmic exponential bound for every finite real
feature test, entropy controls the corresponding weighted squared moments. -/
theorem entropy_ge_finite_feature_energy [IsProbabilityMeasure μ]
    (s : Finset ι) (phi : ι → X → ℝ) (a B : ι → ℝ) {rho : X → ℝ}
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ rho x)
    (h_mass : (∫ x, rho x ∂μ) = 1)
    (h_rho : Integrable rho μ)
    (h_entropy : Integrable (fun x => rho x * Real.log (rho x)) μ)
    (h_phi : ∀ i ∈ s, Measurable (phi i))
    (h_bound : ∀ i ∈ s, ∀ x, ‖phi i x‖ ≤ B i)
    (h_a : ∀ i ∈ s, 0 < a i)
    (h_exp : ∀ t : ι → ℝ,
      Real.log (∫ x, Real.exp (∑ i ∈ s, 2 * t i * phi i x) ∂μ) ≤
        ∑ i ∈ s, a i * (t i)^2) :
    (∑ i ∈ s, (∫ x, rho x * phi i x ∂μ)^2 / a i) ≤
      ∫ x, rho x * Real.log (rho x) ∂μ := by
  have h_moments : ∀ i ∈ s, Integrable (fun x => rho x * phi i x) μ := by
    intro i hi
    exact h_rho.mul_bdd (h_phi i hi).aestronglyMeasurable
      (ae_of_all _ (h_bound i hi))
  apply finite_quadratic_dual_bound s a (fun i => ∫ x, rho x * phi i x ∂μ)
    (∫ x, rho x * Real.log (rho x) ∂μ) h_a
  intro t
  have h_test_meas : Measurable (fun x => ∑ i ∈ s, 2 * t i * phi i x) :=
    Finset.measurable_fun_sum s (fun i hi => measurable_const.mul (h_phi i hi))
  have h_test_bound : ∀ x,
      ‖∑ i ∈ s, 2 * t i * phi i x‖ ≤ ∑ i ∈ s, ‖2 * t i‖ * B i := by
    intro x
    calc
      ‖∑ i ∈ s, 2 * t i * phi i x‖ ≤ ∑ i ∈ s, ‖2 * t i * phi i x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ s, ‖2 * t i‖ * B i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (h_bound i hi x) (norm_nonneg _)
  have h_pairing :
      (∫ x, rho x * (∑ i ∈ s, 2 * t i * phi i x) ∂μ) =
        ∑ i ∈ s, 2 * (∫ x, rho x * phi i x ∂μ) * t i := by
    calc
      (∫ x, rho x * (∑ i ∈ s, 2 * t i * phi i x) ∂μ) =
          ∫ x, ∑ i ∈ s, (2 * t i) * (rho x * phi i x) ∂μ := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        change rho x * (∑ i ∈ s, 2 * t i * phi i x) =
          ∑ i ∈ s, (2 * t i) * (rho x * phi i x)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i ∈ s, ∫ x, (2 * t i) * (rho x * phi i x) ∂μ :=
        integral_finsetSum s (fun i hi => (h_moments i hi).const_mul (2 * t i))
      _ = ∑ i ∈ s, 2 * (∫ x, rho x * phi i x ∂μ) * t i := by
        simp only [integral_const_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have h_gibbs := entropy_variational_bounded h_nonneg h_mass h_rho h_entropy
    h_test_meas (ae_of_all _ h_test_bound)
  rw [h_pairing] at h_gibbs
  rw [Finset.sum_sub_distrib]
  linarith [h_exp t]

end Legacy.TorusEndpoint
