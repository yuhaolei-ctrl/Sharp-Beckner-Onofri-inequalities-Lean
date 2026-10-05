import Legacy.TorusEndpoint.EntropyVariational
import Legacy.TorusEndpoint.ExtendedEntropy
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Unconditional entropy analysis for the dimension-ten proof

These theorems concern actual integrals on probability spaces. No endpoint
inequality, optimizer existence, PDE regularity, rearrangement theorem, or
cosine-mixture representation is assumed or asserted.

The finite-product Gibbs bound permits correlated joint densities. It is the
analytic tensorization step needed after one-dimensional logarithmic partition
estimates have been proved separately.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.D10

section Gibbs

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]

/-- The relative entropy integrand with respect to a strictly positive Gibbs
reference. Its integral is defined only under the explicit integrability
hypotheses of the theorems below. -/
noncomputable def gibbsRelativeEntropy (rho u : X → ℝ) : ℝ :=
  ∫ x, rho x * (Real.log (rho x) -
    (u x - Real.log (∫ y, Real.exp (u y) ∂μ))) ∂μ

omit [IsProbabilityMeasure μ] in
/-- Exact Gibbs gap identity. The density may vanish, and its entropy need
not be continuous or bounded. -/
theorem gibbsRelativeEntropy_eq
    {rho u : X → ℝ}
    (h_mass : (∫ x, rho x ∂μ) = 1)
    (h_rho : Integrable rho μ)
    (h_entropy : Integrable (fun x => rho x * Real.log (rho x)) μ)
    (h_product : Integrable (fun x => rho x * u x) μ) :
    gibbsRelativeEntropy (μ := μ) rho u =
      (∫ x, rho x * Real.log (rho x) ∂μ) -
      (∫ x, rho x * u x ∂μ) + Real.log (∫ x, Real.exp (u x) ∂μ) := by
  unfold gibbsRelativeEntropy
  simp only [sub_sub_eq_add_sub, mul_add, mul_sub]
  change (∫ x, (((fun x : X => rho x * Real.log (rho x)) +
    (fun x : X => rho x * Real.log (∫ y, Real.exp (u y) ∂μ))) -
    (fun x : X => rho x * u x)) x ∂μ) = _
  rw [integral_sub' (h_entropy.add (h_rho.mul_const
    (Real.log (∫ y, Real.exp (u y) ∂μ)))) h_product,
    integral_add' h_entropy (h_rho.mul_const _), integral_mul_const, h_mass]
  ring

/-- Nonnegativity of the exact Gibbs gap, with no boundedness assumption on
the test function. All three integrability hypotheses are mathematical
hypotheses, so totalized nonintegrable Bochner integrals are never used. -/
theorem gibbsRelativeEntropy_nonneg
    {rho u : X → ℝ}
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ rho x)
    (h_mass : (∫ x, rho x ∂μ) = 1)
    (h_rho : Integrable rho μ)
    (h_entropy : Integrable (fun x => rho x * Real.log (rho x)) μ)
    (h_product : Integrable (fun x => rho x * u x) μ)
    (h_exp : Integrable (fun x => Real.exp (u x)) μ) :
    0 ≤ gibbsRelativeEntropy (μ := μ) rho u := by
  rw [gibbsRelativeEntropy_eq h_mass h_rho h_entropy h_product]
  have h := Legacy.TorusEndpoint.entropy_variational_of_integrable
    h_nonneg h_mass h_rho h_entropy h_product h_exp
  linarith

/-- A bounded measurable exponential is integrable on a probability space. -/
theorem integrable_exp_of_bounded {u : X → ℝ} {B : ℝ}
    (hu : Measurable u) (hB : ∀ x, ‖u x‖ ≤ B) :
    Integrable (fun x => Real.exp (u x)) μ := by
  apply (integrable_const (Real.exp B)).mono'
    ((Real.continuous_exp.measurable.comp hu).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖Real.exp (u x)‖ ≤ Real.exp B
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB x)

end Gibbs

section Tensor

variable {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {μ : (i : ι) → Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- Exact factorization of the partition function for a sum of coordinate
tests. This is a statement about the reference product measure, not an
independence assertion about the joint density. -/
theorem tensor_partition (u : (i : ι) → X i → ℝ) :
    (∫ x, Real.exp (∑ i, u i (x i)) ∂Measure.pi μ) =
      ∏ i, ∫ y, Real.exp (u i y) ∂μ i := by
  simp_rw [Real.exp_sum]
  exact integral_fintype_prod_eq_prod (μ := μ) (fun i y => Real.exp (u i y))

/-- Logarithmic factorization, with integrability ensuring that each genuine
partition function is strictly positive. -/
theorem tensor_log_partition (u : (i : ι) → X i → ℝ)
    (hu : ∀ i, Integrable (fun y => Real.exp (u i y)) (μ i)) :
    Real.log (∫ x, Real.exp (∑ i, u i (x i)) ∂Measure.pi μ) =
      ∑ i, Real.log (∫ y, Real.exp (u i y) ∂μ i) := by
  rw [tensor_partition]
  exact Real.log_prod (fun i _ => (integral_exp_pos (hu i)).ne')

/-- Tensorized Gibbs variational inequality for an arbitrary, possibly
correlated density on a finite product probability space. There is no
independence hypothesis on `rho`. -/
theorem tensor_entropy_variational
    {rho : ((i : ι) → X i) → ℝ}
    (h_nonneg : ∀ᵐ x ∂Measure.pi μ, 0 ≤ rho x)
    (h_mass : (∫ x, rho x ∂Measure.pi μ) = 1)
    (h_rho : Integrable rho (Measure.pi μ))
    (h_entropy : Integrable (fun x => rho x * Real.log (rho x)) (Measure.pi μ))
    (u : (i : ι) → X i → ℝ) (B : ι → ℝ)
    (hu : ∀ i, Measurable (u i))
    (hB : ∀ i y, ‖u i y‖ ≤ B i) :
    (∑ i, ((∫ x, rho x * u i (x i) ∂Measure.pi μ) -
      Real.log (∫ y, Real.exp (u i y) ∂μ i))) ≤
      ∫ x, rho x * Real.log (rho x) ∂Measure.pi μ := by
  have hmeas : Measurable (fun x : (i : ι) → X i => ∑ i, u i (x i)) := by
    exact Finset.measurable_sum _ (fun i _ => (hu i).comp (measurable_pi_apply i))
  have hbound : ∀ x : (i : ι) → X i, ‖∑ i, u i (x i)‖ ≤ ∑ i, B i := by
    intro x
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hB i (x i)))
  have hprod (i : ι) : Integrable (fun x => rho x * u i (x i)) (Measure.pi μ) :=
    h_rho.mul_bdd ((hu i).comp (measurable_pi_apply i)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => hB i (x i)))
  have h := Legacy.TorusEndpoint.entropy_variational_bounded h_nonneg h_mass h_rho h_entropy
    hmeas (Filter.Eventually.of_forall hbound)
  have h_exp (i : ι) : Integrable (fun y => Real.exp (u i y)) (μ i) :=
    integrable_exp_of_bounded (hu i) (hB i)
  rw [tensor_log_partition u h_exp] at h
  simpa only [Finset.mul_sum, integral_finsetSum _ (fun i _ => hprod i),
    Finset.sum_sub_distrib] using h

end Tensor

end Legacy.D10
