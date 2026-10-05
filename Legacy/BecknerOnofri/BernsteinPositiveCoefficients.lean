import Legacy.BecknerOnofri.FiniteDifferenceSmooth
import Legacy.BecknerOnofri.FiniteDifferenceMeanValue
import Legacy.BecknerOnofri.TensorBernsteinCoefficientLimits
import Legacy.BecknerOnofri.PositivePolynomialLimit

/-! Positive Taylor expansions from actual smooth coordinate derivatives.
The derivatives are iterated Mathlib `fderivWithin` values, in one fixed order
for each multiindex. No coefficient sign, coefficient limit, or power-series
representation is assumed. -/
noncomputable section
open Finset Set Filter
open scoped BigOperators Topology ContDiff unitInterval
namespace Legacy.BecknerOnofri.BernsteinPositiveCoefficients
open FiniteDifferences

/-- Restriction of an ambient real function to the closed cube. -/
def restriction {d : ℕ} (f : Space d → ℝ) : TensorBernstein.Cube d → ℝ :=
  fun y => f (fun i => (y i : ℝ))

/-- Absolute monotonicity is stated using actual iterated coordinate derivatives. -/
def NonnegativeMixedPartials {d : ℕ} (f : Space d → ℝ) : Prop :=
  ∀ is x, x ∈ closedCube d → 0 ≤ mixedPartial is f x

/-- The Taylor coefficient in the fixed coordinate ordering chosen for a multiindex. -/
def taylorCoefficient {d : ℕ} (f : Space d → ℝ) (a : Index d) : ℝ :=
  mixedPartial (directions a) f 0 / (∏ i, ((a i).factorial : ℝ))

theorem restriction_continuous {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) : Continuous (restriction f) := by
  apply hf.continuousOn.comp_continuous (by fun_prop)
  intro y
  exact ⟨fun i => (y i).property.1, fun i => (y i).property.2⟩

theorem coefficient_nonneg {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (hpos : NonnegativeMixedPartials f)
    {m : ℕ} (hm : 0 < m) (a : Index d) :
    0 ≤ (TensorBernstein.polynomial m (restriction f)).coeff a := by
  by_cases ha : ∀ i, a i ≤ m
  · unfold restriction
    rw [TensorBernsteinCoefficients.polynomial_coefficient_difference m f a ha]
    apply mul_nonneg (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
    exact rectangularDifference_nonneg_jet a (coordinateJet_of_contDiffOn hf) hpos
      (by positivity) 0 (fits_zero_inverse a hm ha)
  · rw [TensorBernsteinCoefficients.polynomial_coefficient_outside m (restriction f) a ha]

theorem coefficient_tendsto {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (a : Index d) :
    Tendsto (fun m => (TensorBernstein.polynomial m (restriction f)).coeff a)
      atTop (𝓝 (taylorCoefficient f a)) := by
  have hh := (TensorBernsteinCoefficientLimits.normalization_tendsto a).mul
    (scaledDifference_tendsto_nat_jet a (coordinateJet_of_contDiffOn hf))
  have he : (1 / (∏ i, ((a i).factorial : ℝ))) * mixedPartial (directions a) f 0 =
      taylorCoefficient f a := by simp [taylorCoefficient, div_eq_mul_inv, mul_comm]
  rw [he] at hh
  apply hh.congr'
  filter_upwards [TensorBernsteinCoefficientLimits.eventually_in_box a,
    eventually_ge_atTop 1] with m hm hm1
  unfold restriction
  rw [TensorBernsteinCoefficients.polynomial_coefficient_difference m f a hm]
  unfold TensorBernsteinCoefficientLimits.normalization
  have hn : (1/(m : ℝ))^degree a ≠ 0 := by positivity
  simp only [mixedPartial_nil]
  field_simp

theorem coefficient_succ_tendsto {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (a : Index d) :
    Tendsto (fun m => (TensorBernstein.polynomial (m+1) (restriction f)).coeff a)
      atTop (𝓝 (taylorCoefficient f a)) :=
  (coefficient_tendsto hf a).comp (tendsto_add_atTop_nat 1)

theorem taylorCoefficient_nonneg {d : ℕ} {f : Space d → ℝ}
    (hpos : NonnegativeMixedPartials f) (a : Index d) : 0 ≤ taylorCoefficient f a :=
  div_nonneg (hpos _ _ (by simp [closedCube])) (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))

/-- The positive Taylor series equals the function at every point of the closed cube. -/
theorem positiveTaylor_hasSum {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (hpos : NonnegativeMixedPartials f)
    (y : TensorBernstein.Cube d) :
    HasSum (fun a => taylorCoefficient f a * PositivePolynomialLimit.monomialValue a y)
      (restriction f y) := by
  exact PositivePolynomialLimit.hasSum_representation
    (fun m a => coefficient_nonneg hf hpos (Nat.succ_pos m) a)
    (fun m => TensorBernstein.polynomial_eval_one (Nat.succ_ne_zero m) (restriction f))
    (coefficient_succ_tendsto hf) (restriction_continuous hf)
    ((TensorBernstein.polynomial_succ_uniform (restriction f) (restriction_continuous hf)).tendsto_at) y

/-- The sum of the nonnegative Taylor coefficients is exactly the value at the corner. -/
theorem positiveTaylor_mass {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (hpos : NonnegativeMixedPartials f) :
    HasSum (taylorCoefficient f) (f 1) := by
  exact PositivePolynomialLimit.coefficient_hasSum_mass
    (fun m a => coefficient_nonneg hf hpos (Nat.succ_pos m) a)
    (fun m => TensorBernstein.polynomial_eval_one (Nat.succ_ne_zero m) (restriction f))
    (coefficient_succ_tendsto hf) (restriction_continuous hf)
    ((TensorBernstein.polynomial_succ_uniform (restriction f) (restriction_continuous hf)).tendsto_at)

/-- Uniform convergence holds on the whole closed cube, including its boundary. -/
theorem positiveTaylor_uniform {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (hpos : NonnegativeMixedPartials f) :
    TendstoUniformly (fun s : Finset (Index d) => fun y : TensorBernstein.Cube d =>
      ∑ a ∈ s, taylorCoefficient f a * PositivePolynomialLimit.monomialValue a y)
      (restriction f) atTop := by
  exact PositivePolynomialLimit.uniform_representation
    (fun m a => coefficient_nonneg hf hpos (Nat.succ_pos m) a)
    (fun m => TensorBernstein.polynomial_eval_one (Nat.succ_ne_zero m) (restriction f))
    (coefficient_succ_tendsto hf) (restriction_continuous hf)
    ((TensorBernstein.polynomial_succ_uniform (restriction f) (restriction_continuous hf)).tendsto_at)

#print axioms coefficient_nonneg
#print axioms coefficient_tendsto
#print axioms positiveTaylor_hasSum
#print axioms positiveTaylor_mass
#print axioms positiveTaylor_uniform

end Legacy.BecknerOnofri.BernsteinPositiveCoefficients
