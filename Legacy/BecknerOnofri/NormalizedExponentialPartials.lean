import Legacy.BecknerOnofri.MixedExponentialPolynomial
import Legacy.BecknerOnofri.BernsteinPositiveCoefficients

/-! The actual mixed partials of a normalized exponential. -/
noncomputable section
namespace Legacy.BecknerOnofri.NormalizedExponentialPartials
open Set FiniteDifferences MixedExponentialDerivatives
open scoped ContDiff

theorem mixedPartial_congr {d : ℕ} (is : List (Fin d)) {f g : Space d → ℝ}
    (he : EqOn f g (closedCube d)) : EqOn (mixedPartial is f) (mixedPartial is g) (closedCube d) := by
  induction is generalizing f g with
  | nil => exact he
  | cons i is ih => exact ih (fun x hx => coordinateDerivative_congr i he hx)

theorem coordinateDerivative_const_mul {d : ℕ} (i : Fin d) (c : ℝ) {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative i (fun y => c*f y) x = c*coordinateDerivative i f x := by
  rw [coordinateDerivative_mul i contDiffOn_const hf hx, coordinateDerivative_const]
  ring

theorem mixedPartial_const_mul {d : ℕ} (is : List (Fin d)) (c : ℝ) {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) {x : Space d} (hx : x ∈ closedCube d) :
    mixedPartial is (fun y => c*f y) x = c*mixedPartial is f x := by
  induction is generalizing f x with
  | nil => rfl
  | cons i is ih =>
    change mixedPartial is (coordinateDerivative i (fun y => c*f y)) x = _
    rw [mixedPartial_congr is (fun y hy => coordinateDerivative_const_mul i c hf hy) hx]
    exact ih (contDiffOn_coordinateDerivative hf i) hx

theorem normalized_exp_nonnegative_mixed {d : ℕ} {u f : Space d → ℝ} {Z : ℝ}
    (hZ : 0 < Z) (hu : ContDiffOn ℝ ∞ u (closedCube d))
    (hf : EqOn f (fun y => Real.exp (u y)/Z) (closedCube d))
    (hpos : ∀ is : List (Fin d), is ≠ [] → ∀ x ∈ closedCube d, 0 ≤ mixedPartial is u x) :
    BernsteinPositiveCoefficients.NonnegativeMixedPartials f := by
  intro is x hx
  have he : EqOn f (fun y => Z⁻¹*Real.exp (u y)) (closedCube d) := by
    intro y hy
    rw [hf hy]
    ring
  rw [mixedPartial_congr is he hx, mixedPartial_const_mul is Z⁻¹ hu.exp hx]
  apply mul_nonneg (inv_nonneg.mpr hZ.le)
  by_cases his : is = []
  · subst is
    exact (Real.exp_pos _).le
  · rw [mixedPartial_exp_formula hu is his hx]
    apply mul_nonneg (Real.exp_pos _).le
    apply add_nonneg (hpos is his x hx)
    apply bell_remainder_nonneg
    intro js hjs _
    exact hpos js (by intro he; subst js; simp at hjs) x hx

#print axioms normalized_exp_nonnegative_mixed
end Legacy.BecknerOnofri.NormalizedExponentialPartials
