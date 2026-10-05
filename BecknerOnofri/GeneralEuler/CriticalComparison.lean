import BecknerOnofri.GeneralEuler.Regularity
import BecknerOnofri.GeneralEuler.WeightedEquation
import Legacy.BecknerOnofri.JacobiTensorMellinComparison
import Legacy.BecknerOnofri.AngularIndexCounts
import Legacy.BecknerOnofri.WeightedStrictComparison

/-! Strict norm comparison for the actual weighted Euler operators. All kernel
properties come from the actual Jacobi heat kernels and Mellin integration. -/
noncomputable section
open MeasureTheory
open Legacy.BecknerOnofri
namespace BecknerOnofri.GeneralEuler.CriticalComparison
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open WienerFourier SmoothFourier SteinerSelection
open AngularMixedTerms JacobiTensor JacobiTensorSpectrum
open BecknerOnofri.GeneralEuler.WeightedEquation PositiveOperatorNeumann

theorem countIndex_single {d : ℕ} (i : Fin d) : countIndex [i] = Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst j; simp [countIndex]
  · simp [countIndex, hj, Ne.symm hj]

theorem criticalInverse_positive {d : ℕ} (a : Index d) (ha : a ≠ 0) :
    Positive (JacobiTensor.measure d) (criticalInverse a ha) :=
  JacobiTensorMellin.inversePower_positive a ha (criticalExponent_pos a ha)

variable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
  (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d}
  (hu : SubcriticalAttainment.Admissible u)
  (hE : Regularity.Data A u)
  (hStR : Steiner (smoothGibbsValue u))
  (hStU : Steiner (fun x => (representative u x).re))

include hd hR hA hu hE hStR hStU
/-- A genuine nonzero first derivative normalizes the Schur bound; the actual
higher mixed kernel is strictly smaller and its inverse is compact. -/
theorem higher_norm_lt_one (is : List (Fin d)) (his : is ≠ []) (hlong : 1 < is.length)
    (i : Fin d) (hi : i ∈ is) (hne : W hd hR hA hu hE hStR [i] ≠ 0) :
    ‖S hd hR hA hu hE hStR is his‖ < 1 := by
  let a := countIndex is
  let a₁ := countIndex [i]
  have ha : a ≠ 0 := BecknerOnofri.GeneralEuler.SpectralIntertwining.countIndex_ne_zero is his
  have ha₁ : a₁ ≠ 0 := BecknerOnofri.GeneralEuler.SpectralIntertwining.countIndex_ne_zero [i] (by simp)
  have hs : (0 : ℝ) < (d : ℝ)/2 := criticalExponent_pos a ha
  have hc : 0 < 1/(2*A) := by positivity
  have hw : ∀ᵐ x ∂JacobiTensor.measure d,
      0 < (sqrtDensityWeight hd hR hA hu hE hStR).value x :=
    ae_of_all _ (sqrtDensity_pos hd hR hA hu hE hStR)
  have hK : ∀ᵐ z ∂(JacobiTensor.measure d).prod (JacobiTensor.measure d),
      0 < JacobiTensorMellin.kernel a₁ ((d:ℝ)/2) z := by
    simpa only [a₁, countIndex_single] using JacobiTensorMellin.kernel_single_pos_ae i hs
  have hKL : ∀ᵐ z ∂(JacobiTensor.measure d).prod (JacobiTensor.measure d),
      JacobiTensorMellin.kernel a ((d:ℝ)/2) z < JacobiTensorMellin.kernel a₁ ((d:ℝ)/2) z := by
    have hh := countIndex_strict_comparison_data is hlong hi
    simpa only [a, a₁, countIndex_single] using
      JacobiTensorMellin.kernel_lt_single_ae (countIndex is) i hh.1 hh.2 hs
  exact WeightedStrictComparison.norm_lt_one (sqrtDensityWeight hd hR hA hu hE hStR)
    hc hw (criticalInverse a₁ ha₁) (criticalInverse a ha)
    (JacobiTensorMellin.kernel a₁ ((d:ℝ)/2)) (JacobiTensorMellin.kernel a ((d:ℝ)/2))
    (JacobiTensorMellin.kernel_aestronglyMeasurable a₁ _)
    (JacobiTensorMellin.kernel_aestronglyMeasurable a _)
    hK (JacobiTensorMellin.kernel_nonnegative_ae a hs) hKL
    (JacobiTensorMellin.kernel_symmetric_ae a₁ _) (JacobiTensorMellin.kernel_symmetric_ae a _)
    (JacobiTensorMellin.kernel_representation a₁ ha₁ hs)
    (JacobiTensorMellin.kernel_representation a ha hs)
    (criticalInverse_compact a ha) (W hd hR hA hu hE hStR [i])
    (W_first_nonnegative hd hR hA hu hE hStR hStU i) hne
    (first_eigen_equation hd hR hA hu hE hStR hStU i)

#print axioms criticalInverse_positive
#print axioms higher_norm_lt_one
end BecknerOnofri.GeneralEuler.CriticalComparison
