module

public import Legacy.BecknerOnofri.PolarizationIntegral

@[expose] public section

/-! Polarization of actual Haar probability densities, with no additional normalization assumption. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.CoordinatePolarization

theorem polarize_nonneg_ae {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ}
    (hf : ∀ᵐ x ∂torusMeasure d, 0 ≤ f x) : ∀ᵐ x ∂torusMeasure d, 0 ≤ polarize i a f x := by
  filter_upwards [hf, (reflection_measurePreserving i a).quasiMeasurePreserving.ae hf] with x hx hr
  rcases polarize_value_or_reflected i a f x with hp | hp <;> rw [hp] <;> assumption

def density {d : ℕ} (i : Fin d) (a : ℝ) (rho : ProbabilityDensity d) : ProbabilityDensity d where
  value := polarize i a rho.value
  nonneg := polarize_nonneg_ae i a rho.nonneg
  integrable := polarize_integrable i a rho.integrable
  mass := (polarize_integral i a rho.integrable).trans rho.mass

theorem density_finiteEntropy {d : ℕ} (i : Fin d) (a : ℝ) {rho : ProbabilityDensity d}
    (hr : rho.FiniteEntropy) : (density i a rho).FiniteEntropy :=
  polarize_entropy_integrable i a rho.integrable.aestronglyMeasurable hr

theorem density_entropy {d : ℕ} (i : Fin d) (a : ℝ) {rho : ProbabilityDensity d}
    (hr : rho.FiniteEntropy) : densityEntropy (density i a rho).value = densityEntropy rho.value :=
  polarize_entropy i a rho.integrable.aestronglyMeasurable hr

theorem density_memLp_two {d : ℕ} (i : Fin d) (a : ℝ) {rho : ProbabilityDensity d}
    (hr : MemLp rho.value 2 (torusMeasure d)) : MemLp (density i a rho).value 2 (torusMeasure d) :=
  polarize_memLp_two i a hr

theorem density_pairing_ge {d : ℕ} (i : Fin d) (a : ℝ) (K : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry K)) {C : ℝ} (hC : ∀ x y, ‖K x y‖ ≤ C)
    (hK : ∀ x y, K (reflection i a x) (reflection i a y) = K x y)
    (hmono : ∀ x ∈ halfTorus i a, ∀ y ∈ halfTorus i a, K x (reflection i a y) ≤ K x y)
    (rho : ProbabilityDensity d) : pairing K rho.value ≤ pairing K (density i a rho).value :=
  pairing_polarize_le_bounded i a K hmeas hC hK hmono rho.integrable

#print axioms density_finiteEntropy
#print axioms density_pairing_ge
end Legacy.BecknerOnofri.CoordinatePolarization
