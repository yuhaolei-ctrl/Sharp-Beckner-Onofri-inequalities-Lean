import BecknerOnofri.RawGapIdentities

/-! Section 2 gap identities with the manuscript's arbitrary positive A.
Here β = σ_d/(2 A (2π)^d) = (2 A c_d)⁻¹. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.Gap

lemma coefficient_pos {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    0 < coefficient d A := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  unfold coefficient
  positivity

lemma coefficient_involutive {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    coefficient d (coefficient d A) = A := by
  have hσ : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos hd).ne'
  have hc : (2*Real.pi)^d ≠ 0 := (pow_pos (by positivity : 0 < 2*Real.pi) d).ne'
  unfold coefficient
  field_simp

/-- Exact primal gap, including the square-completion remainder in physical energy. -/
theorem primal_gap_paper {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) (hm : MeanZero u) :
    Real.log (∫ x,Real.exp (u x) ∂torusMeasure d)-A*potentialEnergy u =
      densityValue (coefficient d A) (normalizedGibbs u) -
        A*potentialEnergy (u-densityPotential (coefficient d A) (normalizedGibbs u)) := by
  simpa only [potentialValue,coefficient_involutive hd hA] using
    primal_gap hd (coefficient_pos hd hA) u hu hm

/-- Exact dual gap for every finite-entropy probability density. -/
theorem dual_gap_paper {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    densityValue (coefficient d A) ρ.value =
      Real.log (∫ x,Real.exp (densityPotential (coefficient d A) ρ.value x) ∂torusMeasure d)-
        A*potentialEnergy (densityPotential (coefficient d A) ρ.value)-
        relativeEntropy ρ.value (normalizedGibbs (densityPotential (coefficient d A) ρ.value)) := by
  simpa only [potentialValue,coefficient_involutive hd hA] using
    dual_gap hd (coefficient_pos hd hA) ρ hρ

#print axioms primal_gap_paper
#print axioms dual_gap_paper
end BecknerOnofri.HighDim.Gap
