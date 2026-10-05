import BecknerOnofri.EntropyTailCertifiedScalar
import BecknerOnofri.EntropyEndpointCertificates

/-! The scalar input is now proved by the complete kernel-checked heat
certificate. Only the global convex minorant and spin inequality remain
explicit numerical hypotheses in this analytic endpoint assembly. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.EntropySpinEndpoint
variable
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t)
    (hspin : ∀ q : Spin.Count → ℝ, Spin.Feasible q → Spin.mean q ∈ Icc (0 : ℝ) 1 →
      (Spin.mean q)^4/250 ≤ Spin.functional q+12*ψ (Spin.mean q))
include ψ hc hcv hminor hspin

theorem density_endpoint {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2*entropy ρ) :=
  EntropyEndpointCertificates.density_endpoint EntropyTail.scalarTail_le_budget ψ hc hcv hminor hspin hd ρ hρ

theorem density_rigidity {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2*entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] (fun _ => 1) :=
  EntropyEndpointCertificates.density_rigidity EntropyTail.scalarTail_le_budget ψ hc hcv hminor hspin hd ρ hρ

#print axioms density_endpoint
#print axioms density_rigidity
end BecknerOnofri.HighDim.EntropySpinEndpoint
