import BecknerOnofri.BranchDefinitions
import Legacy.TorusEndpoint.GreenKernelReal

/-! Literal physical-space objects in the two Section 2 gap identities.
The coefficient is A = 1/(2 β c_d), with c_d = (2π)^d / σ_d.
The mean of the Green kernel is zero, so its convolution with ρ also equals
its convolution with ρ minus the uniform density. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.Gap

def coefficient (d : ℕ) (β : ℝ) : ℝ :=
  spectralThreshold d/(2*β*(2*Real.pi)^d)

def densityPotential {d : ℕ} (β : ℝ) (f : Torus d → ℝ) : Torus d → ℝ :=
  fun x => β*∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*f y ∂torusMeasure d

def densityValue {d : ℕ} (β : ℝ) (f : Torus d → ℝ) : ℝ :=
  β/2*(∫ x,∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*f x*f y
    ∂torusMeasure d ∂torusMeasure d) - ∫ x,f x*Real.log (f x) ∂torusMeasure d

def potentialValue {d : ℕ} (β : ℝ) (u : Torus d → ℝ) : ℝ :=
  Real.log (∫ x,Real.exp (u x) ∂torusMeasure d)-coefficient d β*potentialEnergy u

def relativeEntropy {d : ℕ} (f g : Torus d → ℝ) : ℝ :=
  ∫ x,f x*Real.log (f x/g x) ∂torusMeasure d

end BecknerOnofri.HighDim.Gap
