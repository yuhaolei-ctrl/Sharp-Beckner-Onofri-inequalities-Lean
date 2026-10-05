import BecknerOnofri.BranchDefinitions

/-! The stationary branch, full-domain Hessian and Sobolev profile, separated
from the additional local-maximum and all-support classification assertions. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.LocalReductionStatement

structure StationaryHessian {d : ℕ} (β : ℝ) (u : Torus d → ℝ) : Prop where
  smooth : SmoothOnTorus u
  sobolev : ∀ s : ℝ, InSobolev s u
  criticalSobolev : InCriticalSobolev u
  meanZero : MeanZero u
  stationary : ∀ k : NonzeroFrequency d,
    (frequencyLength k.val^d : ℂ)*fourierCoeff u k.val =
      (β/spectralThreshold d : ℝ)*fourierCoeff (normalizedGibbs u) k.val
  fullModes : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0
  tangentIndependent : ∀ a : Fin d → ℝ,
    tangentCombination u a =ᵐ[torusMeasure d] (fun _ => 0) → a=0
  hessianNonpos : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
    secondVariation β u h ≤ 0
  hessianKernel : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
    (secondVariation β u h=0 ↔ ∃ a : Fin d → ℝ,
      h =ᵐ[torusMeasure d] tangentCombination u a)
  normalCoercivity : ∃ c : ℝ, 0<c ∧ ∀ h : Torus d → ℝ,
    InCriticalSobolev h → InSobolev ((d:ℝ)/2) h → MeanZero h →
    (∀ j : Fin d, (∫ x, h x*coordinateDerivative u j x ∂torusMeasure d)=0) →
    secondVariation β u h ≤ -c*sobolevNorm ((d:ℝ)/2) h^2

def FullModeStationaryBranch (d : ℕ) : Prop :=
  ∃ ε : ℝ, 0<ε ∧ ∃ U : ℝ → Torus d → ℝ,
    (∀ β : ℝ, spectralThreshold d<β → β<spectralThreshold d+ε →
      StationaryHessian β (U β)) ∧
    (∀ s : ℝ, ∃ η C : ℝ, 0<η ∧ η≤ε ∧ 0≤C ∧
      ∀ β : ℝ, spectralThreshold d<β → β<spectralThreshold d+η →
        ∀ a : Torus d, InSobolev s (branchRemainder β (U β) a) ∧
          sobolevNorm s (branchRemainder β (U β) a) ≤ C*onsetDelta d β)

end BecknerOnofri.HighDim.LocalReductionStatement
