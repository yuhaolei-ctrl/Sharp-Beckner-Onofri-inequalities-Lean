module

public import BecknerOnofri.LocalQuarticStatementDefinitions
public import BecknerOnofri.ComplementSobolev

@[expose] public section

/-! Sobolev-valued analyticity is expressed in the physical weighted Fourier
Hilbert space. Every coefficient of the analytic lift is prescribed by the
same actual complementary graph. This is stronger than pointwise Sobolev
regularity of a continuous-space analytic map. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalReductionStatement
open ContinuousGibbs ContinuousFirstShell ContinuousComplement

def SobolevAnalyticComplementGraph (d : ℕ) : Prop :=
  ∃ ψ : ℝ × Coordinates d → complement d,
    AnalyticAt ℝ ψ (1,0) ∧ ψ (1,0)=0 ∧ HasFDerivAt (𝕜 := ℝ) ψ 0 (1,0) ∧
    (∀ᶠ μ in 𝓝 (1:ℝ), ψ (μ,0)=0) ∧
    (∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      projectedEquation (greenContinuous d) (x,ψ x)=0) ∧
    (∀ᶠ x in 𝓝 ((1,(0 : Coordinates d)),(0 : complement d)),
      projectedEquation (greenContinuous d) x=0 ↔ ψ x.1=x.2) ∧
    (∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      SmoothOnTorus (reconstruction d (x.2,ψ x)) ∧
      ∀ s : ℝ, InSobolev s (reconstruction d (x.2,ψ x))) ∧
    (∀ s : ℝ, (fun x => sobolevNorm s (ψ x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2)) ∧
    (∀ s : ℝ, ∃ F : ℝ × Coordinates d → FourierL2 d,
      AnalyticAt ℝ F (1,0) ∧ F (1,0)=0 ∧ HasFDerivAt (𝕜 := ℝ) F 0 (1,0) ∧
      ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), ∀ k : Frequency d,
        F x k=(sobolevScale s k : ℂ)*fourierCoeff (ψ x).val k)

end BecknerOnofri.HighDim.LocalReductionStatement
