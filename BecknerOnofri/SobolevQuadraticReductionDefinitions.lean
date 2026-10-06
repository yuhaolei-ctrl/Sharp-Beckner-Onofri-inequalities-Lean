module

public import BecknerOnofri.LocalQuarticStatementDefinitions

@[expose] public section

/-! The two actual H^s Taylor expansions in Section 5, at the critical
parameter. Both use one locally unique complementary graph and one quadratic
term specified by its physical Fourier coefficients. This assertion does not
claim H^s-valued analyticity of the graph. -/
noncomputable section
open Classical
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalReductionStatement
open ContinuousGibbs ContinuousFirstShell ContinuousComplement

/-- The projected resolvent formula is explicit, rather than an implementation
witness or an assumed inverse operator. Zero and first-shell modes are removed. -/
def QuadraticSlavingCoefficients {d : ℕ} (q : Coordinates d → complement d) : Prop := by
  classical
  exact ∀ z : Coordinates d, ∀ k : Frequency d,
    fourierCoeff (q z).val k =
      if ComplementFrequency k then
        ((1/(2*(frequencyLength k^d-1)):ℝ):ℂ)*fourierCoeff (((assembly d z)^2) : Space d) k
      else 0

def SobolevQuadraticReduction (d : ℕ) : Prop :=
  ∃ ψ : ℝ × Coordinates d → complement d, ∃ q : Coordinates d → complement d,
    AnalyticAt ℝ ψ (1,0) ∧ ψ (1,0)=0 ∧ HasFDerivAt (𝕜 := ℝ) ψ 0 (1,0) ∧
    (∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      projectedEquation (greenContinuous d) (x,ψ x)=0) ∧
    (∀ᶠ x in 𝓝 ((1,(0 : Coordinates d)),(0 : complement d)),
      projectedEquation (greenContinuous d) x=0 ↔ ψ x.1=x.2) ∧
    (∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      SmoothOnTorus (reconstruction d (x.2,ψ x)) ∧
      ∀ s : ℝ, InSobolev s (reconstruction d (x.2,ψ x))) ∧
    QuadraticSlavingCoefficients q ∧
    (∀ z : Coordinates d, ∀ s : ℝ, InSobolev s (q z).val) ∧
    (∀ s : ℝ,
      (∀ᶠ z in 𝓝 (0 : Coordinates d), InSobolev s ((ψ (1,z)-q z).val : Space d)) ∧
      ((fun z => sobolevNorm s ((ψ (1,z)-q z).val : Space d))
        =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3))) ∧
    (∀ s : ℝ,
      (∀ᶠ z in 𝓝 (0 : Coordinates d), InSobolev s
        (normalized (reconstruction d (z,ψ (1,z)))-
          (1+assembly d z+(q z : Space d)+(1/2:ℝ) • center d ((assembly d z)^2)) : Space d)) ∧
      ((fun z => sobolevNorm s (normalized (reconstruction d (z,ψ (1,z)))-
          (1+assembly d z+(q z : Space d)+(1/2:ℝ) • center d ((assembly d z)^2)) : Space d))
        =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3)))

end BecknerOnofri.HighDim.LocalReductionStatement
