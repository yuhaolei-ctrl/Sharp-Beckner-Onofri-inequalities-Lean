module

public import BecknerOnofri.ContinuousComplement
public import BecknerOnofri.GreenContinuous

@[expose] public section

/-! Explicit interface for the continuous-space local quartic reduction.
The graph is existentially quantified; its definition contains no selected
implicit-function witness. This is not the complete Sobolev-space branch theorem. -/
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalReductionStatement
open ContinuousGibbs ContinuousFirstShell ContinuousComplement

def mass {d : ℕ} (z : Coordinates d) : ℝ := ∑ i, ‖z i‖^2

def quartic {d : ℕ} (z : Coordinates d) : ℝ :=
  quarticA d * (∑ i, ‖z i‖^4) +
    quarticB d * (∑ i : Fin d, ∑ j ∈ Finset.univ.filter (fun j : Fin d => i<j),
      ‖z i‖^2 * ‖z j‖^2)

def GraphQuarticReduction (d : ℕ) : Prop :=
  ∃ ψ : ℝ × Coordinates d → complement d,
    AnalyticAt ℝ ψ (1,0) ∧ ψ (1,0) = 0 ∧
    HasFDerivAt (𝕜 := ℝ) ψ 0 (1,0) ∧
    (∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      projectedEquation (greenContinuous d) (x,ψ x) = 0) ∧
    (∀ᶠ x in 𝓝 ((1,(0 : Coordinates d)),(0 : complement d)),
      projectedEquation (greenContinuous d) x = 0 ↔ ψ x.1 = x.2) ∧
    (∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      InCriticalSobolev (reconstruction d (x.2,ψ x)) ∧
      SmoothOnTorus (reconstruction d (x.2,ψ x)) ∧
      ∀ s : ℝ, InSobolev s (reconstruction d (x.2,ψ x))) ∧
    (ψ =O[𝓝 (1,(0 : Coordinates d))]
      (fun x => ‖x.2‖^2+|x.1-1| * ‖x.2‖)) ∧
    (∀ s : ℝ, (fun x => sobolevNorm s (ψ x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2)) ∧
    ((fun x : ℝ × Coordinates d =>
      (dualFunctional (x.1*spectralThreshold d) (reconstruction d (x.2,ψ x))).toReal -
        (1-1/x.1)*mass x.2 - quartic x.2)
      =O[𝓝 (1,0)] (fun x => mass x.2^3+|1-1/x.1| * mass x.2^2))

end BecknerOnofri.HighDim.LocalReductionStatement
