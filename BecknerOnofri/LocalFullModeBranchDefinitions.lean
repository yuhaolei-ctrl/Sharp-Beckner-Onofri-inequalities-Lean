module

public import BecknerOnofri.BranchDefinitions

@[expose] public section

/-! Full local Morse--Bott branch from the local critical-branch proposition.
The assertion applies at d=11 as well as d≥12; it contains no global-minimality claim. -/
noncomputable section
namespace BecknerOnofri.HighDim.LocalReductionStatement

def FullModeLocalBranch (d : ℕ) : Prop :=
  ∃ ε : ℝ,0<ε ∧ ∃ U : ℝ → Torus d → ℝ,
    (∀ β : ℝ,spectralThreshold d<β → β<spectralThreshold d+ε →
      FullModeMorseBott β (U β)) ∧
    (∀ s : ℝ,∃ η C : ℝ,0<η ∧ η≤ε ∧ 0≤C ∧
      ∀ β : ℝ,spectralThreshold d<β → β<spectralThreshold d+η →
        ∀ a : Torus d,InSobolev s (branchRemainder β (U β) a) ∧
          sobolevNorm s (branchRemainder β (U β) a)≤C*onsetDelta d β)

end BecknerOnofri.HighDim.LocalReductionStatement
