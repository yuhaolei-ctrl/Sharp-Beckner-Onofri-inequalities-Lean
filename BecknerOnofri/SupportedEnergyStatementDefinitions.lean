module

public import BecknerOnofri.SupportedBranchStatementDefinitions
public import BecknerOnofri.QuarticBranches

@[expose] public section

/-! The supported branch family and its actual functional values. These are the
existence and value assertions, without the still separate exhaustiveness and stability assertions. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalReductionStatement

def SupportedProfile (d : ℕ) (I : Finset (Fin d)) (r : ℝ → ℝ)
    (U : ℝ → ContinuousGibbs.Space d) : Prop :=
  Tendsto U (𝓝[>] (0:ℝ)) (𝓝 0) ∧
  ∀ᶠ δ in 𝓝[>] (0:ℝ), 0<r δ ∧ SmoothOnTorus (U δ) ∧
    (∀ s : ℝ, InSobolev s (U δ)) ∧ InCriticalSobolev (U δ) ∧ MeanZero (U δ) ∧
    (∀ k : NonzeroFrequency d,
      ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff (U δ) k.val =
        ((1/(1-δ):ℝ):ℂ)*fourierCoeff (normalizedGibbs (U δ)) k.val) ∧
    (∀ j : Fin d, fourierCoeff (U δ) (axisFrequency j)=
      if j∈I then ((Real.sqrt (r δ)):ℂ) else 0) ∧
    (∀ j : Fin d, fourierCoeff (U δ) (axisFrequency j) ≠ 0 ↔ j∈I)

def SupportedEnergyFamily (d n : ℕ) : Prop :=
  ∃ r : ℝ → ℝ, AnalyticAt ℝ r 0 ∧ r 0=0 ∧
    HasDerivAt r (supportCoefficient d n)⁻¹ 0 ∧
    ((fun δ => r δ-δ/supportCoefficient d n) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2)) ∧
    ∀ I : Finset (Fin d), I.card=n → ∃ U : ℝ → ContinuousGibbs.Space d,
      SupportedProfile d I r U ∧
      ((fun δ => (dualFunctional ((1/(1-δ))*spectralThreshold d) (U δ)).toReal -
        (-1/(4*branchQuarticCoefficient d n))*δ^2)
          =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3))

end BecknerOnofri.HighDim.LocalReductionStatement
