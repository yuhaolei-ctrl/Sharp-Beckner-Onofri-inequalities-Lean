import BecknerOnofri.LocalQuarticStatementDefinitions

/-! The existence part of the paper's local critical-branch proposition.
All objects below are actual torus potentials and Fourier coefficients. This
assertion deliberately does not assert exhaustiveness, saddle signs, or local maxima. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalReductionStatement

def supportCoefficient (d n : ℕ) : ℝ := -(2*quarticA d+quarticB d*((n:ℝ)-1))

def SupportedStationaryBranch (d : ℕ) (I : Finset (Fin d)) : Prop :=
  ∃ r : ℝ → ℝ, ∃ U : ℝ → ContinuousGibbs.Space d,
    AnalyticAt ℝ r 0 ∧ r 0=0 ∧ HasDerivAt r (supportCoefficient d I.card)⁻¹ 0 ∧
    ((fun δ => r δ-δ/supportCoefficient d I.card) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2)) ∧
    Tendsto U (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0<r δ ∧ SmoothOnTorus (U δ) ∧
      (∀ s : ℝ, InSobolev s (U δ)) ∧ InCriticalSobolev (U δ) ∧ MeanZero (U δ) ∧
      (∀ k : NonzeroFrequency d,
        ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff (U δ) k.val =
          ((1/(1-δ):ℝ):ℂ)*fourierCoeff (normalizedGibbs (U δ)) k.val) ∧
      (∀ j : Fin d, fourierCoeff (U δ) (axisFrequency j)=
        if j∈I then ((Real.sqrt (r δ)):ℂ) else 0) ∧
      (∀ j : Fin d, fourierCoeff (U δ) (axisFrequency j) ≠ 0 ↔ j∈I)

end BecknerOnofri.HighDim.LocalReductionStatement
