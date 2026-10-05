module

public import BecknerOnofri.SupportedEnergyStatementDefinitions
public import BecknerOnofri.ContinuousSymmetry

@[expose] public section

/-! The local branch classification and energy expansion on one common family.
This statement uses only actual torus potentials, Fourier Euler equations,
translations, and the physical dual functional. Stability is a separate assertion. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalReductionStatement

def SupportedClassification (d : ℕ) : Prop :=
  ∃ r : ℕ → ℝ → ℝ, ∃ U : Finset (Fin d) → ℝ → ContinuousGibbs.Space d,
    (∀ n : ℕ,0<n → n≤d → AnalyticAt ℝ (r n) 0 ∧ r n 0=0 ∧
      HasDerivAt (r n) (supportCoefficient d n)⁻¹ 0 ∧
      ((fun δ => r n δ-δ/supportCoefficient d n) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2))) ∧
    (∀ I : Finset (Fin d),I.Nonempty → SupportedProfile d I (r I.card) (U I) ∧
      ((fun δ => (dualFunctional ((1/(1-δ))*spectralThreshold d) (U I δ)).toReal -
        (-1/(4*branchQuarticCoefficient d I.card))*δ^2)
          =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3))) ∧
    (∀ᶠ x : ℝ × ContinuousGibbs.Space d in 𝓝 (1,0),MeanZero x.2 →
      (∀ k : NonzeroFrequency d,
        ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff x.2 k.val =
          (x.1:ℂ)*fourierCoeff (normalizedGibbs x.2) k.val) → x.2≠0 →
      0<1-1/x.1 ∧ ∃ I : Finset (Fin d),I.Nonempty ∧ ∃ a : Torus d,
        x.2=ContinuousSymmetry.translation a (U I (1-1/x.1)))

end BecknerOnofri.HighDim.LocalReductionStatement
