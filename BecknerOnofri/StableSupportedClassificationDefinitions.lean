import BecknerOnofri.SupportedEnergyStatementDefinitions
import BecknerOnofri.ContinuousSymmetry
import BecknerOnofri.BranchDefinitions

/-! The local branch classification and energy expansion on one common family.
The common witnesses also satisfy genuine Morse--Bott local maximality,
proper-support saddle behavior, and strict ordering of the actual physical energies. -/
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.LocalReductionStatement

def StableSupportedClassification (d : ℕ) : Prop :=
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
        x.2=ContinuousSymmetry.translation a (U I (1-1/x.1))) ∧
    (∀ s : ℝ,(d:ℝ)/2<s → ∃ ε : ℝ,0<ε ∧ ∀ (μ : ℝ) (u : Torus d → ℝ),
      InSobolev s u → MeanZero u → |μ-1|<ε → sobolevNorm s u<ε →
      (∀ k : NonzeroFrequency d,((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff u k.val =
        (μ:ℂ)*fourierCoeff (normalizedGibbs u) k.val) →
      ¬u =ᵐ[torusMeasure d] (fun _ => 0) →
      0<1-1/μ ∧ ∃ I : Finset (Fin d),I.Nonempty ∧ ∃ a : Torus d,
        u =ᵐ[torusMeasure d] (ContinuousSymmetry.translation a (U I (1-1/μ)) : Torus d → ℝ)) ∧
    (∀ᶠ δ in 𝓝[>] (0:ℝ),
      FullModeMorseBott ((1/(1-δ))*spectralThreshold d) (U Finset.univ δ) ∧
      (∀ I : Finset (Fin d),I.Nonempty → I.card<d →
        ∃ v q : ContinuousGibbs.Space d,
          InCriticalSobolev v ∧ MeanZero v ∧ InCriticalSobolev q ∧ MeanZero q ∧
          0<secondVariation ((1/(1-δ))*spectralThreshold d) (U I δ) v ∧
          secondVariation ((1/(1-δ))*spectralThreshold d) (U I δ) q<0) ∧
      (∀ I J : Finset (Fin d),I.Nonempty → I.card<J.card →
        dualFunctional ((1/(1-δ))*spectralThreshold d) (U I δ)<
          dualFunctional ((1/(1-δ))*spectralThreshold d) (U J δ)))

end BecknerOnofri.HighDim.LocalReductionStatement
