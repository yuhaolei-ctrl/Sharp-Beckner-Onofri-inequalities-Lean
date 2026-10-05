import BecknerOnofri.SobolevLocalMaximum
import BecknerOnofri.LocalElevenCore.ContinuousFullLocalMaximum
import BecknerOnofri.LocalElevenCore.DiagonalProfile

noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open ContinuousGibbs ReducedEquation ReducedCubicExpansion DiagonalScalarBranch

theorem physical_sobolev_local_maximum {d : ℕ} (hd : 11≤d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d),∀ s : ℝ,(d:ℝ)/2<s →
      ∃ r : ℝ,0<r ∧ ∀ v : Torus d → ℝ,
        InSobolev s v → InCriticalSobolev v → MeanZero v →
        InSobolev s (fun x => v x-physicalPotential hd β x) →
        sobolevNorm s (fun x => v x-physicalPotential hd β x)<r →
        dualFunctional β v≤dualFunctional β (physicalPotential hd β) := by
  have hσ : spectralThreshold d≠0 :=
    (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  filter_upwards [(normalized_parameter_tendsto hd).eventually (continuous_full_local_maximum hd),
    (normalized_parameter_tendsto hd).eventually (amplitude_eventually_inverse hd)] with β hmax hinv
  have he : physicalPotential hd β =
      potential hd (β/spectralThreshold d,realDiagonal d (amplitude hd (β/spectralThreshold d))) := by
    unfold physicalPotential branchPotential
    rw [hinv]
  rw [div_mul_cancel₀ β hσ,← he] at hmax
  exact sobolev_localMaximum_of_continuous (by omega) β (physicalPotential hd β) hmax

#print axioms physical_sobolev_local_maximum
end BecknerOnofri.HighDim.LocalEleven
