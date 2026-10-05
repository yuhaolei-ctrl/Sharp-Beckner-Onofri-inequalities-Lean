import BecknerOnofri.SobolevQuadraticReductionDefinitions
import BecknerOnofri.LocalElevenCore.SobolevDensitySlaving

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open ContinuousGibbs ContinuousFirstShell ContinuousComplement QuadraticSlaving

lemma quadratic_slaving_coefficients {d : ℕ} (hd : 11≤d) :
    LocalReductionStatement.QuadraticSlavingCoefficients (quadraticCorrection hd) := by
  classical
  intro z k
  rw [← coefficient_eq_fourierCoeff,← coefficient_eq_fourierCoeff]
  by_cases hk : ComplementFrequency k
  · rw [if_pos hk,QuadraticModes.quadraticCorrection_coefficient hd z hk,
      BecknerOnofri.HighDim.QuadraticModes.quadraticSource_coefficient,if_pos hk]
    rfl
  · rw [if_neg hk]
    exact (mem_complement_fourier_iff _).mp (quadraticCorrection hd z).property k hk

theorem sobolev_quadratic_reduction {d : ℕ} (hd : 11≤d) :
    LocalReductionStatement.SobolevQuadraticReduction d := by
  refine ⟨GreenLocalBranch.correction hd,quadraticCorrection hd,
    GreenLocalBranch.correction_analytic hd,GreenLocalBranch.correction_base hd,
    GreenLocalBranch.correction_derivative_zero hd,GreenLocalBranch.correction_solves hd,
    GreenLocalBranch.correction_unique hd,GraphRegularity.potential_regular hd,
    quadratic_slaving_coefficients hd,?_,?_,?_⟩
  · intro z s
    exact quadraticCorrection_inSobolev hd s z
  · intro s
    exact ⟨slaving_error_inSobolev hd s,correction_quadratic_expansion_all_sobolev hd s⟩
  · intro s
    have hQ (z : Coordinates d) : quadraticTerm (assembly d z)=
        (1/2:ℝ) • center d ((assembly d z)^2) := quadraticTerm_of_mean_zero (mean_assembly z)
    constructor
    · simpa only [hQ,slicePotential,ReducedEquation.potential] using density_error_inSobolev hd s
    · simpa only [hQ,slicePotential,ReducedEquation.potential] using normalized_density_quadratic_expansion_all_sobolev hd s

#print axioms sobolev_quadratic_reduction
end BecknerOnofri.HighDim.LocalEleven
