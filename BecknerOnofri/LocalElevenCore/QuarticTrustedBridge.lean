import BecknerOnofri.LocalElevenCore.GraphAllSobolevBounds
import BecknerOnofri.LocalQuarticStatementDefinitions
import BecknerOnofri.LocalElevenCore.ReducedEnergyDeltaRemainder
import BecknerOnofri.LocalElevenCore.GraphRegularity

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open ContinuousFirstShell ContinuousComplement

theorem graph_quartic_reduction {d : ℕ} (hd : 11 ≤ d) :
    LocalReductionStatement.GraphQuarticReduction d := by
  refine ⟨GreenLocalBranch.correction hd,GreenLocalBranch.correction_analytic hd,
    GreenLocalBranch.correction_base hd,GreenLocalBranch.correction_derivative_zero hd,
    GreenLocalBranch.correction_solves hd,GreenLocalBranch.correction_unique hd,?_,
    GreenLocalBranch.correction_quadratic hd,
    GraphAllSobolevBounds.correction_sobolev_quadratic hd,?_⟩
  · filter_upwards [GraphCritical.potential_inCriticalSobolev hd,
      GraphRegularity.potential_regular hd] with x hc hr
    exact ⟨hc,hr⟩
  · exact UniformComplementBounds.physicalReducedEnergy_quartic_paper hd

#print axioms graph_quartic_reduction
end BecknerOnofri.HighDim.LocalEleven
