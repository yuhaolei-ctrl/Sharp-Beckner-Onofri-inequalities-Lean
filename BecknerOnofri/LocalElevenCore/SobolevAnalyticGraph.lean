import BecknerOnofri.SobolevAnalyticGraphDefinitions
import BecknerOnofri.WienerGraphIdentification

noncomputable section
namespace BecknerOnofri.HighDim.LocalEleven

theorem sobolev_analytic_complement_graph {d : ℕ} (hd : 11≤d) :
    LocalReductionStatement.SobolevAnalyticComplementGraph d :=
  ⟨GreenLocalBranch.correction hd,GreenLocalBranch.correction_analytic hd,
    GreenLocalBranch.correction_base hd,GreenLocalBranch.correction_derivative_zero hd,
    GreenLocalBranch.correction_axis hd,GreenLocalBranch.correction_solves hd,
    GreenLocalBranch.correction_unique hd,GraphRegularity.potential_regular hd,
    GraphAllSobolevBounds.correction_sobolev_quadratic hd,WienerGraph.exists_analytic_sobolev_lift hd⟩

#print axioms sobolev_analytic_complement_graph
end BecknerOnofri.HighDim.LocalEleven
