module

public import BecknerOnofri.LocalFullModeBranchDefinitions
public import BecknerOnofri.LocalElevenCore.StationaryTrustedBridge
public import BecknerOnofri.LocalElevenCore.SobolevFullLocalMaximum

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open DiagonalScalarBranch LocalReductionStatement

theorem fullmode_local_branch {d : ℕ} (hd : 11≤d) : FullModeLocalBranch d := by
  have hAll : ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      FullModeMorseBott β (physicalPotential hd β) := by
    filter_upwards [PhysicalBranchProperties.physical_branch_properties hd,
      FullBranchHessian.physical_hessian_nonpos_kernel hd,
      PhysicalNormalCoercivity.physical_normalCoercivity hd,
      physical_sobolev_local_maximum hd] with β hb hh hn hmax
    exact ⟨hb.smooth,fun s _ => hb.sobolev s,hb.criticalSobolev,hb.meanZero,hb.stationary,
      hb.fullModes,hb.tangentIndependent,
      fun h hc hm => (hh h hc hm).1,fun h hc hm => (hh h hc hm).2,hn,hmax⟩
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhdsWithin_iff.mp hAll
  refine ⟨r,hr,(fun β => (physicalPotential hd β : Torus d → ℝ)),?_,?_⟩
  · intro β hβ hupper
    apply hBall
    refine ⟨?_,hβ⟩
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hβ)]
    linarith
  · intro s
    exact physical_profile_sobolev_interval hd s hr

#print axioms fullmode_local_branch
end BecknerOnofri.HighDim.LocalEleven
