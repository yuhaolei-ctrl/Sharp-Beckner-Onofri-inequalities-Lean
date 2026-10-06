module

public import BecknerOnofri.LocalElevenCore.RealReducedLocalMaximum
public import BecknerOnofri.LocalElevenCore.FirstShellOrbits
public import BecknerOnofri.OptimizerTranslation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.RealReducedEnergy
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation ReducedEnergyGradient
open ContinuousSymmetry DiagonalScalarBranch ReducedCubicExpansion

theorem energy_norm_eq {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0),physicalReducedEnergy hd x=
      energy hd x.1 (fun i => ‖x.2 i‖) := by
  filter_upwards [potential_translation hd] with x hx
  have h := hx (phaseNormalizer x.2)
  rw [phaseNormalizer_spec] at h
  change (dualFunctional (x.1*spectralThreshold d) (potential hd x)).toReal =
    (dualFunctional (x.1*spectralThreshold d) (potential hd (x.1,fun i => (‖x.2 i‖:ℂ)))).toReal
  rw [h,OptimizerTranslation.continuous_dual_translation]

theorem diagonal_complex_isLocalMax {d : ℕ} (hd : 11≤d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ),IsLocalMax (fun z => physicalReducedEnergy hd (μ,z))
      (realDiagonal d (amplitude hd μ)) := by
  have ht : Tendsto (fun μ => (μ,realDiagonal d (amplitude hd μ)))
      (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Coordinates d))) := by
    have hz := ((realDiagonal d).continuous.tendsto 0).comp (amplitude_tendsto hd)
    simp only [map_zero] at hz
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hz
  filter_upwards [diagonal_isLocalMax hd,ht.eventually (energy_norm_eq hd).eventually_nhds,
    eventually_parameter_interval hd,self_mem_nhdsWithin] with μ hm he hi hμ
  change 1<μ at hμ
  have hp := amplitude_pos hd hμ hi.2
  let N : Coordinates d → Amplitudes d := fun z i => ‖z i‖
  have hcont : Continuous N := continuous_pi (fun i => (continuous_apply i).norm)
  have hbase : N (realDiagonal d (amplitude hd μ))=(fun _ : Fin d => amplitude hd μ) := by
    funext i
    simp only [N,realDiagonal_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  have hN : Tendsto N (𝓝 (realDiagonal d (amplitude hd μ)))
      (𝓝 (fun _ : Fin d => amplitude hd μ)) := by
    simpa only [hbase] using hcont.tendsto (realDiagonal d (amplitude hd μ))
  have hinc : Tendsto (fun z : Coordinates d => (μ,z))
      (𝓝 (realDiagonal d (amplitude hd μ))) (𝓝 (μ,realDiagonal d (amplitude hd μ))) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have h0 := he.self_of_nhds
  have h0' : physicalReducedEnergy hd (μ,realDiagonal d (amplitude hd μ))=
      energy hd μ (fun _ : Fin d => amplitude hd μ) := by
    simpa only [← hbase] using h0
  filter_upwards [hN.eventually hm,hinc.eventually he] with z hz hez
  rw [hez,h0']
  exact hz

#print axioms diagonal_complex_isLocalMax
end BecknerOnofri.HighDim.LocalEleven.RealReducedEnergy
