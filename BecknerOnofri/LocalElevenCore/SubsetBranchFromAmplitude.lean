import BecknerOnofri.SupportedEnergyStatementDefinitions
import BecknerOnofri.LocalElevenCore.SubsetPositiveBranch
import BecknerOnofri.LocalElevenCore.SubsetEnergyExpansion

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
open ContinuousGibbs ContinuousFirstShell LocalReductionStatement

theorem supported_branch_of_parameter {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) {r : ℝ → ℝ} (hr : AnalyticAt ℝ r 0) (hr0 : r 0=0)
    (he : (fun δ => r δ-δ/coefficient I) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2))
    (hp : ∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ ∧ parameter hd I j hj (Real.sqrt (r δ))=1/(1-δ)) :
    ∃ U : ℝ → Space d, SupportedProfile d I r U ∧
      ((fun δ => (dualFunctional ((1/(1-δ))*spectralThreshold d) (U δ)).toReal -
        (-1/(4*branchQuarticCoefficient d I.card))*δ^2)
          =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3)) := by
  let U : ℝ → Space d := fun δ => branchPotential hd I j hj (Real.sqrt (r δ))
  have ht : Tendsto (fun δ => Real.sqrt (r δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun δ => Real.sqrt (r δ)) 0 := hr.continuousAt.sqrt
    simpa only [hr0,Real.sqrt_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hb0 : branchPotential hd I j hj 0=0 := by
    simp [branchPotential,parameter,AnalyticPitchfork.parameter_base,
      ReducedEquation.potential,GreenLocalBranch.correction_base]
  have hu : Tendsto U (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := (branchPotential_analytic hd I j hj).continuousAt.tendsto.comp ht
    simpa only [hb0,Function.comp_def,U] using h
  refine ⟨U,⟨hu,?_⟩,?_⟩
  · filter_upwards [hp,ht.eventually (branchPotential_properties hd I j hj)] with δ hp hb
    have hf : ReducedEquation.full d (1/(1-δ)) (U δ)=0 := by
      simpa only [U,← hp.2] using hb.2.2.2
    have hs := (ReducedEquation.full_zero_iff_stationary (by omega) _ _).mp hf
    have hcoeff (k : Fin d) : fourierCoeff (U δ) (axisFrequency k)=
        if k∈I then ((Real.sqrt (r δ)):ℂ) else 0 := by
      rw [← coefficient_eq_fourierCoeff]
      simpa only [coordinates,line_apply,U,ContinuousLinearMap.pi_apply] using
        congrFun (branchPotential_coordinates hd I j hj (Real.sqrt (r δ))) k
    refine ⟨hp.1,hb.1,hb.2.1,hb.2.2.1,hs.1,hs.2,hcoeff,?_⟩
    intro k
    rw [hcoeff]
    have hn : (Real.sqrt (r δ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp.1).ne'
    by_cases hk : k∈I <;> simp [hk,hn]
  · have h := supported_energy_expansion hd I ⟨j,hj⟩ hr hr0 he (hp.mono fun _ h => h.1)
    apply h.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hp] with δ hp
    change (dualFunctional _ (ReducedEquation.potential hd _)).toReal-_ =
      (dualFunctional _ (branchPotential hd I j hj (Real.sqrt (r δ)))).toReal-_
    rw [branchPotential,hp.2]

#print axioms supported_branch_of_parameter
end BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
