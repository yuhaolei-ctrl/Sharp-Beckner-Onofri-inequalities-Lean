module

public import BecknerOnofri.LocalElevenCore.SupportedFamilyDefinitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SupportedFamily
open SubsetDiagonal LocalReductionStatement ContinuousGibbs ContinuousFirstShell

theorem branch_profile {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (hI : I.Nonempty) :
    SupportedProfile d I (amplitude hd I.card) (branch hd I) ∧
    ((fun δ => (dualFunctional ((1/(1-δ))*spectralThreshold d) (branch hd I δ)).toReal -
      (-1/(4*branchQuarticCoefficient d I.card))*δ^2)
        =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3)) := by
  obtain ⟨j,hj⟩ := hI
  obtain ⟨hr,hr0,hrd,he,hparams⟩ := amplitude_spec hd (Finset.card_pos.mpr ⟨j,hj⟩)
    (by simpa using Finset.card_le_univ I)
  have hp := (hparams I rfl j hj).1
  have ht : Tendsto (fun δ => Real.sqrt (amplitude hd I.card δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hr.continuousAt.sqrt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa only [hr0,Real.sqrt_zero] using h
  have heq : ∀ᶠ δ in 𝓝[>] (0:ℝ),branch hd I δ=
      branchPotential hd I j hj (Real.sqrt (amplitude hd I.card δ)) := by
    filter_upwards [hp] with δ hp
    simp only [branch,branchPotential,hp.2]
  have hb0 : branchPotential hd I j hj 0=0 := by
    simp [branchPotential,parameter,AnalyticPitchfork.parameter_base,
      ReducedEquation.potential,GreenLocalBranch.correction_base]
  have hu : Tendsto (branch hd I) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply Tendsto.congr' (heq.mono fun _ h => h.symm)
    have h := (branchPotential_analytic hd I j hj).continuousAt.tendsto.comp ht
    simpa only [hb0,Function.comp_def] using h
  refine ⟨⟨hu,?_⟩,?_⟩
  · filter_upwards [hp,heq,ht.eventually (branchPotential_properties hd I j hj)]
      with δ hp heq hb
    rw [← heq] at hb
    have hf : ReducedEquation.full d (1/(1-δ)) (branch hd I δ)=0 := by
      simpa only [← hp.2] using hb.2.2.2
    have hs := (ReducedEquation.full_zero_iff_stationary (by omega) _ _).mp hf
    have hcoeff (k : Fin d) : fourierCoeff (branch hd I δ) (axisFrequency k)=
        if k∈I then ((Real.sqrt (amplitude hd I.card δ)):ℂ) else 0 := by
      rw [heq,← coefficient_eq_fourierCoeff]
      simpa only [coordinates,line_apply,ContinuousLinearMap.pi_apply] using
        congrFun (branchPotential_coordinates hd I j hj (Real.sqrt (amplitude hd I.card δ))) k
    refine ⟨hp.1,hb.1,hb.2.1,hb.2.2.1,hs.1,hs.2,hcoeff,?_⟩
    intro k
    rw [hcoeff]
    have hn : (Real.sqrt (amplitude hd I.card δ):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp.1).ne'
    by_cases hk : k∈I <;> simp [hk,hn]
  · exact supported_energy_expansion hd I ⟨j,hj⟩ hr hr0 he (hp.mono fun _ h => h.1)

#print axioms branch_profile
end BecknerOnofri.HighDim.LocalEleven.SupportedFamily
