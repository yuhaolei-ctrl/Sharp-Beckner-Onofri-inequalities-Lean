module

public import BecknerOnofri.LocalElevenCore.SubsetStationaryBranch

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
open ContinuousGibbs ContinuousFirstShell

/-- An actual Euler branch for every nonempty coordinate support. The amplitude is
analytic in delta, positive on the supercritical side, with the exact paper coefficient. -/
theorem exists_supported_branch {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (hI : I.Nonempty) :
    ∃ r : ℝ → ℝ, ∃ U : ℝ → Space d,
      AnalyticAt ℝ r 0 ∧ r 0=0 ∧ HasDerivAt r (coefficient I)⁻¹ 0 ∧
      ((fun δ => r δ-δ/coefficient I) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2)) ∧
      Tendsto U (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ᶠ δ in 𝓝[>] (0:ℝ), 0<r δ ∧ SmoothOnTorus (U δ) ∧
        (∀ s : ℝ, InSobolev s (U δ)) ∧ InCriticalSobolev (U δ) ∧
        MeanZero (U δ) ∧
        (∀ k : NonzeroFrequency d,
          ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff (U δ) k.val =
            ((1/(1-δ):ℝ):ℂ)*fourierCoeff (normalizedGibbs (U δ)) k.val) ∧
        (∀ j : Fin d, fourierCoeff (U δ) (axisFrequency j)=
          if j∈I then ((Real.sqrt (r δ)):ℂ) else 0) ∧
        U δ=ReducedEquation.potential hd (1/(1-δ),line I (Real.sqrt (r δ))) := by
  obtain ⟨j,hj⟩ := hI
  let D := pitchforkData hd I j hj
  obtain ⟨r,hr,hr0,hrd,hre,hpos⟩ := AnalyticPitchfork.exists_positive_squared_amplitude D
    (coefficient_pos hd I ⟨j,hj⟩)
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
  refine ⟨r,U,hr,hr0,hrd,hre,hu,?_⟩
  filter_upwards [hpos,ht.eventually (branchPotential_properties hd I j hj)] with δ hp hb
  have hf : ReducedEquation.full d (1/(1-δ)) (U δ)=0 := by
    simpa only [U,parameter,← hp.2] using hb.2.2.2
  have hs := (ReducedEquation.full_zero_iff_stationary (by omega) _ _).mp hf
  refine ⟨hp.1,hb.1,hb.2.1,hb.2.2.1,hs.1,hs.2,?_,?_⟩
  · intro k
    rw [← coefficient_eq_fourierCoeff]
    simpa only [coordinates,line_apply,U,ContinuousLinearMap.pi_apply] using
      congrFun (branchPotential_coordinates hd I j hj (Real.sqrt (r δ))) k
  · change ReducedEquation.potential hd (parameter hd I j hj (Real.sqrt (r δ)),_)=_
    rw [show parameter hd I j hj (Real.sqrt (r δ))=1/(1-δ) from hp.2]

#print axioms exists_supported_branch
end BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
