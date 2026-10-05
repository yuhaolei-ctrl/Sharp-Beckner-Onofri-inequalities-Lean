module

public import BecknerOnofri.DiagonalAmplitude

@[expose] public section

/-! The actual diagonal stationary profile in the trusted physical beta and
translation notation, with a uniform C-norm remainder estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.DiagonalScalarBranch
open ContinuousGibbs ContinuousFirstShell ReducedCubicExpansion ContinuousSymmetry

theorem assembly_realDiagonal_apply (d : ℕ) (t : ℝ) (x : Torus d) :
    assembly d (realDiagonal d t) x = 2*t*firstShellProfile 0 x := by
  rw [assembly_apply]
  simp only [ContinuousMap.sum_apply,synthesis_apply,realDiagonal_apply,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,mFourier_axisFrequency,
    firstShellProfile,Pi.zero_apply,sub_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def physicalPotential {d : ℕ} (hd : 12 ≤ d) (β : ℝ) : Space d :=
  branchPotential hd (amplitude hd (β/spectralThreshold d))

theorem normalized_parameter_tendsto {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (fun β : ℝ => β/spectralThreshold d) (𝓝[>] (spectralThreshold d)) (𝓝[>] (1:ℝ)) := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos (by omega)
  have hc : ContinuousAt (fun β : ℝ => β/spectralThreshold d) (spectralThreshold d) :=
    continuousAt_id.div_const _
  have ht : Tendsto (fun β : ℝ => β/spectralThreshold d) (𝓝[>] (spectralThreshold d)) (𝓝 1) := by
    simpa only [div_self hσ.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht
  filter_upwards [self_mem_nhdsWithin] with β hβ
  change 1 < β/spectralThreshold d
  exact (one_lt_div hσ).mpr hβ

theorem physical_onset_eq {d : ℕ} (hd : 12 ≤ d) (β : ℝ) :
    onset (β/spectralThreshold d) = onsetDelta d β := by
  have hσ : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  unfold onset onsetDelta
  rw [one_div_div]

def profileRemainder {d : ℕ} (hd : 12 ≤ d) (β : ℝ) (a : Torus d) : Space d :=
  translation a (physicalPotential hd β - assembly d (realDiagonal d (Real.sqrt (onsetDelta d β/kappa d))))

theorem profileRemainder_apply {d : ℕ} (hd : 12 ≤ d) (β : ℝ) (a x : Torus d) :
    profileRemainder hd β a x = branchRemainder β (physicalPotential hd β) a x := by
  simp only [profileRemainder,translation_apply,ContinuousMap.sub_apply,assembly_realDiagonal_apply,
    branchRemainder,translate,firstShellProfile,Pi.sub_apply,Pi.zero_apply,sub_zero]

theorem profileRemainder_norm {d : ℕ} (hd : 12 ≤ d) (β : ℝ) (a : Torus d) :
    ‖profileRemainder hd β a‖ =
      ‖physicalPotential hd β - assembly d (realDiagonal d (Real.sqrt (onsetDelta d β/kappa d)))‖ :=
  (translation a).norm_map _

theorem physical_profile_bound {d : ℕ} (hd : 12 ≤ d) :
    (fun β => physicalPotential hd β - assembly d (realDiagonal d (Real.sqrt (onsetDelta d β/kappa d))))
      =O[𝓝[>] (spectralThreshold d)] (onsetDelta d) := by
  apply ((amplitude_potential_profile hd).comp_tendsto (normalized_parameter_tendsto hd)).congr
  · intro β
    change branchPotential hd (amplitude hd (β/spectralThreshold d)) -
      assembly d (realDiagonal d (Real.sqrt (onset (β/spectralThreshold d)/kappa d))) = _
    rw [physical_onset_eq hd]
    rfl
  · intro β
    exact physical_onset_eq hd β

/-- One error constant works for all torus translations in the trusted remainder. -/
theorem physical_profile_uniform {d : ℕ} (hd : 12 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      ∀ a : Torus d, ‖profileRemainder hd β a‖ ≤ C*onsetDelta d β := by
  obtain ⟨C,hC⟩ := (physical_profile_bound hd).exists_pos
  refine ⟨C,hC.1,?_⟩
  filter_upwards [hC.2.bound,(normalized_parameter_tendsto hd).eventually self_mem_nhdsWithin]
    with β hb hβ
  have hp : 0 < onsetDelta d β := by
    rw [← physical_onset_eq hd]
    exact onset_pos hβ
  intro a
  rw [profileRemainder_norm]
  simpa only [Real.norm_eq_abs,abs_of_pos hp] using hb

#print axioms physical_profile_uniform
#print axioms profileRemainder_apply
end BecknerOnofri.HighDim.DiagonalScalarBranch
