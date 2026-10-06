module

public import BecknerOnofri.LocalElevenCore.EqualAmplitudeSupport

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry ReducedEquation
open BecknerOnofri.HighDim.ContinuousSymmetry (translation translation_add translation_zero)

/-- No additional small nonzero continuous Euler solutions exist: each is a
translation of one of the supported scalar branches. This uses the actual
complementary graph and the paper's equal-active-amplitude divisibility argument. -/
theorem small_solution_supported {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Space d in 𝓝 (1,0),MeanZero x.2 → full d x.1 x.2=0 → x.2≠0 →
      ∃ I : Finset (Fin d), ∃ j : Fin d, ∃ hj : j∈I, ∃ t : ℝ, ∃ a : Torus d,
        0<t ∧ t=‖fourierCoeff x.2 (axisFrequency j)‖ ∧
        x.1=SubsetDiagonal.parameter hd I j hj t ∧
        x.2=translation a (SubsetDiagonal.branchPotential hd I j hj t) := by
  have ht : Tendsto (fun x : ℝ × Space d => (x.1,coordinates d x.2))
      (𝓝 (1,0)) (𝓝 (1,0)) := by
    have hc : Continuous (fun x : ℝ × Space d => (x.1,coordinates d x.2)) :=
      continuous_fst.prodMk ((coordinates d).continuous.comp continuous_snd)
    simpa only [map_zero] using hc.tendsto (1,0)
  have hμ : Tendsto (Prod.fst : ℝ × Space d → ℝ) (𝓝 (1,0)) (𝓝 1) := continuous_fst.continuousAt
  filter_upwards [small_full_solution_on_graph hd,ht.eventually (reduced_equal_active_fourier hd),
    ht.eventually (reduced_nonnegative_zero_iff hd),ht.eventually (all_supported_parameter_unique hd),
    ht.eventually (potential_translation hd),hμ.eventually (ReducedCubicExpansion.potential_axis hd)]
    with x hgraph hequal hnorm huniq htrans haxis
  intro hm hf hne
  obtain ⟨hu,hr⟩ := hgraph hm hf
  have hz : coordinates d x.2≠0 := by
    intro hz
    rw [hz,haxis] at hu
    exact hne hu
  obtain ⟨I,j,hj,hpos,hline⟩ := equal_squares_supported_line (coordinates d x.2) hz (hequal hr)
  let t : ℝ := ‖coordinates d x.2 j‖
  have hred : reduced hd (x.1,SubsetDiagonal.line I t)=0 := by
    have h := hnorm.mpr hr
    rw [hline] at h
    exact h
  have hparam := huniq I j hj hpos.ne' hred
  have hpot := htrans (phaseNormalizer (coordinates d x.2))
  rw [phaseNormalizer_spec,hline,← hu] at hpot
  have hinv := congrArg (translation (-phaseNormalizer (coordinates d x.2))) hpot
  rw [translation_add,add_neg_cancel,translation_zero] at hinv
  refine ⟨I,j,hj,t,-phaseNormalizer (coordinates d x.2),hpos,?_,hparam.symm,?_⟩
  · simp only [t,coordinates_apply,coefficient_eq_fourierCoeff]
  · rw [SubsetDiagonal.branchPotential,hparam]
    exact hinv.symm

#print axioms small_solution_supported
end BecknerOnofri.HighDim.LocalEleven
