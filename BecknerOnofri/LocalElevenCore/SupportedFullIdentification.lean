import BecknerOnofri.LocalElevenCore.SupportedDeltaIdentification
import BecknerOnofri.LocalElevenCore.SubsetUniqueness
import BecknerOnofri.LocalElevenCore.DiagonalProfile

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SupportedFamily
open ContinuousFirstShell ReducedCubicExpansion ReducedEquation

theorem line_univ (d : ℕ) (t : ℝ) :
    SubsetDiagonal.line (Finset.univ : Finset (Fin d)) t=realDiagonal d t := by
  ext i
  simp [SubsetDiagonal.line_apply,realDiagonal_apply]

/-- The family used for all-support classification agrees exactly with the full
Morse--Bott family, rather than merely sharing a leading-order expansion. -/
theorem full_branch_identification {d : ℕ} (hd : 11≤d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ),branch hd Finset.univ (1-1/μ)=
      DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ) := by
  let j : Fin d := ⟨0,by omega⟩
  have hj : j∈(Finset.univ : Finset (Fin d)) := Finset.mem_univ _
  have ha := amplitude_spec hd (show 0<d by omega) (le_refl d)
  have hi := (ha.2.2.2.2 Finset.univ (by simp) j hj).2
  have ht : Tendsto (fun μ => (μ,DiagonalScalarBranch.amplitude hd μ))
      (𝓝[>] (1:ℝ)) (𝓝 (1,0)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds
      (DiagonalScalarBranch.amplitude_tendsto hd)
  filter_upwards [self_mem_nhdsWithin,DiagonalScalarBranch.eventually_parameter_interval hd,
    ht.eventually (SubsetDiagonal.supported_parameter_unique hd Finset.univ j hj),
    (DiagonalScalarBranch.amplitude_tendsto hd).eventually hi] with μ hμ hint huniq hi
  have hp := DiagonalScalarBranch.amplitude_pos hd hμ hint.2
  have hinv := (DiagonalScalarBranch.amplitude_spec hd hint).2
  have hz := (DiagonalScalarBranch.amplitude_stationary hd hμ hint.2).2.2.2.2
  have he : SubsetDiagonal.parameter hd Finset.univ j hj
      (DiagonalScalarBranch.amplitude hd μ)=μ := by
    apply (huniq hp.ne').mp
    simpa only [line_univ,DiagonalScalarBranch.branchPotential,hinv] using hz
  rw [he] at hi
  simp only [branch,Finset.card_univ,Fintype.card_fin,hi,Real.sqrt_sq_eq_abs,
    abs_of_pos hp,line_univ,sub_sub_cancel,one_div_one_div,
    DiagonalScalarBranch.branchPotential,hinv]

#print axioms full_branch_identification
end BecknerOnofri.HighDim.LocalEleven.SupportedFamily
