module

public import BecknerOnofri.LocalElevenCore.SupportedFamilyProfile
public import BecknerOnofri.AnalyticPitchforkMonotonicity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SupportedFamily
open SubsetDiagonal

theorem scalar_branch_identification {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∀ᶠ t in 𝓝 (0:ℝ),0<t → 0<1-1/parameter hd I j hj t ∧
      branch hd I (1-1/parameter hd I j hj t)=branchPotential hd I j hj t := by
  have ha := amplitude_spec hd (Finset.card_pos.mpr ⟨j,hj⟩) (by simpa using Finset.card_le_univ I)
  have hg := AnalyticPitchfork.parameter_gt_one (pitchforkData hd I j hj)
    (coefficient_pos hd I ⟨j,hj⟩)
  filter_upwards [(ha.2.2.2.2 I rfl j hj).2,hg] with t hl hg
  intro ht
  have hp : 1<parameter hd I j hj t := hg ht
  have hδ : 0<1-1/parameter hd I j hj t :=
    sub_pos.mpr ((div_lt_one (by linarith : 0<parameter hd I j hj t)).mpr hp)
  refine ⟨hδ,?_⟩
  have hi : 1/(1-(1-1/parameter hd I j hj t))=parameter hd I j hj t := by
    rw [sub_sub_cancel,one_div_one_div]
  simp only [branch,hl,Real.sqrt_sq_eq_abs,abs_of_pos ht,hi,branchPotential]

#print axioms scalar_branch_identification
end BecknerOnofri.HighDim.LocalEleven.SupportedFamily
