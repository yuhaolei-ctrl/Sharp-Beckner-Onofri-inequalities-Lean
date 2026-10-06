module

public import BecknerOnofri.LocalElevenCore.SubsetStationaryBranch
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
open ContinuousFirstShell ContinuousSymmetry ReducedEquation

theorem line_injective {d : ℕ} (I : Finset (Fin d)) (hI : I.Nonempty) :
    Function.Injective (line I) := by
  obtain ⟨j,hj⟩ := hI
  intro s t h
  have hj' := congrArg (fun z : Coordinates d => (z j).re) h
  simpa only [line_apply,if_pos hj,Complex.ofReal_re] using hj'

/-- Uniqueness on a fixed equal-amplitude support, for the actual full equation. -/
theorem supported_parameter_unique {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0), x.2≠0 →
      (full d x.1 (potential hd (x.1,line I x.2))=0 ↔ parameter hd I j hj x.2=x.1) := by
  let D := pitchforkData hd I j hj
  filter_upwards [(embedding_tendsto I).eventually (graph_full_iff_reduced hd),
    reduced_line hd I j hj,AnalyticPitchfork.residual_eq_mul_quotient D,
    AnalyticPitchfork.parameter_unique D] with x hf hl hq hu
  intro ht
  have hlin : line I (residual hd I j x)=0 ↔ residual hd I j x=0 := by
    rw [← (line I).map_zero]
    exact (line_injective I ⟨j,hj⟩).eq_iff
  change reduced hd (x.1,line I x.2)=line I (residual hd I j x) at hl
  simp only [embedding_apply] at hf
  rw [hf,hl,hlin]
  change D.residual x=0 ↔ AnalyticPitchfork.parameter D x.2=x.1
  rw [hq,mul_eq_zero,or_iff_right ht,hu]

theorem permutation_between_supports {d : ℕ} (I J : Finset (Fin d))
    (h : I.card=J.card) : ∃ p : Equiv.Perm (Fin d), ∀ i, p i∈I ↔ i∈J := by
  let e : {i // i∈J} ≃ {i // i∈I} := Fintype.equivOfCardEq (by simpa using h.symm)
  refine ⟨e.extendSubtype,?_⟩
  intro i
  by_cases hi : i∈J
  · exact iff_of_true (e.extendSubtype_mem i hi) hi
  · exact iff_of_false (e.extendSubtype_not_mem i hi) hi

theorem permutation_line {d : ℕ} {I J : Finset (Fin d)} (p : Equiv.Perm (Fin d))
    (hp : ∀ i,p i∈I ↔ i∈J) (t : ℝ) : permuteCoordinates p (line I t)=line J t := by
  ext i
  simp only [permuteCoordinates,line_apply,hp]

/-- The analytic parameter germ depends only on the cardinality of the support. -/
theorem parameter_eq_of_card_eq {d : ℕ} (hd : 11≤d) (I J : Finset (Fin d))
    (i j : Fin d) (hi : i∈I) (hj : j∈J) (hcard : I.card=J.card) :
    ∀ᶠ t in 𝓝 (0:ℝ), parameter hd I i hi t=parameter hd J j hj t := by
  obtain ⟨p,hp⟩ := permutation_between_supports I J hcard
  have ht := branch_coordinates_tendsto hd I i hi
  have ht' := AnalyticPitchfork.parameter_pair_tendsto (pitchforkData hd I i hi)
  filter_upwards [ht.eventually (reduced_permutation hd),parameter_reduced_zero hd I i hi,
    ht'.eventually (supported_parameter_unique hd J j hj),
    ht'.eventually ((embedding_tendsto J).eventually (graph_full_iff_reduced hd))]
    with t hperm hzero huniq hfull
  by_cases ht0 : t=0
  · subst t
    simp [parameter,AnalyticPitchfork.parameter_base]
  have hz : reduced hd (parameter hd I i hi t,line J t)=0 := by
    have h := hperm p
    rw [permutation_line p hp,hzero] at h
    exact h.trans (by ext k; rfl)
  exact ((huniq ht0).mp (hfull.mpr hz)).symm

#print axioms supported_parameter_unique
#print axioms parameter_eq_of_card_eq
end BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
