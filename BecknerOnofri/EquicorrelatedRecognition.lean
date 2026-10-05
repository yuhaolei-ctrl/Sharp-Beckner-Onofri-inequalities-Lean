import BecknerOnofri.EquicorrelatedSpectrum

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.EquicorrelatedSpectrum
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma eq_operator_of_entries (M : Module.End ℝ (ι → ℝ)) (a b : ℝ)
    (he : ∀ i j,M (Pi.single j 1) i=if i=j then a+b else b) : M=operator a b := by
  apply LinearMap.pi_ext
  intro j c
  have hc : Pi.single j c=c • (Pi.single j (1:ℝ) : ι → ℝ) := by
    rw [← Pi.single_smul]
    simp
  rw [hc,map_smul,map_smul]
  congr 1
  funext i
  rw [he,operator_apply]
  by_cases hij : i=j <;> simp [Pi.single_apply,hij]

lemma diagonal_eq_of_row_differences (M : Module.End ℝ (ι → ℝ))
    (hs : ∀ i j,M (Pi.single i 1) j=M (Pi.single j 1) i)
    (hr : ∀ i j,∃ c : ℝ,∀ x : ι → ℝ,M x i-M x j=c*(x i-x j)) (i j : ι) :
    M (Pi.single i 1) i=M (Pi.single j 1) j := by
  by_cases hij : i=j
  · subst j; rfl
  obtain ⟨c,hc⟩ := hr i j
  have hi := hc (Pi.single i 1)
  have hj := hc (Pi.single j 1)
  simp only [Pi.single_apply,if_pos rfl,if_neg hij,if_neg (Ne.symm hij),ite_true] at hi hj
  have hsij := hs i j
  linarith

lemma off_column_eq_of_row_differences (M : Module.End ℝ (ι → ℝ))
    (hr : ∀ i j,∃ c : ℝ,∀ x : ι → ℝ,M x i-M x j=c*(x i-x j))
    (i j k : ι) (hki : k≠i) (hkj : k≠j) : M (Pi.single k 1) i=M (Pi.single k 1) j := by
  obtain ⟨c,hc⟩ := hr i j
  have h := hc (Pi.single k 1)
  simp only [Pi.single_apply,if_neg hki,if_neg hki.symm,if_neg hkj,if_neg hkj.symm,
    sub_self,mul_zero] at h
  exact sub_eq_zero.mp h

/-- Symmetry and the exact pairwise row-difference identities identify the
entire matrix. In the application both assumptions come from the actual
energy and analytic squared-amplitude divisibility. -/
theorem exists_operator_of_row_differences (M : Module.End ℝ (ι → ℝ))
    (hs : ∀ i j,M (Pi.single i 1) j=M (Pi.single j 1) i)
    (hr : ∀ i j,∃ c : ℝ,∀ x : ι → ℝ,M x i-M x j=c*(x i-x j)) :
    ∃ a b : ℝ,M=operator a b := by
  cases subsingleton_or_nontrivial ι with
  | inl hsub =>
      letI := hsub
      let p : ι := Classical.arbitrary ι
      refine ⟨M (Pi.single p 1) p,0,eq_operator_of_entries M _ _ ?_⟩
      intro i j
      have hi : i=p := Subsingleton.elim _ _
      have hj : j=p := Subsingleton.elim _ _
      simp only [hi,hj,if_pos rfl,add_zero,ite_true]
  | inr hnon =>
      letI := hnon
      obtain ⟨p,q,hpq⟩ := exists_pair_ne ι
      let b := M (Pi.single q 1) p
      let a := M (Pi.single p 1) p-b
      have hoff (j : ι) (hjp : j≠p) : M (Pi.single j 1) p=b := by
        have h := off_column_eq_of_row_differences M hr j q p hjp.symm hpq
        rw [← hs j p,← hs q p] at h
        exact h
      refine ⟨a,b,eq_operator_of_entries M a b ?_⟩
      intro i j
      by_cases hij : i=j
      · subst j
        rw [if_pos rfl,diagonal_eq_of_row_differences M hs hr i p]
        dsimp only [a]
        ring
      · rw [if_neg hij]
        by_cases hjp : j=p
        · subst j
          rw [← hs i p]
          exact hoff i hij
        · exact (off_column_eq_of_row_differences M hr i p j (Ne.symm hij) hjp).trans (hoff j hjp)

#print axioms exists_operator_of_row_differences
end BecknerOnofri.EquicorrelatedSpectrum
