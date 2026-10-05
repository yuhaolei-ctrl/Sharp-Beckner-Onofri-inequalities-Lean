module

public import Legacy.BecknerOnofri.AngularMixedTerms

@[expose] public section

/-! Actual list-count combinatorics for mixed angular derivative indices. -/
noncomputable section
open Classical
open scoped BigOperators
namespace Legacy.BecknerOnofri.AngularMixedTerms

/-- The sum of the actual coordinate counts is the actual list length. -/
theorem sum_countIndex {d : ℕ} (is : List (Fin d)) : (∑i,countIndex is i)=is.length := by
  induction is with
  | nil => simp [countIndex]
  | cons i is ih =>
    simp only [countIndex,List.count_cons,Finset.sum_add_distrib,List.length_cons]
    simp [beq_iff_eq, ← ih, countIndex]


theorem countIndex_pos_of_mem {d : ℕ} {is : List (Fin d)} {i : Fin d} (hi : i∈is) :
    1≤countIndex is i := List.count_pos_iff.mpr hi

/-- A mixed derivative of order greater than one never has a first-order count index. -/
theorem countIndex_ne_single_of_length {d : ℕ} (is : List (Fin d)) (hl : 1 < is.length) (i : Fin d) :
    countIndex is≠Pi.single i 1 := by
  intro h
  have hs := congrArg (fun a : Fin d→ℕ => ∑j,a j) h
  rw [sum_countIndex] at hs
  simp [Pi.single_apply] at hs
  omega

/-- The exact pair of index facts needed for strict comparison against a chosen first direction. -/
theorem countIndex_strict_comparison_data {d : ℕ} (is : List (Fin d))
    (hl : 1 < is.length) {i : Fin d} (hi : i∈is) :
    1≤countIndex is i ∧ countIndex is≠Pi.single i 1 :=
  ⟨countIndex_pos_of_mem hi,countIndex_ne_single_of_length is hl i⟩

#print axioms countIndex_strict_comparison_data
end Legacy.BecknerOnofri.AngularMixedTerms
