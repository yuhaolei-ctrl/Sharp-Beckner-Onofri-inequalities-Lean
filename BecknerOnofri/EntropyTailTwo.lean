import BecknerOnofri.EntropyTailPolynomialExpansion

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Polynomial
open Finset
namespace BecknerOnofri.HighDim.EntropyTail

theorem outsideCube_iff_not_mem (k : Frequency 12) :
    outsideCube k ↔ k ∉ RectangleLattice.box (fun _ : Fin 12 => 1) := by
  simp only [RandomRectangles.mem_box_natAbs, outsideCube]
  push Not
  rfl

theorem scalarTail_two_polynomial : scalarTail 2 =
    ((inverseSixth (radialPolynomial 2 12) - inverseSixth (radialPolynomial 1 12) : ℚ) : ℝ) := by
  classical
  let f : Frequency 12 → ℝ := fun k =>
    (frequencyLength k^12)⁻¹ * ∏ i : Fin 12, scalarCoefficient 2 (k i).natAbs
  have hsub : RectangleLattice.box (fun _ : Fin 12 => 1) ⊆ RectangleLattice.box (fun _ : Fin 12 => 2) := by
    intro k hk
    rw [RandomRectangles.mem_box_natAbs] at hk ⊢
    intro i
    exact (hk i).trans (by norm_num)
  have hfilter : (RectangleLattice.box (fun _ : Fin 12 => 2)) \
      (RectangleLattice.box (fun _ : Fin 12 => 1)) =
      (RectangleLattice.box (fun _ : Fin 12 => 2)).filter outsideCube := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_filter, outsideCube_iff_not_mem]
  have ht : scalarTail 2 = ∑ k ∈ (RectangleLattice.box (fun _ : Fin 12 => 2)) \
      (RectangleLattice.box (fun _ : Fin 12 => 1)), f k := by
    rw [scalarTail_eq_finite_sum, hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [scalarTailWeight, f]
    split_ifs <;> simp
  have hr (r : ℕ) : (∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => r), f k) =
      ((inverseSixth (radialPolynomial r 12) : ℚ) : ℝ) := by
    rw [inverseSixth_radialPolynomial, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact coefficient_weight_cast k
  have h := Finset.sum_sdiff (f := f) hsub
  rw [← ht, hr 1, hr 2] at h
  rw [Rat.cast_sub]
  linarith

theorem scalarTail_two_upper : scalarTail 2 < 41963/500000 := by
  rw [scalarTail_two_polynomial, inverseSixth_difference_eq_shell]
  have h := (Rat.cast_lt (K := ℝ)).mpr indexTwoShellSum_upper
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem scalarTail_two_le_budget : scalarTail 2 ≤ scalarBudget 2 := by
  rw [scalarBudget_two]
  have h := scalarTail_two_upper
  linarith

theorem scalarTail_le_budget_of_le_two {n : ℕ} (hn : n ≤ 2) : scalarTail n ≤ scalarBudget n := by
  by_cases h : n ≤ 1
  · exact scalarTail_le_budget_small h
  · have he : n = 2 := by omega
    subst n
    exact scalarTail_two_le_budget

#print axioms scalarTail_two_polynomial
#print axioms scalarTail_two_upper
#print axioms scalarTail_le_budget_of_le_two
end BecknerOnofri.HighDim.EntropyTail
