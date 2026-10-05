module

public import BecknerOnofri.QuadraticModes
public import BecknerOnofri.QuadraticFrequencies

@[expose] public section

/-! Exact first-shell-square coefficients at the second and mixed modes. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open Classical
namespace BecknerOnofri.HighDim.QuadraticModes
open ContinuousGibbs ContinuousFirstShell

theorem shellSquare_double {d : ℕ} (z : Coordinates d) (i : Fin d) :
    coefficient (axisFrequency i + axisFrequency i) (shellSquare z) = z i^2 := by
  rw [shellSquare_coefficient]
  simp only [double_eq_sum_iff, if_neg (sum_ne_neg_sum _ _ _ _), if_neg (sum_ne_diff _ _ _ _),
    neg_sub, if_neg (sum_ne_diff _ _ _ _), add_zero]
  simp [ite_and, pow_two]

theorem shellSquare_sum {d : ℕ} (z : Coordinates d) {i j : Fin d} (hij : i ≠ j) :
    coefficient (axisFrequency i + axisFrequency j) (shellSquare z) = 2*z i*z j := by
  rw [shellSquare_coefficient]
  simp only [sum_eq_sum_iff, if_neg (sum_ne_neg_sum _ _ _ _), if_neg (sum_ne_diff _ _ _ _),
    neg_sub, if_neg (sum_ne_diff _ _ _ _), add_zero]
  have hf (m n : Fin d) :
      (if (i=m ∧ j=n) ∨ (i=n ∧ j=m) then z m*z n else 0) =
      (if i=m ∧ j=n then z m*z n else 0) + (if i=n ∧ j=m then z m*z n else 0) := by
    by_cases ha : i=m ∧ j=n <;> by_cases hb : i=n ∧ j=m
    · exact (hij (ha.1.trans hb.2.symm)).elim
    · rw [if_pos (Or.inl ha), if_pos ha, if_neg hb, add_zero]
    · rw [if_pos (Or.inr hb), if_neg ha, if_pos hb, zero_add]
    · rw [if_neg (not_or.mpr ⟨ha,hb⟩), if_neg ha, if_neg hb, add_zero]
  simp only [hf, Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel]
  simp
  ring

theorem shellSquare_diff {d : ℕ} (z : Coordinates d) {i j : Fin d} (hij : i ≠ j) :
    coefficient (axisFrequency i - axisFrequency j) (shellSquare z) = 2*z i*conj (z j) := by
  rw [shellSquare_coefficient]
  have hn (m n : Fin d) : axisFrequency i - axisFrequency j ≠ -(axisFrequency m + axisFrequency n) := by
    intro h
    have hh : axisFrequency m + axisFrequency n = axisFrequency j - axisFrequency i := by
      simpa only [neg_neg, neg_sub] using congrArg Neg.neg h.symm
    exact sum_ne_diff _ _ _ _ hh
  simp only [if_neg (Ne.symm (sum_ne_diff _ _ _ _)), if_neg (hn _ _), zero_add,
    diff_eq_diff_iff hij, neg_sub]
  simp only [diff_eq_diff_iff hij, ite_and, map_mul, map_star, starRingEnd_self_apply,
    Finset.sum_add_distrib, Finset.sum_ite_irrel]
  simp
  ring

theorem quadraticSource_double {d : ℕ} (z : Coordinates d) (i : Fin d) :
    coefficient (axisFrequency i + axisFrequency i) (quadraticSource z).val = z i^2 := by
  rw [quadraticSource_coefficient, if_pos (complement_double i), shellSquare_double]

theorem quadraticSource_sum {d : ℕ} (z : Coordinates d) {i j : Fin d} (hij : i ≠ j) :
    coefficient (axisFrequency i + axisFrequency j) (quadraticSource z).val = 2*z i*z j := by
  rw [quadraticSource_coefficient, if_pos (complement_sum hij), shellSquare_sum z hij]

theorem quadraticSource_diff {d : ℕ} (z : Coordinates d) {i j : Fin d} (hij : i ≠ j) :
    coefficient (axisFrequency i - axisFrequency j) (quadraticSource z).val = 2*z i*conj (z j) := by
  rw [quadraticSource_coefficient, if_pos (complement_diff hij), shellSquare_diff z hij]

#print axioms quadraticSource_double
#print axioms quadraticSource_sum
#print axioms quadraticSource_diff
end BecknerOnofri.HighDim.QuadraticModes
