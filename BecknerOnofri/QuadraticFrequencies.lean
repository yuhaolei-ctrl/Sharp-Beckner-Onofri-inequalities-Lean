import BecknerOnofri.ComplementGap
import BecknerOnofri.FirstShellSharpness

/-! Exact frequency identities for the quadratic first-shell modes. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace BecknerOnofri.HighDim.QuadraticModes

@[simp] theorem axis_total {d : ℕ} (i : Fin d) : ∑ k, axisFrequency i k = 1 := by
  simp [axisFrequency]

theorem axis_injective {d : ℕ} : Function.Injective (@axisFrequency d) := by
  intro i j h
  have hh := congrFun h i
  by_contra hij
  simp [axisFrequency, hij] at hh

theorem sum_ne_zero {d : ℕ} (i j : Fin d) : axisFrequency i + axisFrequency j ≠ 0 := by
  intro h
  have h := congrArg (fun k : Frequency d => ∑ l, k l) h
  simp [Finset.sum_add_distrib] at h

theorem sum_ne_neg_sum {d : ℕ} (i j m n : Fin d) :
    axisFrequency i + axisFrequency j ≠ -(axisFrequency m + axisFrequency n) := by
  intro h
  have h := congrArg (fun k : Frequency d => ∑ l, k l) h
  simp [Finset.sum_add_distrib] at h

theorem sum_ne_diff {d : ℕ} (i j m n : Fin d) :
    axisFrequency i + axisFrequency j ≠ axisFrequency m - axisFrequency n := by
  intro h
  have h := congrArg (fun k : Frequency d => ∑ l, k l) h
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h

theorem sum_eq_sum_iff {d : ℕ} (i j m n : Fin d) :
    axisFrequency i + axisFrequency j = axisFrequency m + axisFrequency n ↔
      (i=m ∧ j=n) ∨ (i=n ∧ j=m) := by
  constructor
  · intro h
    have hi := congrFun h i
    have hj := congrFun h j
    by_cases him : i=m
    · left
      subst m
      have he : axisFrequency j = axisFrequency n := add_left_cancel h
      exact ⟨rfl, axis_injective he⟩
    · right
      have hin : i=n := by
        by_contra hin
        simp [axisFrequency, him, hin] at hi
        split_ifs at hi <;> omega
      subst n
      have he : axisFrequency j = axisFrequency m := by
        have hh : axisFrequency j + axisFrequency i = axisFrequency m + axisFrequency i := by
          simpa [add_comm] using h
        exact add_right_cancel hh
      exact ⟨rfl, axis_injective he⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · rfl
    · exact add_comm _ _

theorem diff_eq_diff_iff {d : ℕ} {i j : Fin d} (hij : i ≠ j) (m n : Fin d) :
    axisFrequency i - axisFrequency j = axisFrequency m - axisFrequency n ↔ i=m ∧ j=n := by
  constructor
  · intro h
    have hi := congrFun h i
    have hj := congrFun h j
    have him : i=m := by
      by_contra him
      simp [axisFrequency, hij, him] at hi
      split_ifs at hi <;> omega
    have hjn : j=n := by
      by_contra hjn
      simp [axisFrequency, Ne.symm hij, hjn] at hj
      split_ifs at hj <;> omega
    exact ⟨him,hjn⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem double_eq_sum_iff {d : ℕ} (i m n : Fin d) :
    axisFrequency i + axisFrequency i = axisFrequency m + axisFrequency n ↔ i=m ∧ i=n := by
  rw [sum_eq_sum_iff]
  tauto

theorem zero_eq_diff_iff {d : ℕ} (i j : Fin d) :
    (0 : Frequency d) = axisFrequency i - axisFrequency j ↔ i=j := by
  rw [eq_comm, sub_eq_zero]
  exact axis_injective.eq_iff

theorem latticeSquare_double {d : ℕ} (i : Fin d) :
    latticeSquare (axisFrequency i + axisFrequency i) = 4 := by
  unfold latticeSquare
  rw [Finset.sum_eq_single i]
  · norm_num [axisFrequency]
  · intro j _ hji
    simp [axisFrequency, hji]
  · simp

theorem latticeSquare_sum {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    latticeSquare (axisFrequency i + axisFrequency j) = 2 := by
  unfold latticeSquare
  have h (l : Fin d) : (axisFrequency i l + axisFrequency j l).natAbs^2 =
      (if l=i then 1 else 0) + (if l=j then 1 else 0) := by
    by_cases hli : l=i
    · subst l
      simp [axisFrequency, hij]
    · by_cases hlj : l=j
      · subst l
        simp [axisFrequency, Ne.symm hij]
      · simp [axisFrequency, hli, hlj]
  simp only [Pi.add_apply, h, Finset.sum_add_distrib]
  simp

theorem latticeSquare_diff {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    latticeSquare (axisFrequency i - axisFrequency j) = 2 := by
  unfold latticeSquare
  have h (l : Fin d) : (axisFrequency i l - axisFrequency j l).natAbs^2 =
      (if l=i then 1 else 0) + (if l=j then 1 else 0) := by
    by_cases hli : l=i
    · subst l
      simp [axisFrequency, hij]
    · by_cases hlj : l=j
      · subst l
        simp [axisFrequency, Ne.symm hij]
      · simp [axisFrequency, hli, hlj]
  simp only [Pi.sub_apply, h, Finset.sum_add_distrib]
  simp

theorem complement_double {d : ℕ} (i : Fin d) :
    ComplementFrequency (axisFrequency i + axisFrequency i) := by
  constructor
  · exact sum_ne_zero i i
  · intro h
    have hh := (latticeSquare_eq_one_iff _).mpr h
    rw [latticeSquare_double] at hh
    norm_num at hh

theorem complement_sum {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    ComplementFrequency (axisFrequency i + axisFrequency j) := by
  constructor
  · exact sum_ne_zero i j
  · intro h
    have hh := (latticeSquare_eq_one_iff _).mpr h
    rw [latticeSquare_sum hij] at hh
    norm_num at hh

theorem complement_diff {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    ComplementFrequency (axisFrequency i - axisFrequency j) := by
  constructor
  · intro h
    exact hij (axis_injective (sub_eq_zero.mp h))
  · intro h
    have hh := (latticeSquare_eq_one_iff _).mpr h
    rw [latticeSquare_diff hij] at hh
    norm_num at hh

theorem eigenvalue_double {d : ℕ} (i : Fin d) :
    frequencyLength (axisFrequency i + axisFrequency i)^d = (2:ℝ)^d := by
  have h : frequencyLength (axisFrequency i + axisFrequency i) = 2 := by
    rw [frequencyLength, ← latticeSquare_cast, latticeSquare_double]
    norm_num
  rw [h]

theorem eigenvalue_sum {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    frequencyLength (axisFrequency i + axisFrequency j)^d = (2:ℝ)^((d:ℝ)/2) := by
  rw [frequencyLength, ← latticeSquare_cast, latticeSquare_sum hij]
  norm_num only [Nat.cast_ofNat]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

theorem eigenvalue_diff {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    frequencyLength (axisFrequency i - axisFrequency j)^d = (2:ℝ)^((d:ℝ)/2) := by
  rw [frequencyLength, ← latticeSquare_cast, latticeSquare_diff hij]
  norm_num only [Nat.cast_ofNat]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

#print axioms eigenvalue_sum
end BecknerOnofri.HighDim.QuadraticModes
