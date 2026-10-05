module

public import Legacy.BecknerOnofri.FiniteDifferenceDefs
public import Mathlib.Algebra.Group.ForwardDiff

@[expose] public section

/-! The explicit rectangular finite-grid difference satisfies the true
coordinatewise forward-difference recurrence. -/

noncomputable section
open scoped BigOperators
open Finset

namespace Legacy.BecknerOnofri.FiniteDifferences

@[simp] theorem rectangularDifference_zero {d : ℕ} (h : ℝ) (f : Space d → ℝ) (x : Space d) :
    rectangularDifference 0 h f x = f x := by
  simp only [rectangularDifference, DifferenceGrid, Finsupp.zero_apply]
  simp
  change f (x + 0) = f x
  rw [add_zero]

def oneDifference (n : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ j : Fin (n+1), (-1 : ℝ)^(n-j.val) * (n.choose j.val : ℝ) * F j.val

theorem oneDifference_eq_iter (n : ℕ) (F : ℕ → ℝ) :
    oneDifference n F = (fwdDiff (1 : ℕ))^[n] F 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold oneDifference
  calc
    _ = ∑ j ∈ range (n+1), (-1 : ℝ)^(n-j) * (n.choose j : ℝ) * F j :=
      Fin.sum_univ_eq_sum_range _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [zsmul_eq_mul]

theorem oneDifference_succ (n : ℕ) (F : ℕ → ℝ) :
    oneDifference (n+1) F = oneDifference n (fun j => F (j+1)) - oneDifference n F := by
  rw [oneDifference_eq_iter, Function.iterate_succ_apply', fwdDiff]
  rw [oneDifference_eq_iter, oneDifference_eq_iter]
  rw [fwdDiff_iter_comp_add]

abbrev OtherGrid {d : ℕ} (a : Index d) (i : Fin d) :=
  ∀ j : {j : Fin d // j ≠ i}, Fin (a j.val+1)

def splitGrid {d : ℕ} (a : Index d) (i : Fin d) (n : ℕ) :
    DifferenceGrid (a.update i n) ≃ Fin (n+1) × OtherGrid a i :=
  (Equiv.piSplitAt i (fun j => Fin ((a.update i n) j+1))).trans
    (Equiv.prodCongr (finCongr (by simp))
      (Equiv.piCongrRight (fun j => finCongr (by simp [Finsupp.update_apply, j.property]))))

@[simp] theorem splitGrid_fst_val {d : ℕ} (a : Index d) (i : Fin d) (n : ℕ)
    (j : DifferenceGrid (a.update i n)) : (splitGrid a i n j).1.val = (j i).val := rfl

@[simp] theorem splitGrid_snd_val {d : ℕ} (a : Index d) (i : Fin d) (n : ℕ)
    (j : DifferenceGrid (a.update i n)) (k : {k : Fin d // k ≠ i}) :
    ((splitGrid a i n j).2 k).val = (j k.val).val := rfl

def otherWeight {d : ℕ} (a : Index d) (i : Fin d) (q : OtherGrid a i) : ℝ :=
  ∏ j, (-1 : ℝ) ^ (a j.val - (q j).val) * ((a j.val).choose (q j).val : ℝ)

def shiftedGridPoint {d : ℕ} {a : Index d} {i : Fin d}
    (q : OtherGrid a i) (h : ℝ) (r : ℕ) (x : Space d) : Space d :=
  x + fun j => (if hj : j = i then (r : ℝ) else ((q ⟨j, hj⟩).val : ℝ)) * h

theorem splitGrid_point {d : ℕ} (a : Index d) (i : Fin d) (n : ℕ)
    (j : DifferenceGrid (a.update i n)) (h : ℝ) (x : Space d) :
    shiftedGridPoint (splitGrid a i n j).2 h (splitGrid a i n j).1.val x =
      x + fun k => ((j k).val : ℝ) * h := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [shiftedGridPoint]
  · simp [shiftedGridPoint, hk]

theorem splitGrid_weight {d : ℕ} (a : Index d) (i : Fin d) (n : ℕ)
    (j : DifferenceGrid (a.update i n)) :
    (∏ k : Fin d, (-1 : ℝ)^((a.update i n) k-(j k).val) *
      (((a.update i n) k).choose (j k).val : ℝ)) =
      ((-1 : ℝ)^(n-(splitGrid a i n j).1.val) * (n.choose (splitGrid a i n j).1.val : ℝ)) *
        otherWeight a i (splitGrid a i n j).2 := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Finsupp.update_apply, splitGrid_fst_val]
  congr 1
  rw [Finset.prod_subtype _ (show ∀ k : Fin d, k ∈ univ.erase i ↔ k ≠ i by simp)]
  apply Finset.prod_congr rfl
  intro k hk
  simp [k.property]

theorem rectangularDifference_update {d : ℕ} (a : Index d) (i : Fin d) (n : ℕ)
    (h : ℝ) (f : Space d → ℝ) (x : Space d) :
    rectangularDifference (a.update i n) h f x =
      ∑ q : OtherGrid a i, otherWeight a i q *
        oneDifference n (fun r => f (shiftedGridPoint q h r x)) := by
  unfold rectangularDifference
  calc
    _ = ∑ z : Fin (n+1) × OtherGrid a i,
        ((-1 : ℝ)^(n-z.1.val) * (n.choose z.1.val : ℝ)) * otherWeight a i z.2 *
          f (shiftedGridPoint z.2 h z.1.val x) := by
      apply Fintype.sum_equiv (splitGrid a i n)
      intro j
      rw [splitGrid_point, splitGrid_weight]
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [oneDifference, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

theorem shiftedGridPoint_succ {d : ℕ} {a : Index d} {i : Fin d}
    (q : OtherGrid a i) (h : ℝ) (r : ℕ) (x : Space d) :
    shiftedGridPoint q h (r+1) x = shiftedGridPoint q h r (translate x i h) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [shiftedGridPoint, translate, basis]
    ring
  · simp [shiftedGridPoint, translate, basis, hk]

/-- Successor recurrence of the explicitly defined full rectangular grid sum. -/
theorem rectangularDifference_succ {d : ℕ} (a : Index d) (i : Fin d)
    (h : ℝ) (f : Space d → ℝ) (x : Space d) :
    rectangularDifference (a + Finsupp.single i 1) h f x =
      rectangularDifference a h f (translate x i h) - rectangularDifference a h f x := by
  have hself : a.update i (a i) = a := by
    ext k
    simp only [Finsupp.update_apply]
    split_ifs with hk
    · exact congrArg a hk.symm
    · rfl
  have hsucc : a + Finsupp.single i 1 = a.update i (a i + 1) := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [Finsupp.update_apply]
    · simp [Finsupp.update_apply, hk]
  have hl := rectangularDifference_update a i (a i) h f (translate x i h)
  have hr := rectangularDifference_update a i (a i) h f x
  rw [hself] at hl hr
  rw [hsucc, rectangularDifference_update, hl, hr]
  simp only [oneDifference_succ, shiftedGridPoint_succ, mul_sub, Finset.sum_sub_distrib]

#print axioms rectangularDifference_zero
#print axioms rectangularDifference_succ

end Legacy.BecknerOnofri.FiniteDifferences
