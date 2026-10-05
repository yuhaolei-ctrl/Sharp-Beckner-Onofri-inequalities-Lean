module

public import BecknerOnofri.RectangleLattice

@[expose] public section

/-! Finite face comparisons and induction on actual lattice rectangles. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Finset

namespace BecknerOnofri.RectangleLattice

def faceSum {d : ℕ} (p : ℝ) (R : Fin d → ℕ) (i : Fin d) (m : ℕ) : ℝ :=
  ∑ z ∈ box (Function.update R i 0),
    ((m : ℝ) ^ 2 + normSq z) ^ (-(p / 2))

theorem normSq_nonneg {d : ℕ} (k : Lattice d) : 0 ≤ normSq k :=
  sum_nonneg (fun _ _ => sq_nonneg _)

theorem faceSum_slice_le {d : ℕ} (hS : SliceBound d) (R : Fin d → ℕ)
    (i j : Fin d) (hji : j ≠ i) (m : ℕ) (hm : 2 ≤ m) :
    faceSum (d : ℝ) R i m ≤ faceSum ((d : ℝ) - 1) (Function.update R j 0) i m := by
  unfold faceSum
  rw [sum_box_split (Function.update R i 0) j]
  have hcomm : Function.update (Function.update R i 0) j 0 =
      Function.update (Function.update R j 0) i 0 := Function.update_comm hji.symm _ _ _
  rw [← hcomm]
  apply sum_le_sum
  intro z hz
  have hzj := coordinate_zero_of_mem_deleted j hz
  have hq : 4 ≤ (m : ℝ) ^ 2 + normSq z := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [normSq_nonneg z]
  have hh := hS ((m : ℝ) ^ 2 + normSq z) hq (R j)
  simpa only [Function.update_of_ne hji, normSq_update z j _ hzj, ← add_assoc] using hh

theorem weight_zero {d : ℕ} {p : ℝ} (hp : 0 < p) : weight p (0 : Lattice d) = 0 := by
  have he : -(p / 2) ≠ 0 := by linarith
  simp [weight, normSq, Real.zero_rpow he]

theorem latticeSum_eq_sum_box {d : ℕ} {p : ℝ} (hp : 0 < p) (R : Fin d → ℕ) :
    latticeSum p R = ∑ k ∈ box R, weight p k := by
  unfold latticeSum puncturedBox
  rw [sum_filter]
  apply sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [weight_zero hp]
  · simp [hk0]

theorem integer_interval_grow (m : ℕ) :
    Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
      insert (-((m + 1 : ℕ) : ℤ))
        (insert ((m + 1 : ℕ) : ℤ) (Icc (-(m : ℤ)) (m : ℤ))) := by
  ext n
  simp only [mem_Icc, mem_insert]
  omega

theorem sum_integer_interval_grow (m : ℕ) (f : ℤ → ℝ) :
    (∑ n ∈ Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ), f n) =
      (∑ n ∈ Icc (-(m : ℤ)) (m : ℤ), f n) +
        f (-((m + 1 : ℕ) : ℤ)) + f ((m + 1 : ℕ) : ℤ) := by
  rw [integer_interval_grow, sum_insert, sum_insert]
  · ring
  · simp only [mem_Icc]
    omega
  · simp only [mem_insert, mem_Icc]
    omega

theorem latticeSum_grow {d : ℕ} {p : ℝ} (hp : 0 < p) (R : Fin d → ℕ)
    (i : Fin d) (m : ℕ) :
    latticeSum p (Function.update R i (m + 1)) =
      latticeSum p (Function.update R i m) + 2 * faceSum p R i (m + 1) := by
  rw [latticeSum_eq_sum_box hp, latticeSum_eq_sum_box hp]
  rw [sum_box_split (Function.update R i (m + 1)) i,
    sum_box_split (Function.update R i m) i]
  simp only [Function.update_idem, Function.update_self]
  simp_rw [sum_integer_interval_grow]
  rw [sum_add_distrib, sum_add_distrib]
  have hpos : (∑ z ∈ box (Function.update R i 0),
      weight p (Function.update z i ((m + 1 : ℕ) : ℤ))) = faceSum p R i (m + 1) := by
    apply sum_congr rfl
    intro z hz
    rw [weight, normSq_update z i _ (coordinate_zero_of_mem_deleted i hz)]
    simp [add_comm]
  have hneg : (∑ z ∈ box (Function.update R i 0),
      weight p (Function.update z i (-((m + 1 : ℕ) : ℤ)))) = faceSum p R i (m + 1) := by
    apply sum_congr rfl
    intro z hz
    rw [weight, normSq_update z i _ (coordinate_zero_of_mem_deleted i hz)]
    simp only [Int.cast_neg, Int.cast_natCast, neg_sq]
    rw [add_comm]
  rw [hpos, hneg]
  ring

theorem deletion_sum_grow {d : ℕ} {p : ℝ} (hp : 0 < p) (R : Fin d → ℕ)
    (i : Fin d) (m : ℕ) :
    (∑ j : Fin d, latticeSum p (Function.update (Function.update R i (m + 1)) j 0)) =
      (∑ j : Fin d, latticeSum p (Function.update (Function.update R i m) j 0)) +
        2 * ∑ j ∈ (univ : Finset (Fin d)).erase i,
          faceSum p (Function.update R j 0) i (m + 1) := by
  have he (j : Fin d) :
      latticeSum p (Function.update (Function.update R i (m + 1)) j 0) =
        latticeSum p (Function.update (Function.update R i m) j 0) +
          (if j = i then 0 else 2 * faceSum p (Function.update R j 0) i (m + 1)) := by
    by_cases hj : j = i
    · subst j
      simp
    · simpa only [hj, if_false, Function.update_comm (Ne.symm hj)] using
        latticeSum_grow hp (Function.update R j 0) i m
  simp_rw [he]
  rw [sum_add_distrib]
  congr 1
  have hfilter : (univ : Finset (Fin d)).filter (fun j => j ≠ i) = univ.erase i := by
    ext j
    simp
  calc
    _ = ∑ j ∈ (univ : Finset (Fin d)).filter (fun j => j ≠ i),
        2 * faceSum p (Function.update R j 0) i (m + 1) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j hj
      by_cases hji : j = i <;> simp [hji]
    _ = _ := by rw [hfilter, mul_sum]

theorem deletionGap_grow {d : ℕ} (hd : 13 ≤ d) (hS : SliceBound d)
    (R : Fin d → ℕ) (i : Fin d) (m : ℕ) (hm : 1 ≤ m) :
    deletionGap (Function.update R i m) ≤ deletionGap (Function.update R i (m + 1)) := by
  have hdreal : (13 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdm : 0 < (d : ℝ) - 1 := by linarith
  have hsum := sum_le_sum (s := (univ : Finset (Fin d)).erase i)
    (fun j hj => faceSum_slice_le hS R i j (mem_erase.mp hj).1 (m + 1) (by omega))
  simp only [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin, Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one] at hsum
  have hf : faceSum (d : ℝ) R i (m + 1) ≤
      (1 / ((d : ℝ) - 1)) * ∑ j ∈ (univ : Finset (Fin d)).erase i,
        faceSum ((d : ℝ) - 1) (Function.update R j 0) i (m + 1) := by
    have hh : faceSum (d : ℝ) R i (m + 1) ≤
        (∑ j ∈ (univ : Finset (Fin d)).erase i,
          faceSum ((d : ℝ) - 1) (Function.update R j 0) i (m + 1)) / ((d : ℝ) - 1) :=
      (le_div_iff₀ hdm).mpr (by simpa only [mul_comm] using hsum)
    calc
      _ ≤ _ := hh
      _ = _ := by ring
  unfold deletionGap
  rw [deletion_sum_grow hdm, latticeSum_grow hdpos]
  nlinarith

/-- Induction over the sum of the side radii reduces every actual rectangle
to a zero-one cube. The only analytic input is the explicit finite slice bound. -/
theorem deletionGap_nonneg_of_slice {d : ℕ} (hd : 13 ≤ d) (hS : SliceBound d)
    (R : Fin d → ℕ) : 0 ≤ deletionGap R := by
  have h : ∀ n : ℕ, ∀ R : Fin d → ℕ, (∑ i, R i) = n → 0 ≤ deletionGap R := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R htotal
      by_cases hsmall : ∀ i, R i ≤ 1
      · let A : Finset (Fin d) := univ.filter (fun i => R i = 1)
        have he : R = cubeRadii A := by
          funext i
          by_cases hi : R i = 1
          · simp [cubeRadii, A, hi]
          · have hz : R i = 0 := by have hh := hsmall i; omega
            simp [cubeRadii, A, hz]
        rw [he]
        exact deletionGap_cube_nonneg hd A
      · push Not at hsmall
        obtain ⟨i, hi⟩ := hsmall
        let R' : Fin d → ℕ := Function.update R i (R i - 1)
        have hless : (∑ j, R' j) < ∑ j, R j := by
          apply sum_lt_sum
          · intro j hj
            by_cases hji : j = i
            · subst j
              simp [R']
            · simp [R', Function.update_of_ne hji]
          · refine ⟨i, mem_univ _, ?_⟩
            simp only [R', Function.update_self]
            omega
        have hprev : 0 ≤ deletionGap R' := ih (∑ j, R' j) (by omega) R' rfl
        have hg := deletionGap_grow hd hS R i (R i - 1) (by omega)
        have he : R i - 1 + 1 = R i := by omega
        rw [he, Function.update_eq_self] at hg
        exact hprev.trans hg
  exact h (∑ i, R i) R rfl

/-- The manuscript's rectangular lattice inequality, pending only the
separate genuine analytic slice theorem. Deleted coordinates have radius zero. -/
theorem rectangle_comparison_of_slice {d : ℕ} (hd : 13 ≤ d) (hS : SliceBound d)
    (R : Fin d → ℕ) :
    latticeSum (d : ℝ) R ≤ (1 / ((d : ℝ) - 1)) *
      (∑ i : Fin d, latticeSum ((d : ℝ) - 1) (Function.update R i 0)) := by
  have h := deletionGap_nonneg_of_slice hd hS R
  unfold deletionGap at h
  linarith

end BecknerOnofri.RectangleLattice
