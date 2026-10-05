import BecknerOnofri.LatticeDefinitions
import BecknerOnofri.RectangleReserve
import Mathlib.Data.Int.Interval

/-!
Actual finite lattice rectangles and coordinate projections.  A deleted
coordinate is represented by radius zero in the original ambient lattice;
the exponent is changed explicitly, as in the manuscript.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Finset

namespace BecknerOnofri.RectangleLattice

def support {d : ℕ} (k : Lattice d) : Finset (Fin d) := univ.filter (fun i => k i ≠ 0)

def cubeRadii {d : ℕ} (A : Finset (Fin d)) : Fin d → ℕ := fun i => if i ∈ A then 1 else 0

theorem mem_box {d : ℕ} (R : Fin d → ℕ) (k : Lattice d) :
    k ∈ box R ↔ ∀ i, -(R i : ℤ) ≤ k i ∧ k i ≤ (R i : ℤ) := by
  simp [box, Fintype.mem_piFinset]

theorem box_delete {d : ℕ} (R : Fin d → ℕ) (i : Fin d) :
    box (Function.update R i 0) = (box R).filter (fun k => k i = 0) := by
  ext k
  simp only [mem_filter, mem_box]
  constructor
  · intro h
    have hi := h i
    simp only [Function.update_self, Nat.cast_zero, neg_zero] at hi
    have hki : k i = 0 := le_antisymm hi.2 hi.1
    refine ⟨?_, hki⟩
    intro j
    by_cases hj : j = i
    · subst j
      rw [hki]
      constructor <;> omega
    · simpa [Function.update_of_ne hj] using h j
  · rintro ⟨h, hi⟩ j
    by_cases hj : j = i
    · subst j
      simp [hi]
    · simpa [Function.update_of_ne hj] using h j

theorem puncturedBox_delete {d : ℕ} (R : Fin d → ℕ) (i : Fin d) :
    puncturedBox (Function.update R i 0) = (puncturedBox R).filter (fun k => k i = 0) := by
  rw [puncturedBox, box_delete]
  ext k
  simp [puncturedBox, and_comm, and_assoc]

theorem latticeSum_delete {d : ℕ} (p : ℝ) (R : Fin d → ℕ) (i : Fin d) :
    latticeSum p (Function.update R i 0) =
      ∑ k ∈ puncturedBox R, if k i = 0 then weight p k else 0 := by
  unfold latticeSum
  rw [puncturedBox_delete, sum_filter]

/-- Count the coordinate projections containing each actual lattice vector. -/
theorem sum_latticeSum_delete {d : ℕ} (p : ℝ) (R : Fin d → ℕ) :
    (∑ i : Fin d, latticeSum p (Function.update R i 0)) =
      ∑ k ∈ puncturedBox R, ((d : ℝ) - ((support k).card : ℝ)) * weight p k := by
  simp_rw [latticeSum_delete]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  have hc : (univ.filter (fun i : Fin d => k i = 0)).card + (support k).card = d := by
    simpa [support] using card_filter_add_card_filter_not
      (s := (univ : Finset (Fin d))) (p := fun i => k i = 0)
  have hc' : ((univ.filter (fun i : Fin d => k i = 0)).card : ℝ) +
      ((support k).card : ℝ) = (d : ℝ) := by exact_mod_cast hc
  congr 1
  linarith

theorem support_eq_empty_iff {d : ℕ} (k : Lattice d) : support k = ∅ ↔ k = 0 := by
  simp [support, filter_eq_empty_iff, funext_iff]

theorem mem_cube_box {d : ℕ} (A : Finset (Fin d)) (k : Lattice d) :
    k ∈ box (cubeRadii A) ↔ ∀ i, if i ∈ A then k i ∈ ({-1, 0, 1} : Finset ℤ) else k i = 0 := by
  rw [mem_box]
  constructor
  · intro h i
    have hi := h i
    by_cases hm : i ∈ A
    · simp only [cubeRadii, hm, if_true, Nat.cast_one] at hi
      simp only [hm, if_true, mem_insert, mem_singleton]
      omega
    · simp only [cubeRadii, hm, if_false, Nat.cast_zero, neg_zero] at hi
      simp only [hm, if_false]
      omega
  · intro h i
    have hi := h i
    by_cases hm : i ∈ A
    · simp only [hm, if_true, mem_insert, mem_singleton] at hi
      simp only [cubeRadii, hm, if_true, Nat.cast_one]
      omega
    · simp only [hm, if_false] at hi
      simp [cubeRadii, hm, hi]

theorem support_subset_of_mem_cube {d : ℕ} {A : Finset (Fin d)} {k : Lattice d}
    (hk : k ∈ box (cubeRadii A)) : support k ⊆ A := by
  intro i hi
  have hn : k i ≠ 0 := (mem_filter.mp hi).2
  have h := (mem_cube_box A k).mp hk i
  by_contra hm
  simp only [hm, if_false] at h
  exact hn h

theorem cube_normSq {d : ℕ} {A : Finset (Fin d)} {k : Lattice d}
    (hk : k ∈ box (cubeRadii A)) : normSq k = ((support k).card : ℝ) := by
  unfold normSq support
  rw [card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, sum_filter]
  apply sum_congr rfl
  intro i hi
  have h := (mem_cube_box A k).mp hk i
  by_cases hm : i ∈ A
  · simp only [hm, if_true, mem_insert, mem_singleton] at h
    rcases h with h | h | h <;> simp [h]
  · simp only [hm, if_false] at h
    simp [h]

theorem cube_support_fiber_eq {d : ℕ} (A s : Finset (Fin d)) (hs : s ⊆ A) :
    ((box (cubeRadii A)).filter (fun k => support k = s)) =
      Fintype.piFinset (fun i => if i ∈ s then ({-1, 1} : Finset ℤ) else {0}) := by
  ext k
  simp only [mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hk, hks⟩ i
    have hki := (mem_cube_box A k).mp hk i
    have hsup := Finset.ext_iff.mp hks i
    by_cases his : i ∈ s
    · have hiA := hs his
      have hin : k i ≠ 0 := by simpa [support] using hsup.mpr his
      simp only [hiA, if_true, mem_insert, mem_singleton] at hki
      simp only [his, if_true, mem_insert, mem_singleton]
      omega
    · have hiz : k i = 0 := by
        by_contra h
        exact his (hsup.mp (by simp [support, h]))
      simp [his, hiz]
  · intro h
    constructor
    · apply (mem_cube_box A k).mpr
      intro i
      have hi := h i
      by_cases his : i ∈ s
      · have hiA := hs his
        simp only [his, if_true, mem_insert, mem_singleton] at hi
        simp only [hiA, if_true, mem_insert, mem_singleton]
        omega
      · simp only [his, if_false, mem_singleton] at hi
        simp [hi]
    · ext i
      have hi := h i
      by_cases his : i ∈ s
      · simp only [his, if_true, mem_insert, mem_singleton] at hi
        have hin : k i ≠ 0 := by omega
        simp [support, his, hin]
      · simp only [his, if_false, mem_singleton] at hi
        simp [support, his, hi]

theorem cube_support_fiber_card {d : ℕ} (A s : Finset (Fin d)) (hs : s ⊆ A) :
    ((box (cubeRadii A)).filter (fun k => support k = s)).card = 2 ^ s.card := by
  rw [cube_support_fiber_eq A s hs, Fintype.card_piFinset]
  have hc (i : Fin d) : (if i ∈ s then ({-1, 1} : Finset ℤ) else {0}).card =
      if i ∈ s then 2 else 1 := by split_ifs <;> norm_num
  simp_rw [hc]
  simp

/-- Exact enumeration of the support size in an actual zero-one lattice box. -/
theorem sum_cube_support {d : ℕ} (A : Finset (Fin d)) (f : ℕ → ℝ) :
    (∑ k ∈ box (cubeRadii A), f (support k).card) =
      ∑ j ∈ range (A.card + 1), (2 : ℝ) ^ j * (A.card.choose j : ℝ) * f j := by
  have hmap : ∀ k ∈ box (cubeRadii A), support k ∈ A.powerset := by
    intro k hk
    exact mem_powerset.mpr (support_subset_of_mem_cube hk)
  calc
    _ = ∑ s ∈ A.powerset,
        ∑ k ∈ (box (cubeRadii A)).filter (fun k => support k = s), f (support k).card :=
      (sum_fiberwise_of_maps_to hmap _).symm
    _ = ∑ s ∈ A.powerset, (2 : ℝ) ^ s.card * f s.card := by
      apply sum_congr rfl
      intro s hs
      calc
        _ = ∑ _k ∈ (box (cubeRadii A)).filter (fun k => support k = s), f s.card := by
          apply sum_congr rfl
          intro k hk
          rw [(mem_filter.mp hk).2]
        _ = _ := by
          rw [sum_const, nsmul_eq_mul, cube_support_fiber_card A s (mem_powerset.mp hs)]
          norm_cast
    _ = _ := by
      rw [sum_powerset]
      apply sum_congr rfl
      intro j hj
      have hh := sum_powersetCard j A (fun n => (2 : ℝ) ^ n * f n)
      simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hh

/-- Puncturing a lattice cube removes exactly the empty support. -/
theorem sum_punctured_cube_support {d : ℕ} (A : Finset (Fin d)) (f : ℕ → ℝ) :
    (∑ k ∈ puncturedBox (cubeRadii A), f (support k).card) =
      ∑ j ∈ range (A.card + 1), if j = 0 then 0 else
        (2 : ℝ) ^ j * (A.card.choose j : ℝ) * f j := by
  unfold puncturedBox
  rw [sum_filter]
  have he (k : Lattice d) : (if k ≠ 0 then f (support k).card else 0) =
      (if (support k).card = 0 then 0 else f (support k).card) := by
    have hh : (support k).card = 0 ↔ k = 0 := card_eq_zero.trans (support_eq_empty_iff k)
    by_cases hk : k = 0
    · rw [if_neg (by simp [hk]), if_pos (hh.mpr hk)]
    · rw [if_pos hk, if_neg (mt hh.mp hk)]
  simp_rw [he]
  rw [sum_cube_support A (fun n => if n = 0 then 0 else f n)]
  apply sum_congr rfl
  intro j hj
  split_ifs <;> simp_all

theorem latticeSum_cube {d : ℕ} (p : ℝ) (A : Finset (Fin d)) :
    latticeSum p (cubeRadii A) =
      ∑ j ∈ range (A.card + 1), if j = 0 then 0 else
        (2 : ℝ) ^ j * (A.card.choose j : ℝ) * (j : ℝ) ^ (-(p / 2)) := by
  unfold latticeSum
  have he : (∑ k ∈ puncturedBox (cubeRadii A), weight p k) =
      ∑ k ∈ puncturedBox (cubeRadii A), ((support k).card : ℝ) ^ (-(p / 2)) := by
    apply sum_congr rfl
    intro k hk
    rw [weight, cube_normSq (mem_filter.mp hk).1]
  rw [he]
  exact sum_punctured_cube_support A (fun n => (n : ℝ) ^ (-(p / 2)))

def deletionGap {d : ℕ} (R : Fin d → ℕ) : ℝ :=
  (1 / ((d : ℝ) - 1)) * (∑ i : Fin d, latticeSum ((d : ℝ) - 1) (Function.update R i 0)) -
    latticeSum (d : ℝ) R

theorem deletionGap_eq_sum {d : ℕ} (R : Fin d → ℕ) :
    deletionGap R = ∑ k ∈ puncturedBox R,
      ((((d : ℝ) - ((support k).card : ℝ)) / ((d : ℝ) - 1)) *
        weight ((d : ℝ) - 1) k - weight (d : ℝ) k) := by
  unfold deletionGap
  rw [sum_latticeSum_delete]
  unfold latticeSum
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  ring

theorem projected_weight_factor (d j : ℝ) (hj : 0 < j) :
    ((d - j) / (d - 1)) * j ^ (-((d - 1) / 2)) - j ^ (-(d / 2)) =
      j ^ (-(d / 2)) * (((d - j) / (d - 1)) * Real.sqrt j - 1) := by
  have he : -((d - 1) / 2) = -(d / 2) + 1 / 2 := by ring
  rw [he, Real.rpow_add hj, ← Real.sqrt_eq_rpow]
  ring

theorem cubeGap_truncate {d r : ℕ} (hrd : r ≤ d) :
    RectangleReserve.cubeGap d r = ∑ j ∈ range (r + 1),
      if 2 ≤ j then RectangleReserve.cubeWeight d r j * RectangleReserve.cubeFactor d j else 0 := by
  unfold RectangleReserve.cubeGap
  symm
  apply sum_subset (range_mono (by omega))
  intro j hjd hjr
  have hrj : r < j := by simp only [mem_range] at hjr; omega
  have hc := Nat.choose_eq_zero_of_lt hrj
  simp [RectangleReserve.cubeWeight, hc]

/-- Identify the actual projected-lattice gap with the certified cube polynomial. -/
theorem deletionGap_cube {d : ℕ} (hd : 13 ≤ d) (A : Finset (Fin d)) :
    deletionGap (cubeRadii A) = RectangleReserve.cubeGap d A.card := by
  have hAd : A.card ≤ d := by simpa using A.card_le_univ
  rw [deletionGap_eq_sum, RectangleLattice.cubeGap_truncate hAd]
  have he :
      (∑ k ∈ puncturedBox (cubeRadii A),
        ((((d : ℝ) - ((support k).card : ℝ)) / ((d : ℝ) - 1)) *
          weight ((d : ℝ) - 1) k - weight (d : ℝ) k)) =
      ∑ k ∈ puncturedBox (cubeRadii A),
        ((((d : ℝ) - ((support k).card : ℝ)) / ((d : ℝ) - 1)) *
          ((support k).card : ℝ) ^ (-(((d : ℝ) - 1) / 2)) -
            ((support k).card : ℝ) ^ (-((d : ℝ) / 2))) := by
    apply sum_congr rfl
    intro k hk
    simp only [weight, cube_normSq (mem_filter.mp hk).1]
  rw [he, sum_punctured_cube_support A (fun j =>
    (((d : ℝ) - (j : ℝ)) / ((d : ℝ) - 1)) *
      (j : ℝ) ^ (-(((d : ℝ) - 1) / 2)) - (j : ℝ) ^ (-((d : ℝ) / 2)))]
  apply sum_congr rfl
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    norm_num
  by_cases hj1 : j = 1
  · subst j
    have hd' : (d : ℝ) - 1 ≠ 0 := by
      have hdreal : (13 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    simp [hd']
  · have hj2 : 2 ≤ j := by omega
    simp only [hj0, if_false, hj2, if_true]
    rw [projected_weight_factor (d : ℝ) (j : ℝ) (by exact_mod_cast (Nat.pos_of_ne_zero hj0))]
    unfold RectangleReserve.cubeWeight RectangleReserve.cubeFactor
    ring

theorem deletionGap_cube_nonneg {d : ℕ} (hd : 13 ≤ d) (A : Finset (Fin d)) :
    0 ≤ deletionGap (cubeRadii A) := by
  rw [deletionGap_cube hd]
  exact RectangleReserve.cubeGap_nonneg hd (by simpa using A.card_le_univ)

theorem update_zero_mem_box {d : ℕ} {R : Fin d → ℕ} {k : Lattice d}
    (hk : k ∈ box R) (i : Fin d) :
    Function.update k i 0 ∈ box (Function.update R i 0) := by
  apply (mem_box _ _).mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne hj] using (mem_box R k).mp hk j

theorem coordinate_zero_of_mem_deleted {d : ℕ} {R : Fin d → ℕ} {k : Lattice d}
    (i : Fin d) (hk : k ∈ box (Function.update R i 0)) : k i = 0 := by
  have h := (mem_box _ _).mp hk i
  simp only [Function.update_self, Nat.cast_zero, neg_zero] at h
  exact le_antisymm h.2 h.1

theorem update_mem_box {d : ℕ} {R : Fin d → ℕ} {k : Lattice d} (i : Fin d)
    (hk : k ∈ box (Function.update R i 0)) {n : ℤ}
    (hn : n ∈ Icc (-(R i : ℤ)) (R i : ℤ)) : Function.update k i n ∈ box R := by
  apply (mem_box _ _).mpr
  intro j
  by_cases hj : j = i
  · subst j
    simpa using mem_Icc.mp hn
  · simpa [Function.update_of_ne hj] using (mem_box _ _).mp hk j

/-- Exact finite Fubini decomposition along a single coordinate. -/
theorem sum_box_split {d : ℕ} (R : Fin d → ℕ) (i : Fin d) (f : Lattice d → ℝ) :
    (∑ k ∈ box R, f k) = ∑ z ∈ box (Function.update R i 0),
      ∑ n ∈ Icc (-(R i : ℤ)) (R i : ℤ), f (Function.update z i n) := by
  rw [← sum_product' _ _ (fun z n => f (Function.update z i n))]
  symm
  apply sum_bij (fun zn _ => Function.update zn.1 i zn.2)
  · intro zn hzn
    exact update_mem_box i (mem_product.mp hzn).1 (mem_product.mp hzn).2
  · intro zn₁ hz₁ zn₂ hz₂ he
    have hz1 := coordinate_zero_of_mem_deleted i (mem_product.mp hz₁).1
    have hz2 := coordinate_zero_of_mem_deleted i (mem_product.mp hz₂).1
    apply Prod.ext
    · funext j
      have hh := congrFun he j
      by_cases hj : j = i
      · subst j
        exact hz1.trans hz2.symm
      · simpa [Function.update_of_ne hj] using hh
    · simpa using congrFun he i
  · intro k hk
    refine ⟨(Function.update k i 0, k i), mem_product.mpr ⟨update_zero_mem_box hk i, ?_⟩, ?_⟩
    · exact mem_Icc.mpr ((mem_box R k).mp hk i)
    · simp
  · intro zn hzn
    rfl

theorem normSq_update {d : ℕ} (k : Lattice d) (i : Fin d) (n : ℤ) (hi : k i = 0) :
    normSq (Function.update k i n) = normSq k + (n : ℝ) ^ 2 := by
  have hsum : (∑ j ∈ (univ : Finset (Fin d)).erase i,
      ((Function.update k i n) j : ℝ) ^ 2) =
      ∑ j ∈ (univ : Finset (Fin d)).erase i, (k j : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  unfold normSq
  rw [← sum_erase_add _ _ (mem_univ i), hsum]
  have hrest := sum_erase_add (s := (univ : Finset (Fin d)))
    (fun j => (k j : ℝ) ^ 2) (mem_univ i)
  simp only [Function.update_self, hi, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hrest ⊢
  rw [hrest]

/-- The finite slice hypothesis used only in the rectangle-growth reduction.
The separate analytic spectral-slice theorem must discharge this hypothesis. -/
def SliceBound (d : ℕ) : Prop :=
  ∀ q : ℝ, 4 ≤ q → ∀ R : ℕ,
    (∑ n ∈ Icc (-(R : ℤ)) (R : ℤ),
      (q + (n : ℝ) ^ 2) ^ (-((d : ℝ) / 2))) ≤
      q ^ (-(((d : ℝ) - 1) / 2))

end BecknerOnofri.RectangleLattice
