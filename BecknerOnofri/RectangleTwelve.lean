module

public import BecknerOnofri.HighDimRectangles
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

/-! The d=12 rectangle case added in the 2026-09-21 manuscript.
The zero-one cube gap is checked with exact rational lower bounds for square
roots; the existing face induction then covers arbitrary coordinate radii. -/
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open scoped BigOperators
open Finset
namespace BecknerOnofri.RectangleReserve

def cubeGapTwelveLower (r : ℕ) : ℚ :=
  ∑ j ∈ range 13, if 2≤j then
    2^j*(r.choose j:ℚ)/(j:ℚ)^6 * (((12:ℚ)-j)/11*((Nat.sqrt (100*j):ℚ)/10)-1) else 0

theorem cubeGapTwelveLower_nonneg : ∀ r : Fin 13,0≤cubeGapTwelveLower r.val := by
  decide +kernel

theorem rational_sqrt_lower (j : ℕ) : (Nat.sqrt (100*j):ℝ)/10≤Real.sqrt (j:ℝ) := by
  have h : (Nat.sqrt (100*j):ℝ)^2≤100*(j:ℝ) := by
    exact_mod_cast Nat.sqrt_le' (100*j)
  have hs := Real.sq_sqrt (show (0:ℝ)≤j by positivity)
  have hp := Real.sqrt_nonneg (j:ℝ)
  nlinarith [show (0:ℝ)≤Nat.sqrt (100*j) by positivity]

theorem cubeGap_twelve_nonneg {r : ℕ} (hr : r≤12) : 0≤cubeGap 12 r := by
  have hrat : (0:ℝ)≤(cubeGapTwelveLower r:ℚ) := by
    exact_mod_cast cubeGapTwelveLower_nonneg ⟨r,by omega⟩
  apply hrat.trans
  simp only [cubeGapTwelveLower,Rat.cast_sum,apply_ite,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_sub,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,cubeGap]
  apply sum_le_sum
  intro j hj
  by_cases hj2 : 2≤j
  · simp only [hj2,if_true,cubeWeight,cubeFactor]
    norm_num only [Nat.cast_ofNat,show (-(12:ℝ)/2)=(-6:ℝ) by norm_num,
      show (-((12:ℝ)/2))=(-6:ℝ) by norm_num]
    rw [Real.rpow_neg (by positivity),show (6:ℝ)=(6:ℕ) from rfl,Real.rpow_natCast]
    have hj12 : j≤12 := by have hh := mem_range.mp hj; omega
    have hfac : 0≤((12:ℝ)-j)/11 := by
      apply div_nonneg _ (by norm_num)
      have hh : (j:ℝ)≤12 := by exact_mod_cast hj12
      linarith
    have h := mul_le_mul_of_nonneg_left (rational_sqrt_lower j) hfac
    have hw : 0≤(2:ℝ)^j*(r.choose j:ℝ)/(j:ℝ)^6 := by positivity
    convert mul_le_mul_of_nonneg_left (sub_le_sub_right h 1) hw using 1 <;> norm_num <;> ring <;> simp_all
  · simp [hj2]

end BecknerOnofri.RectangleReserve
namespace BecknerOnofri.RectangleLattice
theorem deletionGap_cube_of_two_le {d : ℕ} (hd : 2 ≤ d) (A : Finset (Fin d)) :
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
      have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    simp [hd']
  · have hj2 : 2 ≤ j := by omega
    simp only [hj0, if_false, hj2, if_true]
    rw [projected_weight_factor (d : ℝ) (j : ℝ) (by exact_mod_cast (Nat.pos_of_ne_zero hj0))]
    unfold RectangleReserve.cubeWeight RectangleReserve.cubeFactor
    ring


theorem deletionGap_cube_twelve (A : Finset (Fin 12)) :
    0≤deletionGap (cubeRadii A) := by
  rw [deletionGap_cube_of_two_le (by norm_num)]
  exact RectangleReserve.cubeGap_twelve_nonneg (by simpa using A.card_le_univ)

theorem deletionGap_grow_of_two_le {d : ℕ} (hd : 2 ≤ d) (hS : SliceBound d)
    (R : Fin d → ℕ) (i : Fin d) (m : ℕ) (hm : 1 ≤ m) :
    deletionGap (Function.update R i m) ≤ deletionGap (Function.update R i (m + 1)) := by
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
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

theorem deletionGap_nonneg_twelve (hS : SliceBound 12)
    (R : Fin 12 → ℕ) : 0 ≤ deletionGap R := by
  have h : ∀ n : ℕ, ∀ R : Fin 12 → ℕ, (∑ i, R i) = n → 0 ≤ deletionGap R := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R htotal
      by_cases hsmall : ∀ i, R i ≤ 1
      · let A : Finset (Fin 12) := univ.filter (fun i => R i = 1)
        have he : R = cubeRadii A := by
          funext i
          by_cases hi : R i = 1
          · simp [cubeRadii, A, hi]
          · have hz : R i = 0 := by have hh := hsmall i; omega
            simp [cubeRadii, A, hz]
        rw [he]
        exact deletionGap_cube_twelve A
      · push Not at hsmall
        obtain ⟨i, hi⟩ := hsmall
        let R' : Fin 12 → ℕ := Function.update R i (R i - 1)
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
        have hg := deletionGap_grow_of_two_le (by norm_num) hS R i (R i - 1) (by omega)
        have he : R i - 1 + 1 = R i := by omega
        rw [he, Function.update_eq_self] at hg
        exact hprev.trans hg
  exact h (∑ i, R i) R rfl


/-- Full updated manuscript range, retaining the actual unrestricted lattice sum. -/
theorem rectangle_comparison_ge12 {d : ℕ} (hd : 12≤d) (R : Fin d → ℕ) :
    latticeSum (d:ℝ) R ≤ (1/((d:ℝ)-1))*
      ∑ i : Fin d,latticeSum ((d:ℝ)-1) (Function.update R i 0) := by
  by_cases he : d=12
  · subst d
    have h := deletionGap_nonneg_twelve (sliceBound (by norm_num)) R
    unfold deletionGap at h
    linarith
  · exact rectangle_comparison (by omega) R

#print axioms rectangle_comparison_ge12
end BecknerOnofri.RectangleLattice
