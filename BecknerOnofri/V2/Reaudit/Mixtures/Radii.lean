module

public import BecknerOnofri.RandomRectangles

@[expose] public section

/-! # Random rectangles with a prescribed survival function (S037)

The manuscript's proof of `prop:spectral-marginal-energy` draws, for a pair `(N, M)` of mixture
indices, independent radii `R_i` with
`P(R_i = m) = a_{N_i}(m) a_{M_i}(m) - a_{N_i}(m+1) a_{M_i}(m+1)`
and telescopes to `P(R_i ≥ |k_i|) = a_{N_i}(k_i) a_{M_i}(k_i)`.  This file proves the exact
finite statement for an arbitrary antitone survival function `s_i` vanishing beyond `n_i` (the case
`s_i(j) = a_{N_i}(j) a_{M_i}(j)` is `pairSurvival`): the radius law `radiusOf`, the product law
`rectLaw`, the survival identity `rect_survival` and the rectangle decomposition `sum_rect` of a
weighted product sum over the box. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Finset

namespace BecknerOnofri.V2.Reaudit.Mixtures
open BecknerOnofri.RectangleLattice BecknerOnofri.RandomRectangles Legacy.D10

/-- `P(R = r) = s(r) - s(r + 1)`. -/
def radiusOf (s : ℕ → ℝ) (r : ℕ) : ℝ := s r - s (r + 1)

theorem radiusOf_nonneg {s : ℕ → ℝ} (h : Antitone s) (r : ℕ) : 0 ≤ radiusOf s r :=
  sub_nonneg.mpr (h (Nat.le_succ r))

/-- Telescoping: `P(R ≥ j) = s(j)` when `s` vanishes beyond `n`. -/
theorem radius_survival_of_zero {s : ℕ → ℝ} {n : ℕ} (hz : ∀ j, n < j → s j = 0) (j : ℕ) :
    (∑ r ∈ range (n + 1), if j ≤ r then radiusOf s r else 0) = s j := by
  unfold radiusOf
  rw [filtered_telescope]
  by_cases hj : j < n + 1
  · simp [hj, hz (n + 1) (by omega)]
  · simp [hj, hz j (by omega)]

/-- Independent radii: the product law on rectangles. -/
def rectLaw {d : ℕ} (s : Fin d → ℕ → ℝ) (R : Fin d → ℕ) : ℝ := ∏ i, radiusOf (s i) (R i)

theorem rectLaw_nonneg {d : ℕ} {s : Fin d → ℕ → ℝ} (h : ∀ i, Antitone (s i)) (R : Fin d → ℕ) :
    0 ≤ rectLaw s R :=
  prod_nonneg (fun i _ => radiusOf_nonneg (h i) _)

/-- The rectangle-survival identity `P(|k_i| ≤ R_i ∀ i) = ∏ s_i(|k_i|)`. -/
theorem rect_survival {d : ℕ} (s : Fin d → ℕ → ℝ) (n : Fin d → ℕ)
    (hz : ∀ i j, n i < j → s i j = 0) (k : Lattice d) :
    (∑ R ∈ latentBox n, if k ∈ box R then rectLaw s R else 0) = ∏ i, s i (k i).natAbs := by
  have he (R : Fin d → ℕ) :
      (if k ∈ box R then rectLaw s R else 0) =
        ∏ i, if (k i).natAbs ≤ R i then radiusOf (s i) (R i) else 0 := by
    classical
    simp only [mem_box_natAbs]
    by_cases h : ∀ i, (k i).natAbs ≤ R i
    · simp [h, rectLaw]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact (prod_eq_zero (mem_univ i) (if_neg hi)).symm
  simp_rw [he]
  unfold latentBox
  rw [← prod_univ_sum (fun i => range (n i + 1))
    (fun i r => if (k i).natAbs ≤ r then radiusOf (s i) r else 0)]
  exact prod_congr rfl (fun i _ => radius_survival_of_zero (hz i) _)

/-- A weighted sum over the box against a product survival function is an average over random
rectangles. -/
theorem sum_rect {d : ℕ} (s : Fin d → ℕ → ℝ) (n : Fin d → ℕ)
    (hz : ∀ i j, n i < j → s i j = 0) (f : Lattice d → ℝ) :
    (∑ k ∈ box n, f k * ∏ i, s i (k i).natAbs) =
      ∑ R ∈ latentBox n, rectLaw s R * (∑ k ∈ box R, f k) := by
  classical
  simp_rw [← rect_survival s n hz, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro R hR
  have hsub := rectangle_subset hR
  have hfilter : (box n).filter (fun k => k ∈ box R) = box R := by
    ext k
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun hk => hsub hk
  calc
    _ = rectLaw s R * (∑ k ∈ box n, if k ∈ box R then f k else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      split_ifs <;> ring
    _ = _ := by rw [← sum_filter, hfilter, mul_sum]

/-- The survival function of a pair of indices `(n, m)` in coordinate `i`:
`s_i(j) = a_{n_i}(j) a_{m_i}(j)` (the radii of the manuscript). -/
def pairSurvival {d : ℕ} (n m : Fin d → ℕ) (i : Fin d) (j : ℕ) : ℝ :=
  binomialCoeffReal (n i) j * binomialCoeffReal (m i) j

theorem pairSurvival_antitone {d : ℕ} (n m : Fin d → ℕ) (i : Fin d) :
    Antitone (pairSurvival n m i) := by
  intro j j' hjj'
  unfold pairSurvival
  exact mul_le_mul (coeff_antitone _ hjj') (coeff_antitone _ hjj') (coeff_nonneg _ _)
    (coeff_nonneg _ _)

theorem pairSurvival_zero {d : ℕ} (n m : Fin d → ℕ) (i : Fin d) (j : ℕ) (hj : n i < j) :
    pairSurvival n m i j = 0 := by
  unfold pairSurvival
  rw [coeff_eq_zero hj, zero_mul]

theorem componentCoeff_mul {d : ℕ} (n m : Fin d → ℕ) (k : Lattice d) :
    componentCoeff n k * componentCoeff m k = ∏ i, pairSurvival n m i (k i).natAbs := by
  unfold componentCoeff binomialProduct pairSurvival
  rw [← prod_mul_distrib]

#print axioms rect_survival
#print axioms sum_rect

end BecknerOnofri.V2.Reaudit.Mixtures
