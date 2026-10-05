import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

/-!
Finite combinatorics for the rectangular Fourier-lattice comparison.
The three-symbol bound is proved by counting actual ternary words.
-/

open scoped BigOperators
open Finset

namespace BecknerOnofri.RectangleCombinatorics

abbrev Word (d : ℕ) := Fin d → Fin 3

def avoidSupport {d : ℕ} (w : Word d) (a : Fin 3) : Finset (Fin d) :=
  univ.filter (fun i => w i ≠ a)

def largeWords (d : ℕ) (a : Fin 3) : Finset (Word d) :=
  univ.filter (fun w => 2 * d < 3 * (avoidSupport w a).card)

def largeSymbols {d : ℕ} (w : Word d) : Finset (Fin 3) :=
  univ.filter (fun a => 2 * d < 3 * (avoidSupport w a).card)

theorem support_fiber_eq_pi {d : ℕ} (a : Fin 3) (s : Finset (Fin d)) :
    (univ.filter (fun w : Word d => avoidSupport w a = s)) =
      Fintype.piFinset (fun i => if i ∈ s then univ.erase a else {a}) := by
  ext w
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro h i
    have hi := Finset.ext_iff.mp h i
    by_cases his : i ∈ s
    · have hn : w i ≠ a := by simpa [avoidSupport] using hi.mpr his
      simp [his, hn]
    · have he : w i = a := by
        by_contra hn
        exact his (hi.mp (by simp [avoidSupport, hn]))
      simp [his, he]
  · intro h
    ext i
    have hi := h i
    by_cases his : i ∈ s
    · simp only [his, if_true, mem_erase, mem_univ, and_true] at hi
      simp [avoidSupport, his, hi]
    · simp only [his, if_false, mem_singleton] at hi
      simp [avoidSupport, his, hi]

theorem support_fiber_card {d : ℕ} (a : Fin 3) (s : Finset (Fin d)) :
    (univ.filter (fun w : Word d => avoidSupport w a = s)).card = 2 ^ s.card := by
  rw [support_fiber_eq_pi, Fintype.card_piFinset]
  have hcard (i : Fin d) :
      (if i ∈ s then (univ : Finset (Fin 3)).erase a else {a}).card =
        if i ∈ s then 2 else 1 := by
    split_ifs <;> simp
  simp_rw [hcard]
  simp

theorem sum_avoidSupport_card {d : ℕ} (w : Word d) :
    ∑ a : Fin 3, (avoidSupport w a).card = 2 * d := by
  simp only [avoidSupport, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have hinner (i : Fin d) : (∑ a : Fin 3, if w i ≠ a then 1 else 0) = (2 : ℕ) := by
    generalize w i = a
    fin_cases a <;> decide
  simp_rw [hinner]
  simp [mul_comm]

theorem largeSymbols_card_le_two {d : ℕ} (w : Word d) : (largeSymbols w).card ≤ 2 := by
  by_contra hh
  have htotal : (largeSymbols w).card ≤ 3 := by
    simpa [largeSymbols] using
      (card_le_card (filter_subset (fun a => 2*d < 3*(avoidSupport w a).card) univ))
  have he : largeSymbols w = univ := by
    apply Finset.eq_of_subset_of_card_le (filter_subset _ _)
    change 3 ≤ (largeSymbols w).card
    omega
  have h (a : Fin 3) : 2 * d < 3 * (avoidSupport w a).card := by
    have ha : a ∈ largeSymbols w := by rw [he]; exact mem_univ _
    exact (mem_filter.mp ha).2
  have hs := sum_avoidSupport_card w
  simp only [Fin.sum_univ_three] at hs
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  omega

def relabel {d : ℕ} (a : Fin 3) : Word d ≃ Word d :=
  Equiv.piCongrRight (fun _ => Equiv.swap 0 a)

theorem relabel_support {d : ℕ} (a : Fin 3) (w : Word d) :
    avoidSupport (relabel a w) a = avoidSupport w 0 := by
  ext i
  simp only [avoidSupport, mem_filter, mem_univ, true_and]
  change Equiv.swap 0 a (w i) ≠ a ↔ w i ≠ 0
  have he : Equiv.swap 0 a (w i) = a ↔ w i = 0 := by
    constructor
    · intro h
      exact (Equiv.swap 0 a).injective (h.trans (Equiv.swap_apply_left 0 a).symm)
    · intro h
      rw [h, Equiv.swap_apply_left]
  exact not_congr he

theorem largeWords_card_eq (d : ℕ) (a : Fin 3) :
    (largeWords d 0).card = (largeWords d a).card := by
  apply Finset.card_equiv (relabel a)
  intro w
  simp [largeWords, relabel_support]

theorem three_mul_largeWords_le (d : ℕ) :
    3 * (largeWords d 0).card ≤ 2 * 3 ^ d := by
  calc
    3 * (largeWords d 0).card = ∑ a : Fin 3, (largeWords d a).card := by
      simp_rw [← largeWords_card_eq d]
      simp
    _ = ∑ w : Word d, (largeSymbols w).card := by
      simp only [largeWords, largeSymbols, card_eq_sum_ones, sum_filter]
      exact sum_comm
    _ ≤ ∑ _w : Word d, 2 := sum_le_sum (fun w _ => largeSymbols_card_le_two w)
    _ = 2 * 3 ^ d := by simp [Word, mul_comm]

/-- Partition ternary words by the positions not occupied by zero. -/
theorem largeWords_card_eq_sum_supports (d : ℕ) :
    (largeWords d 0).card =
      ∑ s : Finset (Fin d), if 2 * d < 3 * s.card then 2 ^ s.card else 0 := by
  have hf := Finset.sum_card_fiberwise_eq_card_filter
    (univ : Finset (Word d))
    ((univ : Finset (Finset (Fin d))).filter (fun s => 2 * d < 3 * s.card))
    (fun w => avoidSupport w 0)
  have hcount : (largeWords d 0).card =
      ∑ s ∈ (univ : Finset (Finset (Fin d))).filter (fun s => 2 * d < 3 * s.card),
        (univ.filter (fun w : Word d => avoidSupport w 0 = s)).card := by
    simpa [largeWords] using hf.symm
  rw [hcount]
  simp_rw [support_fiber_card]
  exact sum_filter _ _

/-- Counting supports and the two choices at every supported position gives
the exact binomial expression, without any probabilistic assumptions. -/
theorem largeWords_card_eq_binomial_tail (d : ℕ) :
    (largeWords d 0).card =
      ∑ j ∈ (range (d + 1)).filter (fun j => 2 * d < 3 * j),
        2 ^ j * d.choose j := by
  rw [largeWords_card_eq_sum_supports]
  calc
    (∑ s : Finset (Fin d), if 2 * d < 3 * s.card then 2 ^ s.card else 0) =
        ∑ s ∈ (univ : Finset (Fin d)).powerset,
          if 2 * d < 3 * s.card then 2 ^ s.card else 0 := by simp
    _ = ∑ j ∈ range (d + 1),
        d.choose j * (if 2 * d < 3 * j then 2 ^ j else 0) := by
      rw [Finset.sum_powerset]
      have hs (j : ℕ) :
          (∑ s ∈ (univ : Finset (Fin d)).powersetCard j,
            if 2 * d < 3 * s.card then 2 ^ s.card else 0) =
              d.choose j * (if 2 * d < 3 * j then 2 ^ j else 0) := by
        simpa using Finset.sum_powersetCard j (univ : Finset (Fin d))
          (fun n => if 2 * d < 3 * n then (2 : ℕ) ^ n else 0)
      simp_rw [hs]
      simp
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j hj
      split_ifs <;> simp [mul_comm]

/-- Equation `spectral-three-symbol-count` in exact integer arithmetic. -/
theorem three_symbol_count_nat (d : ℕ) :
    3 * (∑ j ∈ (range (d + 1)).filter (fun j => 2 * d < 3 * j),
      2 ^ j * d.choose j) ≤ 2 * 3 ^ d := by
  rw [← largeWords_card_eq_binomial_tail]
  exact three_mul_largeWords_le d

/-- The manuscript's three-symbol estimate, as a real-valued inequality. -/
theorem three_symbol_count (d : ℕ) :
    (∑ j ∈ (range (d + 1)).filter (fun j => 2 * d < 3 * j),
      (2 : ℝ) ^ j * (d.choose j : ℝ)) ≤ (2 / 3 : ℝ) * 3 ^ d := by
  have h := three_symbol_count_nat d
  have hr : 3 *
      (∑ j ∈ (range (d + 1)).filter (fun j => 2 * d < 3 * j),
        (2 : ℝ) ^ j * (d.choose j : ℝ)) ≤ 2 * (3 : ℝ) ^ d := by
    exact_mod_cast h
  linarith

/-- Exact cancellation identity behind the pair-reserve normalization. -/
theorem binomial_ratio_eq {r j : ℕ} (hj : 2 ≤ j) (hjr : j ≤ r) :
    (r.choose j : ℝ) / (r.choose 2 : ℝ) =
      ((r - 2).choose (j - 2) : ℝ) / (j.choose 2 : ℝ) := by
  have hr : (r.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hj.trans hjr)).ne'
  have hj' : (j.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  apply (div_eq_div_iff hr hj').2
  have he := Nat.choose_mul (n := r) hj
  exact_mod_cast (by simpa [Nat.mul_comm] using he)

/-- The comparison used to dominate every negative cube contribution by
the corresponding contribution of the full d-coordinate cube. -/
theorem binomial_ratio_mono {r d j : ℕ} (hj : 2 ≤ j) (hjr : j ≤ r) (hrd : r ≤ d) :
    (r.choose j : ℝ) / (r.choose 2 : ℝ) ≤
      (d.choose j : ℝ) / (d.choose 2 : ℝ) := by
  rw [binomial_ratio_eq hj hjr, binomial_ratio_eq hj (hjr.trans hrd)]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.choose_le_choose (j - 2) (Nat.sub_le_sub_right hrd 2)
  · positivity

end BecknerOnofri.RectangleCombinatorics
