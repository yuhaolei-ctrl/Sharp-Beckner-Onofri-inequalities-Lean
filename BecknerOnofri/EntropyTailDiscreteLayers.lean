module

public import BecknerOnofri.EntropyTailAxisFactors
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail.DiscreteLayers

def increment (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | n+1 => f (n+1)-f n

theorem increment_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hm : Monotone f) (n : ℕ) :
    0 ≤ increment f n := by
  cases n with
  | zero => exact hf 0
  | succ n => exact sub_nonneg.mpr (hm (Nat.le_succ n))

theorem sum_increment (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), increment f j = f n := by
  induction n with
  | zero => simp [increment]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, increment]
    ring

theorem cutoff_sum (f : ℕ → ℝ) {M x : ℕ} (hx : x ≤ M) :
    (∑ j ∈ Finset.range (M+1), if j ≤ x then increment f j else 0) = f x := by
  have hsub : Finset.range (x+1) ⊆ Finset.range (M+1) := Finset.range_mono (by omega)
  calc
    _ = ∑ j ∈ Finset.range (x+1), if j ≤ x then increment f j else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro j _ hj
      have hn : ¬ j ≤ x := by
        intro h
        exact hj (Finset.mem_range.mpr (by omega))
      simp only [if_neg hn]
    _ = ∑ j ∈ Finset.range (x+1), increment f j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
    _ = f x := sum_increment f x

theorem finite_expansion (f : ℕ → ℝ) {M x : ℕ} (hx : x ≤ M) :
    (∑ j : Fin (M+1), if (j : ℕ) ≤ x then increment f j else 0) = f x := by
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ x then increment f j else 0)
    (M+1)).trans (cutoff_sum f hx)

/-- A finite layer-cake expansion; no measure-theoretic or probabilistic premise is hidden. -/
theorem product_expansion {d M : ℕ} (f : Fin d → ℕ → ℝ) (x : Fin d → ℕ)
    (hx : ∀ i, x i ≤ M) :
    (∏ i, f i (x i)) =
      ∑ r : Fin d → Fin (M+1), (∏ i, increment (f i) (r i)) *
        (if ∀ i, (r i : ℕ) ≤ x i then 1 else 0) := by
  classical
  calc
    _ = ∏ i, ∑ j : Fin (M+1), if (j : ℕ) ≤ x i then increment (f i) j else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      exact (finite_expansion (f i) (hx i)).symm
    _ = ∑ r : Fin d → Fin (M+1), ∏ i, if (r i : ℕ) ≤ x i then increment (f i) (r i) else 0 :=
      Fintype.prod_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : ∀ i, (r i : ℕ) ≤ x i
      · simp only [if_pos hr, mul_one]
        apply Finset.prod_congr rfl
        intro i _
        rw [if_pos (hr i)]
      · rw [if_neg hr, mul_zero]
        obtain ⟨i, hi⟩ := not_forall.mp hr
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

#print axioms product_expansion
end BecknerOnofri.HighDim.EntropyTail.DiscreteLayers
