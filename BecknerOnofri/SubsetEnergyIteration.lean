module

public import BecknerOnofri.SubsetDeletionCounting
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Data.ENNReal.Operations

@[expose] public section

/-! Finite-subset induction of a nonnegative marginal-energy inequality.
All sums and products allow infinite energy. -/
noncomputable section
open Finset
open scoped BigOperators ENNReal
namespace BecknerOnofri

theorem subset_energy_iteration {α : Type*} [DecidableEq α]
    (E : Finset α → ℝ≥0∞) (r : ℕ) (hr : 1 ≤ r)
    (hstep : ∀ s : Finset α, r < s.card →
      ((s.card-1:ℕ):ℝ≥0∞) * E s ≤ ∑ i ∈ s, E (s.erase i))
    (s : Finset α) (hrs : r ≤ s.card) :
    (((s.card-1).choose (r-1):ℕ):ℝ≥0∞) * E s ≤ ∑ t ∈ s.powersetCard r, E t := by
  revert hrs
  refine s.strongInductionOn ?_
  intro s ih hrs
  by_cases he : s.card = r
  · subst r
    simp
  have hlt : r < s.card := by omega
  have hs2 : 2 ≤ s.card := by omega
  have hn : s.card-2+1 = s.card-1 := by omega
  have hdiff : s.card-1-(r-1) = s.card-r := by omega
  have hcomb : (s.card-2).choose (r-1) * (s.card-1) =
      (s.card-1).choose (r-1) * (s.card-r) := by
    simpa only [hn, hdiff] using Nat.choose_mul_succ_eq (s.card-2) (r-1)
  have hcast : (((s.card-2).choose (r-1):ℕ):ℝ≥0∞) * ((s.card-1:ℕ):ℝ≥0∞) =
      (((s.card-1).choose (r-1):ℕ):ℝ≥0∞) * ((s.card-r:ℕ):ℝ≥0∞) := by
    exact_mod_cast hcomb
  have hb : ((s.card-r:ℕ):ℝ≥0∞) *
      ((((s.card-1).choose (r-1):ℕ):ℝ≥0∞) * E s) ≤
      ((s.card-r:ℕ):ℝ≥0∞) * ∑ t ∈ s.powersetCard r, E t := by
    calc
      _ = (((s.card-2).choose (r-1):ℕ):ℝ≥0∞) *
          (((s.card-1:ℕ):ℝ≥0∞) * E s) := by
          rw [← mul_assoc, ← mul_assoc, hcast]
          ac_rfl
      _ ≤ (((s.card-2).choose (r-1):ℕ):ℝ≥0∞) * ∑ i ∈ s, E (s.erase i) :=
        mul_le_mul_right (hstep s hlt) _
      _ = ∑ i ∈ s, (((s.card-2).choose (r-1):ℕ):ℝ≥0∞) * E (s.erase i) := by rw [mul_sum]
      _ ≤ ∑ i ∈ s, ∑ t ∈ (s.erase i).powersetCard r, E t := by
        apply sum_le_sum
        intro i hi
        have hcard := card_erase_of_mem hi
        have hsub := erase_ssubset hi
        have h := ih (s.erase i) hsub (by omega : r ≤ (s.erase i).card)
        simpa only [hcard, Nat.sub_sub, show 1+1=2 from rfl] using h
      _ = _ := by rw [sum_erase_powersetCard, nsmul_eq_mul]
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast (by omega : s.card-r ≠ 0))
    (by simp)).mp hb

#print axioms subset_energy_iteration
end BecknerOnofri
