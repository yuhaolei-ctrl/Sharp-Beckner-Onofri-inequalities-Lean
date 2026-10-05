import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! The unconditional rational base bound in the one-dimensional spectral slice estimate. -/

noncomputable section
open MeasureTheory Set

namespace BecknerOnofri.HighDim

theorem inverse_twelfth_summable (N : ℕ) :
    Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) ^ 12)⁻¹) := by
  exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 12)⁻¹) N).mpr
    (Real.summable_nat_pow_inv.mpr (by norm_num))

theorem inverse_twelfth_tail_from_three :
    (∑' n : ℕ, (((n + 3 : ℕ) : ℝ) ^ 12)⁻¹) ≤ 1 / (11 * (2 : ℝ) ^ 11) := by
  have ha : AntitoneOn (fun x : ℝ => x ^ (-12 : ℝ)) (Ici (2 : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx) hxy (by norm_num)
  have hi : IntegrableOn (fun x : ℝ => x ^ (-12 : ℝ)) (Ioi (2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h := AntitoneOn.tsum_comp_add_le_integral 2 ha hi
    (fun x hx => Real.rpow_nonneg
      (le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hx)) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)] at h
  norm_num [Real.rpow_neg, Real.rpow_natCast, add_assoc] at h ⊢
  exact h

theorem inverse_twelfth_tail_from_two :
    (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ 12)⁻¹) ≤
      ((2 : ℝ) ^ 12)⁻¹ + 1 / (11 * (2 : ℝ) ^ 11) := by
  have hs : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ 12)⁻¹) :=
    inverse_twelfth_summable 2
  rw [hs.tsum_eq_zero_add]
  change ((2 : ℝ) ^ 12)⁻¹ + (∑' n : ℕ, (((n + 3 : ℕ) : ℝ) ^ 12)⁻¹) ≤ _
  simpa only [add_comm] using
    add_le_add_left inverse_twelfth_tail_from_three (((2 : ℝ) ^ 12)⁻¹)

def spectralSliceBaseTerm (n : ℕ) : ℝ := ((1 + (n : ℝ) ^ 2 / 2) ^ 6)⁻¹

theorem spectralSliceBaseTerm_le {n : ℕ} (hn : 0 < n) :
    spectralSliceBaseTerm n ≤ 64 * ((n : ℝ) ^ 12)⁻¹ := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold spectralSliceBaseTerm
  calc
    ((1 + (n : ℝ) ^ 2 / 2) ^ 6)⁻¹ ≤ (((n : ℝ) ^ 2 / 2) ^ 6)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 6)
    _ = 64 * ((n : ℝ) ^ 12)⁻¹ := by
      rw [div_pow, ← pow_mul]
      norm_num
      ring

theorem spectralSliceBaseTerm_summable (N : ℕ) (hN : 0 < N) :
    Summable (fun n : ℕ => spectralSliceBaseTerm (n + N)) := by
  have hs : Summable (fun n : ℕ => (((n + N : ℕ) : ℝ) ^ 12)⁻¹) :=
    inverse_twelfth_summable N
  apply Summable.of_nonneg_of_le (fun n => by unfold spectralSliceBaseTerm; positivity)
    (fun n => spectralSliceBaseTerm_le (by omega)) (hs.mul_left 64)

theorem spectralSliceBaseTerm_tail_bound :
    (∑' n : ℕ, spectralSliceBaseTerm (n + 2)) ≤
      64 * (((2 : ℝ) ^ 12)⁻¹ + 1 / (11 * (2 : ℝ) ^ 11)) := by
  have hs : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ 12)⁻¹) :=
    inverse_twelfth_summable 2
  calc
    (∑' n : ℕ, spectralSliceBaseTerm (n + 2)) ≤
        ∑' n : ℕ, 64 * (((n + 2 : ℕ) : ℝ) ^ 12)⁻¹ :=
      (spectralSliceBaseTerm_summable 2 (by norm_num)).tsum_le_tsum
        (fun n => spectralSliceBaseTerm_le (by omega)) (hs.mul_left 64)
    _ = 64 * ∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ 12)⁻¹ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left inverse_twelfth_tail_from_two (by norm_num)

theorem spectral_slice_base_bound :
    (3 / 4 : ℝ) * (1 + 2 * ∑' n : ℕ, spectralSliceBaseTerm (n + 1)) ≤
      311141 / 342144 := by
  have hs := spectralSliceBaseTerm_summable 1 (by norm_num)
  have hsplit := hs.tsum_eq_zero_add
  have htail := spectralSliceBaseTerm_tail_bound
  simp only [zero_add, Nat.add_assoc] at hsplit
  norm_num [spectralSliceBaseTerm] at hsplit
  unfold spectralSliceBaseTerm at htail ⊢
  norm_num at htail
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith

theorem spectral_slice_base_bound_lt_one : (311141 / 342144 : ℝ) < 1 := by norm_num

theorem spectral_slice_base_rpow_bound :
    (3 / 4 : ℝ) * (1 + 2 * ∑' n : ℕ,
      (1 + (((n + 1 : ℕ) : ℝ) ^ 2) / 2) ^ (-6 : ℝ)) ≤ 311141 / 342144 := by
  simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, spectralSliceBaseTerm] using
    spectral_slice_base_bound

end BecknerOnofri.HighDim
