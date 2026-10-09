module

public import BecknerOnofri.V2.ThetaTail.Defs
public import BecknerOnofri.V2.ThetaTail.LogBridge

@[expose] public section

/-! # The harmonic lower bound `H_n > log(n+1/2) + 577/1000` (`d12-tail-eq:harmonic`)

Written route: `D_n = H_n − log(n+1/2)` decreases (midpoint inequality), `E_m = H_m − log m −
1/(2m)` increases (trapezoid inequality), and `D_m ≥ E_m`; the finite bounds `H_20`, `log 20`
(rational certificates) give `E_20 > 577/1000`.  The limit `γ` is not needed: for `n ≥ 1` and
`m = max(n,20)`, `D_n ≥ D_m ≥ E_m ≥ E_20`. -/
noncomputable section
open Finset Filter
namespace BecknerOnofri.V2.ThetaTail

lemma log_one_add_inv_ge {a : ℝ} (ha : 0 < a) : 2 / (2 * a + 1) ≤ Real.log (1 + a⁻¹) := by
  have h := Real.hasSum_log_one_add_inv ha
  have h0 := h.summable.sum_le_tsum (range 1) (fun k _ => by positivity)
  rw [h.tsum_eq] at h0
  simp at h0
  rw [div_eq_mul_inv]; exact h0

lemma log_one_add_inv_le {a : ℝ} (ha : 0 < a) :
    Real.log (1 + a⁻¹) ≤ 2 * (1 / (2 * a + 1)) / (1 - (1 / (2 * a + 1)) ^ 2) := by
  set t : ℝ := 1 / (2 * a + 1) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one (by positivity)]; linarith
  have h := Real.hasSum_log_one_add_inv ha
  have hg : HasSum (fun k : ℕ => 2 * t * (t ^ 2) ^ k) (2 * t / (1 - t ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (sq_nonneg t) (by nlinarith : t ^ 2 < 1)).mul_left (2 * t)
    simpa [div_eq_mul_inv] using this
  refine hasSum_le (fun k => ?_) h hg |>.trans_eq' rfl
  have : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  calc 2 * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1) ≤ 2 * 1 * t ^ (2 * k + 1) := by gcongr
    _ = 2 * t * (t ^ 2) ^ k := by rw [pow_succ, pow_mul]; ring

/-- `D_n = H_n − log(n+1/2)` -/
def Dseq (n : ℕ) : ℝ := Hn n - Real.log ((n : ℝ) + 1 / 2)

/-- `E_m = H_m − log m − 1/(2m)` -/
def Eseq (m : ℕ) : ℝ := Hn m - Real.log (m : ℝ) - 1 / (2 * (m : ℝ))

lemma Hn_succ (n : ℕ) : Hn (n + 1) = Hn n + 1 / ((n : ℝ) + 1) := by
  unfold Hn; rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; ring

lemma Dseq_succ_le (n : ℕ) : Dseq (n + 1) ≤ Dseq n := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have h := log_one_add_inv_ge ha
  have e : Real.log (1 + ((n : ℝ) + 1 / 2)⁻¹) = Real.log ((n : ℝ) + 1 + 1 / 2) - Real.log ((n : ℝ) + 1 / 2) := by
    rw [← Real.log_div (by positivity) ha.ne']
    congr 1; field_simp; ring
  rw [e] at h
  have e2 : 2 / (2 * ((n : ℝ) + 1 / 2) + 1) = 1 / ((n : ℝ) + 1) := by field_simp; ring
  rw [e2] at h
  unfold Dseq
  rw [Hn_succ]; push_cast
  linarith

lemma Eseq_le_succ {m : ℕ} (hm : 1 ≤ m) : Eseq m ≤ Eseq (m + 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := log_one_add_inv_le hm0
  have e : Real.log (1 + (m : ℝ)⁻¹) = Real.log ((m : ℝ) + 1) - Real.log m := by
    rw [← Real.log_div (by positivity) hm0.ne']
    congr 1; field_simp
  rw [e] at h
  have e2 : 2 * (1 / (2 * (m : ℝ) + 1)) / (1 - (1 / (2 * (m : ℝ) + 1)) ^ 2)
      = 1 / (2 * (m : ℝ)) + 1 / (2 * ((m : ℝ) + 1)) := by
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    have hm2 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    have h1 : 1 - (1 / (2 * (m : ℝ) + 1)) ^ 2 = 4 * m * (m + 1) / (2 * (m : ℝ) + 1) ^ 2 := by
      field_simp; ring
    rw [h1]
    field_simp
    ring
  rw [e2] at h
  unfold Eseq
  rw [Hn_succ]; push_cast
  have : 1 / (2 * ((m : ℝ) + 1)) = 1 / (2 * ((m : ℝ) + 1)) := rfl
  have e3 : 1 / ((m : ℝ) + 1) = 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * ((m : ℝ) + 1)) := by
    field_simp; ring
  linarith

lemma Eseq_le_Dseq (m : ℕ) (hm : 1 ≤ m) : Eseq m ≤ Dseq m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold Eseq Dseq
  have e : Real.log ((m : ℝ) + 1 / 2) = Real.log m + Real.log (1 + 1 / (2 * (m : ℝ))) := by
    rw [← Real.log_mul hm0.ne' (by positivity)]; congr 1; field_simp
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (2 * (m : ℝ)) by positivity)
  rw [e]; linarith

lemma Eseq_mono {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : Eseq i ≤ Eseq j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih => exact ih.trans (Eseq_le_succ (hi.trans hj))

lemma Dseq_anti {i j : ℕ} (hij : i ≤ j) : Dseq j ≤ Dseq i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih => exact (Dseq_succ_le j).trans ih

lemma Hn_cast20 : Hn 20 = ((harmonicQ 20 : ℚ) : ℝ) := by
  unfold Hn harmonicQ; push_cast; rfl

theorem Eseq_twenty_gt : (577 : ℝ) / 1000 < Eseq 20 := by
  have hH : (3597739 : ℝ) / 10 ^ 6 < Hn 20 := by
    rw [Hn_cast20]
    have := ratCast_lt harmonic20_lower
    push_cast at this ⊢; linarith
  have hl : Real.log 20 < 2995733 / 10 ^ 6 := by
    have e : Real.log 20 = 4 * Real.log 2 + Real.log (5 / 4) := by
      rw [show (20 : ℝ) = 2 ^ 4 * (5 / 4) by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]; norm_num
    have h1 := log_le_logUpper 16 2 (by norm_num)
    have h2 := log_le_logUpper 16 (5 / 4) (by norm_num)
    have h3 := ratCast_lt log20_upper
    push_cast at h1 h2 h3 ⊢
    rw [e]; linarith
  have hg := ratCast_lt gamma_lower
  push_cast at hg
  unfold Eseq
  push_cast
  linarith

/-- `H_n > log(n+1/2) + 577/1000` for `n ≥ 1` -/
theorem Hn_gt (n : ℕ) (hn : 1 ≤ n) : Real.log ((n : ℝ) + 1 / 2) + 577 / 1000 < Hn n := by
  set m := max n 20 with hm
  have h1 : Dseq m ≤ Dseq n := Dseq_anti (le_max_left _ _)
  have h2 : Eseq m ≤ Dseq m := Eseq_le_Dseq m (by omega)
  have h3 : Eseq 20 ≤ Eseq m := Eseq_mono (by norm_num) (le_max_right _ _)
  have := Eseq_twenty_gt
  unfold Dseq at h1 h2
  linarith

end BecknerOnofri.V2.ThetaTail
