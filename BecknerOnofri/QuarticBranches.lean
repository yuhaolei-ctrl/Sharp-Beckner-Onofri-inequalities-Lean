module

public import BecknerOnofri.Kappa
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-! Exact algebraic part of the reduced branch classification.
These are the actual quartic coefficients in the manuscript. This file does
not assert the analytic reduction or the existence of a PDE branch. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim

def branchQuarticCoefficient (d n : ℕ) : ℝ :=
  (quarticA d + quarticB d / 2 * ((n : ℝ) - 1)) / n

def reducedQuartic (d : ℕ) (δ : ℝ) (r : Fin d → ℝ) : ℝ :=
  δ * (∑ i, r i) + quarticA d * (∑ i, r i ^ 2) +
    quarticB d / 2 * ((∑ i, r i) ^ 2 - ∑ i, r i ^ 2)

theorem quarticA_neg {d : ℕ} (hd : 12 ≤ d) : quarticA d < 0 := by
  have hp : (2 : ℝ) < (2 : ℝ) ^ d := by
    calc
      (2 : ℝ) < (2 : ℝ) ^ (12 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
  unfold quarticA
  have ht : 1 / (4 * ((2 : ℝ) ^ d - 1)) < (1 / 4 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0 < 4 * ((2 : ℝ) ^ d - 1))).mpr
    linarith
  linarith

theorem quarticB_pos {d : ℕ} (hd : 12 ≤ d) : 0 < quarticB d := by
  have hp := five_mul_dimension_le_half_power d hd
  have hd' : (12 : ℝ) ≤ d := by exact_mod_cast hd
  unfold quarticB
  apply div_pos (by norm_num)
  linarith

theorem branchQuarticCoefficient_full {d : ℕ} (hd : 0 < d) :
    branchQuarticCoefficient d d = -kappa d / (2 * (d : ℝ)) := by
  unfold branchQuarticCoefficient kappa
  field_simp
  <;> ring

theorem branchQuarticCoefficient_strictMono {d m n : ℕ} (hd : 12 ≤ d)
    (hm : 0 < m) (hmn : m < n) :
    branchQuarticCoefficient d m < branchQuarticCoefficient d n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_trans hm hmn)
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have ha := quarticA_neg hd
  have hb := quarticB_pos hd
  unfold branchQuarticCoefficient
  apply (div_lt_div_iff₀ hm' hn').mpr
  nlinarith [mul_pos (sub_pos.mpr hmn') (sub_pos.mpr (show quarticA d < quarticB d / 2 by linarith))]

theorem branchQuarticCoefficient_neg {d n : ℕ} (hd : 12 ≤ d)
    (hn : 0 < n) (hnd : n ≤ d) : branchQuarticCoefficient d n < 0 := by
  have hd0 : 0 < d := by omega
  have hfull : branchQuarticCoefficient d d < 0 := by
    rw [branchQuarticCoefficient_full hd0]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (kappa_pos d hd)) (by positivity)
  rcases eq_or_lt_of_le hnd with rfl | hlt
  · exact hfull
  · exact (branchQuarticCoefficient_strictMono hd hn hlt).trans hfull

theorem branch_pressure_strictMono {d m n : ℕ} (hd : 12 ≤ d)
    (hm : 0 < m) (hmn : m < n) (hnd : n ≤ d) :
    -1 / (4 * branchQuarticCoefficient d m) < -1 / (4 * branchQuarticCoefficient d n) := by
  have hqm := branchQuarticCoefficient_neg hd hm (hmn.le.trans hnd)
  have hqn := branchQuarticCoefficient_neg hd (lt_trans hm hmn) hnd
  have hlt := branchQuarticCoefficient_strictMono hd hm hmn
  have he (q : ℝ) : -1 / (4 * q) = 1 / (-4 * q) := by ring
  rw [he, he]
  exact div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)

theorem reducedQuartic_uniform {d : ℕ} (hd : 12 ≤ d) (δ : ℝ) :
    reducedQuartic d δ (fun _ => δ / kappa d) = (d : ℝ) / (2 * kappa d) * δ ^ 2 := by
  have hk := (kappa_pos d hd).ne'
  have he : 2 * quarticA d + ((d : ℝ) - 1) * quarticB d = -kappa d := by
    unfold kappa
    ring
  simp only [reducedQuartic, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  nlinarith [he]

theorem reducedQuartic_coercive {d : ℕ} (hd : 12 ≤ d) (δ : ℝ) (r : Fin d → ℝ) :
    reducedQuartic d δ r ≤ (d : ℝ) / (2 * kappa d) * δ ^ 2 -
      kappa d / 2 * ∑ i, (r i - δ / kappa d) ^ 2 := by
  have hk := (kappa_pos d hd).ne'
  have hb := (quarticB_pos hd).le
  have he : 2 * quarticA d + ((d : ℝ) - 1) * quarticB d = -kappa d := by
    unfold kappa
    ring
  have hCS : (∑ i, r i) ^ 2 ≤ (d : ℝ) * ∑ i, r i ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := r)
  have hss : (∑ i, (r i - δ / kappa d) ^ 2) =
      (∑ i, r i ^ 2) - 2 * (δ / kappa d) * (∑ i, r i) + (d : ℝ) * (δ / kappa d) ^ 2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hbound := mul_le_mul_of_nonneg_left hCS (show 0 ≤ quarticB d / 2 by positivity)
  rw [hss]
  unfold reducedQuartic
  have hδ : kappa d * (δ / kappa d) = δ := mul_div_cancel₀ δ hk
  have htarget : (d : ℝ) / (2 * kappa d) * δ ^ 2 =
      (d : ℝ) * kappa d / 2 * (δ / kappa d) ^ 2 := by field_simp
  rw [htarget]
  nlinarith [congrArg (fun z : ℝ => z * (∑ i, r i ^ 2)) he,
    congrArg (fun z : ℝ => z * (∑ i, r i)) hδ]

theorem reducedQuartic_eq_max_iff {d : ℕ} (hd : 12 ≤ d) (δ : ℝ) (r : Fin d → ℝ) :
    reducedQuartic d δ r = (d : ℝ) / (2 * kappa d) * δ ^ 2 ↔
      r = fun _ => δ / kappa d := by
  constructor
  · intro he
    have h := reducedQuartic_coercive hd δ r
    rw [he] at h
    have hk := kappa_pos d hd
    have hs : 0 ≤ ∑ i, (r i - δ / kappa d) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hz : (∑ i, (r i - δ / kappa d) ^ 2) = 0 := by nlinarith
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (r i - δ / kappa d))).mp
      hz i (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · rintro rfl
    exact reducedQuartic_uniform hd δ

theorem full_branch_pressure_coefficient {d : ℕ} (hd : 12 ≤ d) :
    -1 / (4 * branchQuarticCoefficient d d) = (d : ℝ) / (2 * kappa d) := by
  have hd0 : 0 < d := by omega
  have hdne : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd0).ne'
  have hk := (kappa_pos d hd).ne'
  rw [branchQuarticCoefficient_full hd0]
  field_simp
  <;> norm_num

#print axioms branchQuarticCoefficient_neg
#print axioms branch_pressure_strictMono
#print axioms reducedQuartic_coercive
#print axioms reducedQuartic_eq_max_iff
end BecknerOnofri.HighDim
