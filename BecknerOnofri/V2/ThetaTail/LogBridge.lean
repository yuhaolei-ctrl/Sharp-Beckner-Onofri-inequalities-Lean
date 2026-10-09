module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import BecknerOnofri.V2.ThetaTail.RationalCertificates

@[expose] public section

/-! # Real-analytic soundness of the logarithm certificates (Appendix B.1)

`ℓ_M(a) ≤ log a ≤ u_M(a)` for rational `a ≥ 1`, with `ℓ_M`, `u_M` the definitions
`logLower`, `logUpper` of `RationalCertificates`.  This is the "positive logarithmic series"
sentence of Appendix B.1. -/
noncomputable section
open Finset Filter
namespace BecknerOnofri.V2.ThetaTail

lemma ratCast_lt {a b : ℚ} (h : a < b) : (a : ℝ) < (b : ℝ) := Rat.cast_lt.2 h

/-- `ℓ_M`-type lower bound in real form: partial sums of the `artanh` series. -/
theorem sum_le_log_ratio {z : ℝ} (h0 : 0 ≤ z) (h1 : z < 1) (n : ℕ) :
    2 * ∑ k ∈ range n, z ^ (2 * k + 1) / (2 * k + 1) ≤ Real.log ((1 + z) / (1 - z)) := by
  have := Real.sum_range_le_log_div h0 h1 n
  linarith

/-- the upper bound `log((1+z)/(1-z)) ≤ ℓ + 2 z^{2M+3}/((2M+3)(1-z²))`. -/
theorem log_ratio_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z < 1) (M : ℕ) :
    Real.log ((1 + z) / (1 - z)) ≤
      2 * ∑ k ∈ range (M + 1), z ^ (2 * k + 1) / (2 * k + 1)
        + 2 * z ^ (2 * M + 3) / ((2 * M + 3) * (1 - z ^ 2)) := by
  have habs : |z| < 1 := by rwa [abs_of_nonneg h0]
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hlog : Real.log ((1 + z) / (1 - z)) = Real.log (1 + z) - Real.log (1 - z) :=
    Real.log_div (by linarith) (by linarith)
  rw [hlog]
  have hsum := hs.summable
  have hsplit := hsum.sum_add_tsum_nat_add (M + 1)
  rw [hs.tsum_eq] at hsplit
  -- tail bound
  have hgeo : HasSum (fun i : ℕ => z ^ (2 * (i + (M + 1)) + 1)) (z ^ (2 * M + 3) / (1 - z ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (sq_nonneg z) hz2).mul_left (z ^ (2 * M + 3))
    convert this using 1
    · ext i
      rw [show 2 * (i + (M + 1)) + 1 = 2 * M + 3 + 2 * i by ring, pow_add, pow_mul]
    · rw [div_eq_mul_inv]
  have hT : ∑' i : ℕ, (2 : ℝ) * (1 / (2 * ((i + (M + 1) : ℕ) : ℝ) + 1)) * z ^ (2 * (i + (M + 1)) + 1)
      ≤ 2 / (2 * M + 3) * (z ^ (2 * M + 3) / (1 - z ^ 2)) := by
    rw [← hgeo.tsum_eq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_) ((hsum.comp_injective (add_left_injective (M + 1)))) (hgeo.summable.mul_left _)
    have hpos : 0 ≤ z ^ (2 * (i + (M + 1)) + 1) := pow_nonneg h0 _
    have : (1 : ℝ) / (2 * ((i + (M + 1) : ℕ) : ℝ) + 1) ≤ 1 / (2 * M + 3) := by
      apply one_div_le_one_div_of_le
      · positivity
      · push_cast; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    calc (2 : ℝ) * (1 / (2 * ((i + (M + 1) : ℕ) : ℝ) + 1)) * z ^ (2 * (i + (M + 1)) + 1)
        ≤ 2 * (1 / (2 * M + 3)) * z ^ (2 * (i + (M + 1)) + 1) := by gcongr
      _ = _ := by ring
  have hfin : ∑ i ∈ range (M + 1), (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * z ^ (2 * i + 1)
      = 2 * ∑ k ∈ range (M + 1), z ^ (2 * k + 1) / (2 * k + 1) := by
    rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; ring
  have key : Real.log (1 + z) - Real.log (1 - z) =
      ∑ i ∈ range (M + 1), (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * z ^ (2 * i + 1)
      + ∑' i : ℕ, (2 : ℝ) * (1 / (2 * ((i + (M + 1) : ℕ) : ℝ) + 1)) * z ^ (2 * (i + (M + 1)) + 1) :=
    hsplit.symm
  rw [key, hfin]
  have : 2 / (2 * (M : ℝ) + 3) * (z ^ (2 * M + 3) / (1 - z ^ 2))
      = 2 * z ^ (2 * M + 3) / ((2 * M + 3) * (1 - z ^ 2)) := by
    have h3 : (1 - z ^ 2) ≠ 0 := by linarith
    have h4 : (2 * (M : ℝ) + 3) ≠ 0 := by positivity
    field_simp
  linarith

lemma logZ_nonneg (a : ℚ) (ha : 1 ≤ a) : (0 : ℝ) ≤ ((logZ a : ℚ) : ℝ) := by
  have : (0 : ℚ) ≤ logZ a := div_nonneg (by linarith) (by linarith)
  exact_mod_cast this

lemma logZ_lt_one (a : ℚ) (ha : 1 ≤ a) : ((logZ a : ℚ) : ℝ) < 1 := by
  have : logZ a < 1 := by
    unfold logZ
    rw [div_lt_one (by linarith)]; linarith
  exact_mod_cast this

lemma ratio_logZ (a : ℚ) (ha : 1 ≤ a) :
    (1 + ((logZ a : ℚ) : ℝ)) / (1 - ((logZ a : ℚ) : ℝ)) = (a : ℝ) := by
  have h1 : (a : ℝ) + 1 ≠ 0 := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  unfold logZ
  push_cast
  field_simp
  ring

theorem logLower_le_log (M : ℕ) (a : ℚ) (ha : 1 ≤ a) :
    ((logLower M a : ℚ) : ℝ) ≤ Real.log (a : ℝ) := by
  have h := sum_le_log_ratio (logZ_nonneg a ha) (logZ_lt_one a ha) (M + 1)
  rw [ratio_logZ a ha] at h
  unfold logLower
  push_cast
  exact h

theorem log_le_logUpper (M : ℕ) (a : ℚ) (ha : 1 ≤ a) :
    Real.log (a : ℝ) ≤ ((logUpper M a : ℚ) : ℝ) := by
  have h := log_ratio_le (logZ_nonneg a ha) (logZ_lt_one a ha) M
  rw [ratio_logZ a ha] at h
  unfold logUpper logLower
  push_cast
  exact h

end BecknerOnofri.V2.ThetaTail
