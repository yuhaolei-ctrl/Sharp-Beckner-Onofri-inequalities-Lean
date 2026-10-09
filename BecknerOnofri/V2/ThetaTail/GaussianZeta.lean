module

public import BecknerOnofri.V2.ThetaTail.GaussianLambert
public import BecknerOnofri.V2.ThetaTail.SinhLog

@[expose] public section

/-! # `(d12-tail-eq:Glog)` and `(d12-tail-eq:Gzeta)`

Lambert -> logarithm conversion with the signs of the source, then the sinh-product bounds
summed against `k^{-6}`.  HONESTLY CONDITIONAL on `TwelveSquareIdentity`:

`G_le_Phi_of_twelveSquare`:
`G(η) ≤ (63/8) ζ(6) log(1/η) + c₀ + (15/4) ζ(5) η − (1/4) ζ(4) η² + (1/360) ζ(2) η⁴ − ∑ d_s e^{-sη}`
with `c₀ = (log 4/8) ζ(6) − (63/8) Λ`, `Λ = ∑ log k / k⁶ = −ζ'(6)`.
(`ζ(p)` is the real series `zetaR p`; Mathlib's `riemannZeta` is not needed.) -/
noncomputable section
open Finset Filter Topology
namespace BecknerOnofri.V2.ThetaTail

/-- `Λ = ∑_{k≥1} log k / k⁶ = −ζ'(6)` -/
def zetaLog : ℝ := ∑' n : ℕ, Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ 6

lemma summable_zetaLog : Summable (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ 6) := by
  have h5 := summable_zetaTerm (p := 5) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h5
  · exact div_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
      (by positivity)
  · have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hl : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have := Real.log_le_sub_one_of_pos hk; linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc Real.log ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ 5 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ 5 :=
          mul_le_mul_of_nonneg_right hl (by positivity)
      _ = 1 * ((n : ℝ) + 1) ^ 6 := by ring

lemma zetaLog_nonneg : 0 ≤ zetaLog :=
  tsum_nonneg fun n => div_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    (by positivity)

/-- the summand `-log(1-e^{-kη})/k⁶` (indexed by `n = k-1`) -/
def negLogTerm (η : ℝ) (n : ℕ) : ℝ :=
  (-Real.log (1 - Real.exp (-(((n : ℝ) + 1) * η)))) / ((n : ℝ) + 1) ^ 6

lemma summable_negLogTerm {η : ℝ} (hη : 0 < η) : Summable (negLogTerm η) := by
  have h := summable_neg_log_terms (x := Real.exp (-η)) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.2 (by linarith))
  have h' := (summable_pnat_iff_summable_succ
    (f := fun k : ℕ => (-Real.log (1 - Real.exp (-η) ^ k)) / (k : ℝ) ^ 6)).1 h
  refine h'.congr fun n => ?_
  unfold negLogTerm
  rw [← Real.exp_nat_mul]
  push_cast
  congr 4
  ring

lemma lambertSum_eq_tsum {η : ℝ} (hη : 0 < η) :
    lambertSum (Real.exp (-η)) = ∑' n : ℕ, negLogTerm η n := by
  unfold lambertSum sigma5
  rw [tsum_lambert_log (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by linarith))]
  rw [tsum_pnat_eq_tsum_succ (f := fun k : ℕ => (-Real.log (1 - Real.exp (-η) ^ k)) / (k : ℝ) ^ 6)]
  refine tsum_congr fun n => ?_
  unfold negLogTerm
  rw [← Real.exp_nat_mul]
  push_cast
  congr 4
  ring

/-- the bounding series for the first sum -/
def r1 (η : ℝ) (n : ℕ) : ℝ :=
  (-Real.log (((n : ℝ) + 1) * η) + ((n : ℝ) + 1) * η / 2 - (((n : ℝ) + 1) * η) ^ 2 / 24
    + (((n : ℝ) + 1) * η) ^ 4 / 2880) / ((n : ℝ) + 1) ^ 6

/-- the bounding series for the second sum -/
def r2 (η : ℝ) (n : ℕ) : ℝ :=
  (Real.log (4 * (((n : ℝ) + 1) * η)) - 2 * (((n : ℝ) + 1) * η)
    + 2 * (((n : ℝ) + 1) * η) ^ 2 / 3) / ((n : ℝ) + 1) ^ 6

lemma hasSum_r1 {η : ℝ} (hη : 0 < η) :
    HasSum (r1 η) (-zetaLog - Real.log η * zetaR 6 + η / 2 * zetaR 5 - η ^ 2 / 24 * zetaR 4
      + η ^ 4 / 2880 * zetaR 2) := by
  have hL := summable_zetaLog.hasSum
  have h6 := (summable_zetaTerm (p := 6) (by norm_num)).hasSum
  have h5 := (summable_zetaTerm (p := 5) (by norm_num)).hasSum
  have h4 := (summable_zetaTerm (p := 4) (by norm_num)).hasSum
  have h2 := (summable_zetaTerm (p := 2) (by norm_num)).hasSum
  have := ((((hL.neg.sub (h6.mul_left (Real.log η))).add (h5.mul_left (η / 2))).sub
    (h4.mul_left (η ^ 2 / 24))).add (h2.mul_left (η ^ 4 / 2880)))
  convert this using 1
  · ext n
    unfold r1
    have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [Real.log_mul hk.ne' hη.ne']
    field_simp
    ring
  · unfold zetaLog zetaR; ring

lemma hasSum_r2 {η : ℝ} (hη : 0 < η) :
    HasSum (r2 η) (Real.log 4 * zetaR 6 + zetaLog + Real.log η * zetaR 6 - 2 * η * zetaR 5
      + 2 * η ^ 2 / 3 * zetaR 4) := by
  have hL := summable_zetaLog.hasSum
  have h6 := (summable_zetaTerm (p := 6) (by norm_num)).hasSum
  have h5 := (summable_zetaTerm (p := 5) (by norm_num)).hasSum
  have h4 := (summable_zetaTerm (p := 4) (by norm_num)).hasSum
  have := ((((h6.mul_left (Real.log 4)).add hL).add (h6.mul_left (Real.log η))).sub
    (h5.mul_left (2 * η))).add (h4.mul_left (2 * η ^ 2 / 3))
  convert this using 1
  · ext n
    unfold r2
    have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hk.ne' hη.ne']
    field_simp
    ring
  · unfold zetaLog zetaR; ring

lemma negLogTerm_le_r1 {η : ℝ} (hη : 0 < η) (n : ℕ) : negLogTerm η n ≤ r1 η n := by
  unfold negLogTerm r1
  have hk : (0 : ℝ) < ((n : ℝ) + 1) * η := by positivity
  exact div_le_div_of_nonneg_right (neg_log_one_sub_exp_neg_le _ hk) (by positivity)

lemma neg_negLogTerm_four_le_r2 {η : ℝ} (hη : 0 < η) (n : ℕ) :
    -negLogTerm (4 * η) n ≤ r2 η n := by
  unfold negLogTerm r2
  have hk : (0 : ℝ) < ((n : ℝ) + 1) * η := by positivity
  have h := log_one_sub_exp_neg_four_le _ hk
  have e : ((n : ℝ) + 1) * (4 * η) = 4 * (((n : ℝ) + 1) * η) := by ring
  rw [e, neg_div, neg_neg]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- `(d12-tail-eq:Gzeta)`, conditional on the twelve-square identity. -/
theorem G_le_Phi_of_twelveSquare (hT : TwelveSquareIdentity) {η : ℝ} (hη : 0 < η) :
    G η ≤ 63 / 8 * zetaR 6 * (-Real.log η) + (Real.log 4 / 8 * zetaR 6 - 63 / 8 * zetaLog)
      + 15 / 4 * zetaR 5 * η - 1 / 4 * zetaR 4 * η ^ 2 + 1 / 360 * zetaR 2 * η ^ 4
      - ∑ t ∈ Finset.Icc 1 12, dCoeffR t * Real.exp (-η * t) := by
  have h := G_le_lambert_of_twelveSquare hT hη
  rw [lambertSum_eq_tsum hη, lambertSum_eq_tsum (by linarith : 0 < 4 * η)] at h
  have hS1 := hasSum_le (negLogTerm_le_r1 hη) (summable_negLogTerm hη).hasSum (hasSum_r1 hη)
  have hS2 := hasSum_le (fun n => neg_negLogTerm_four_le_r2 hη n)
    (summable_negLogTerm (by linarith : 0 < 4 * η)).hasSum.neg (hasSum_r2 hη)
  nlinarith [h, hS1, hS2]

end BecknerOnofri.V2.ThetaTail
