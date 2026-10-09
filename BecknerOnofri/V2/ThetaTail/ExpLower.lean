module

public import BecknerOnofri.V2.ThetaTail.SmallG
public import BecknerOnofri.V2.ThetaTail.TailBernstein

@[expose] public section

/-! # The lower bound `∑ d_s e^{-sx} > L(y)` (`d12-tail-eq:expL`)

For `x = 2(1-y)/9`, `y ∈ [0,1]`: `e^{-sx} = e^{-2s/9} e^{(2s/9)y}`; replace `e^{-2s/9}` by
`E_11(2s/9)` (odd Taylor polynomial, `≤ e^{-z}`) and `e^{(2s/9)y}` by its degree-four Taylor
polynomial (nonnegative terms discarded); the five coefficient sums exceed `λ_0..λ_4`
(kernel-checked in `RationalCertificates`). Unconditional. -/
noncomputable section
open Finset
namespace BecknerOnofri.V2.ThetaTail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem expAlt11_nonneg : ∀ s ∈ Finset.Icc (1 : ℕ) 12, 0 ≤ expAlt 11 (2 * (s : ℚ) / 9) := by
  decide +kernel

/-- the five moment sums as reals -/
def Mk (k : ℕ) : ℝ := ((dExpMoment k : ℚ) : ℝ)

theorem tailL_le_dsum {y : ℝ} (hy0 : 0 ≤ y) :
    tailL y ≤ ∑ k ∈ range 5, Mk k * y ^ k := by
  have h0 := ratCast_lt five_checks_0
  have h1 := ratCast_lt five_checks_1
  have h2 := ratCast_lt five_checks_2
  have h3 := ratCast_lt five_checks_3
  have h4 := ratCast_lt five_checks_4
  push_cast at h0 h1 h2 h3 h4
  unfold Mk
  simp only [sum_range_succ, sum_range_zero]
  unfold tailL
  have p1 : 0 ≤ y := hy0
  nlinarith [mul_le_mul_of_nonneg_right h1.le p1, mul_le_mul_of_nonneg_right h2.le (pow_nonneg p1 2),
    mul_le_mul_of_nonneg_right h3.le (pow_nonneg p1 3), mul_le_mul_of_nonneg_right h4.le (pow_nonneg p1 4)]

/-- the exponential sum dominates `L(y)` -/
theorem tailL_le_expSum {x y : ℝ} (hy0 : 0 ≤ y) (hx : x = 2 * (1 - y) / 9) :
    tailL y ≤ ∑ t ∈ Finset.Icc 1 12, dCoeffR t * Real.exp (-x * t) := by
  refine (tailL_le_dsum hy0).trans ?_
  -- termwise lower bounds
  set E : ℕ → ℝ := fun s => ((expAlt 11 (2 * (s : ℚ) / 9) : ℚ) : ℝ) with hE
  set z : ℕ → ℝ := fun s => 2 * (s : ℝ) / 9 with hz
  have hterm : ∀ s ∈ Finset.Icc 1 12, dCoeffR s * (E s * ∑ k ∈ range 5, (z s * y) ^ k / (k.factorial : ℝ))
      ≤ dCoeffR s * Real.exp (-x * s) := by
    intro s hs
    refine mul_le_mul_of_nonneg_left ?_ (dCoeffR_pos hs).le
    have hEn : 0 ≤ E s := by
      exact Rat.cast_nonneg.2 (expAlt11_nonneg s hs)
    have hzn : 0 ≤ z s := by simp only [hz]; positivity
    have hEle : E s ≤ Real.exp (-(z s)) := by
      have := expAlt_le_exp_neg 11 (by decide) (2 * (s : ℚ) / 9) (by positivity)
      simpa [hE, hz] using this
    have hP : ∑ k ∈ range 5, (z s * y) ^ k / (k.factorial : ℝ) ≤ Real.exp (z s * y) :=
      Real.sum_le_exp_of_nonneg (mul_nonneg hzn hy0) 5
    have hPn : 0 ≤ ∑ k ∈ range 5, (z s * y) ^ k / (k.factorial : ℝ) :=
      sum_nonneg fun k _ => by positivity
    have hexp : Real.exp (-x * s) = Real.exp (-(z s)) * Real.exp (z s * y) := by
      rw [← Real.exp_add]; congr 1; simp only [hz]; rw [hx]; ring
    rw [hexp]
    exact mul_le_mul hEle hP hPn (Real.exp_pos _).le
  refine le_trans ?_ (sum_le_sum hterm)
  -- exchange of summations
  have hMk : ∀ k, Mk k = ∑ s ∈ Finset.Icc 1 12,
      dCoeffR s * E s * (z s) ^ k / (k.factorial : ℝ) := by
    intro k
    unfold Mk dExpMoment dCoeffR
    push_cast
    refine sum_congr rfl fun s _ => ?_
    first | (simp only [hE, hz]; done) | (simp only [hE, hz]; push_cast; first | done | ring)
  simp_rw [hMk, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine le_of_eq (sum_congr rfl fun s _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun k _ => ?_
  first | (rw [mul_pow]; done) | (rw [mul_pow]; ring)

end BecknerOnofri.V2.ThetaTail
