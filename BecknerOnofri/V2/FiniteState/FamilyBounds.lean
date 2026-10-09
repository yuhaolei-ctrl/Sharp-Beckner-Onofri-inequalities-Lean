module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

@[expose] public section

/-!
# Scalar feasibility facts for the explicit reference family (Lemma 5.19, Appendix A.3)

Compiled (sorry-free).  Pure real-analysis facts about the parameters
`L, λ, a, χ, ω` and the state-zero product; no dependence on the thirteen-state vocabulary.
-/

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState

def famL (t : ℝ) : ℝ := 9 / 2 * t ^ 10
def famLam (t : ℝ) : ℝ := famL t / (1 + famL t)
def famBias (t : ℝ) : ℝ := t - famL t * (1 - t)
def famChi (t : ℝ) : ℝ := 31 / t ^ 2 - 32 + 12 * t ^ 4 + t ^ 2 / (10 * (1 - t))
def famP (u : ℝ) : ℝ := 31 - 32 * u + 12 * u ^ 3
def famOmega (t : ℝ) : ℝ := t ^ 2 * (1 - t) / (famP (t ^ 2) * (1 - t) + t ^ 4 / 10)

/-- Maximum of `t^9 (1-t)` is `9^9/10^10` (at `t = 9/10`): exact factorisation with a double
root and a positive-coefficient cofactor.  Verified by exact rational polynomial division. -/
theorem pow9_mul_one_sub_le {t : ℝ} (ht : 0 ≤ t) : t ^ 9 * (1 - t) ≤ 9 ^ 9 / 10 ^ 10 := by
  have hq : 0 ≤ (4782969 / 100000000 : ℝ) + (531441 / 5000000) * t + (177147 / 1000000) * t ^ 2 +
      (6561 / 25000) * t ^ 3 + (729 / 2000) * t ^ 4 + (243 / 500) * t ^ 5 + (63 / 100) * t ^ 6 +
      (4 / 5) * t ^ 7 + t ^ 8 := by positivity
  have hid : (9 ^ 9 / 10 ^ 10 : ℝ) - t ^ 9 * (1 - t) = (t - 9 / 10) ^ 2 *
      ((4782969 / 100000000 : ℝ) + (531441 / 5000000) * t + (177147 / 1000000) * t ^ 2 +
      (6561 / 25000) * t ^ 3 + (729 / 2000) * t ^ 4 + (243 / 500) * t ^ 5 + (63 / 100) * t ^ 6 +
      (4 / 5) * t ^ 7 + t ^ 8) := by ring
  nlinarith [mul_nonneg (sq_nonneg (t - 9 / 10)) hq]

theorem famL_mul_one_sub_le {t : ℝ} (ht : 0 ≤ t) : famL t * (1 - t) ≤ t / 5 := by
  have h := pow9_mul_one_sub_le ht
  have hc : (9 / 2 : ℝ) * (9 ^ 9 / 10 ^ 10) < 1 / 5 := by norm_num
  have e : famL t * (1 - t) = 9 / 2 * t * (t ^ 9 * (1 - t)) := by unfold famL; ring
  rw [e]
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 9 / 2 * t)
  nlinarith [mul_le_mul_of_nonneg_left hc.le ht]

/-- `4t/5 ≤ a(t) ≤ t` for `0 ≤ t ≤ 1`. -/
theorem famBias_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    4 * t / 5 ≤ famBias t ∧ famBias t ≤ t := by
  have h := famL_mul_one_sub_le ht0
  have hL : 0 ≤ famL t * (1 - t) :=
    mul_nonneg (by unfold famL; positivity) (by linarith)
  unfold famBias
  constructor <;> linarith

/-- `t χ(t) ≥ 11` on `(0,1)`.  The cubic cofactor is `k(t) = 31+20t-12t²-12t³-12t⁴-12t⁵`:
`31 - 11 t - 32 t² + 12 t⁶ = (1-t) k(t)`. -/
theorem t_mul_famChi_ge {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 11 ≤ t * famChi t := by
  have h1t : 0 < 1 - t := by linarith
  have e1 : t * famChi t - 11 =
      (1 - t) * (31 + 20 * t - 12 * t ^ 2 - 12 * t ^ 3 - 12 * t ^ 4 - 12 * t ^ 5) / t +
        t ^ 3 / (10 * (1 - t)) := by
    unfold famChi
    field_simp
    ring
  have p2 : t ^ 2 ≤ t := by nlinarith
  have p3 : t ^ 3 ≤ t ^ 2 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
  have p4 : t ^ 4 ≤ t ^ 2 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
  have p5 : t ^ 5 ≤ t ^ 2 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
  have hk : 0 ≤ 31 + 20 * t - 12 * t ^ 2 - 12 * t ^ 3 - 12 * t ^ 4 - 12 * t ^ 5 := by nlinarith
  have : 0 ≤ t * famChi t - 11 := by
    rw [e1]
    have := div_nonneg (mul_nonneg h1t.le hk) ht0.le
    have := div_nonneg (pow_nonneg ht0.le 3) (by positivity : (0 : ℝ) ≤ 10 * (1 - t))
    positivity
  linarith

theorem famChi_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < famChi t := by
  have h := t_mul_famChi_ge ht0 ht1
  by_contra hc
  push Not at hc
  nlinarith [mul_nonpos_of_nonneg_of_nonpos ht0.le hc]

/-- `χ a ≥ 44/5` (> 11/2). -/
theorem famChi_mul_bias_ge {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 44 / 5 ≤ famChi t * famBias t := by
  have h1 := t_mul_famChi_ge ht0 ht1
  have h2 := (famBias_bounds ht0.le ht1.le).1
  have hχ := famChi_pos ht0 ht1
  -- χ a ≥ χ · 4t/5 = (4/5)(tχ) ≥ 44/5
  nlinarith [mul_le_mul_of_nonneg_left h2 hχ.le]

/-- `ω(t) = 1/χ(t)` (`d12-spin-eq:h`): the stable rational form agrees with the reciprocal. -/
theorem famOmega_mul_famChi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : famOmega t * famChi t = 1 := by
  have h1t : 0 < 1 - t := by linarith
  have hP : 0 < famP (t ^ 2) * (1 - t) + t ^ 4 / 10 := by
    have hb : 0 < 31 * (1 - t ^ 2) ^ 3 + 61 * t ^ 2 * (1 - t ^ 2) ^ 2 + 29 * t ^ 4 * (1 - t ^ 2) + 11 * t ^ 6 := by
      have : 0 < 1 - t ^ 2 := by nlinarith
      positivity
    have hid : famP (t ^ 2) = 31 * (1 - t ^ 2) ^ 3 + 61 * t ^ 2 * (1 - t ^ 2) ^ 2 +
        29 * t ^ 4 * (1 - t ^ 2) + 11 * t ^ 6 := by unfold famP; ring
    rw [hid]; positivity
  have hchi : famChi t = (famP (t ^ 2) * (1 - t) + t ^ 4 / 10) / (t ^ 2 * (1 - t)) := by
    unfold famChi famP
    field_simp
  rw [hchi]
  unfold famOmega
  have hne : famP (t ^ 2) * (1 - t) + t ^ 4 / 10 ≠ 0 := hP.ne'
  have h2 : t ^ 2 * (1 - t) ≠ 0 := by positivity
  rw [div_mul_div_comm, mul_comm (t ^ 2 * (1 - t)) (famP (t ^ 2) * (1 - t) + t ^ 4 / 10)]
  exact div_self (mul_ne_zero hne h2)

/-- Tangent-line bound at the mean `11/2` for the concave map `y ↦ (y - c)/(χ + y)`.
This is the independent cross-check of the Jensen step; the written Jensen route is in
`FamilyJensen`. -/
theorem tangent_term {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < χ + c) {k : ℝ} (hk : 0 ≤ k) :
    (k - c) / (χ + k) ≤
      (11 / 2 - c) / (χ + 11 / 2) + (χ + c) / (χ + 11 / 2) ^ 2 * (k - 11 / 2) := by
  have hk' : 0 < χ + k := by linarith
  have hm : 0 < χ + 11 / 2 := by linarith
  have key : (11 / 2 - c) / (χ + 11 / 2) + (χ + c) / (χ + 11 / 2) ^ 2 * (k - 11 / 2) -
      (k - c) / (χ + k) = (χ + c) * (k - 11 / 2) ^ 2 / ((χ + k) * (χ + 11 / 2) ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (χ + c) * (k - 11 / 2) ^ 2 / ((χ + k) * (χ + 11 / 2) ^ 2) := by positivity
  linarith

/-- Sum over the twelve integers `0..11`; the linear terms cancel because the mean is `11/2`. -/
theorem sum_tangent {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < χ + c) :
    ∑ k ∈ Finset.range 12, ((k : ℝ) - c) / (χ + k) ≤ 12 * ((11 / 2 - c) / (χ + 11 / 2)) := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range 12) =>
    tangent_term hχ hc (Nat.cast_nonneg k))
  have hlin : ∑ k ∈ Finset.range 12, ((k : ℝ) - 11 / 2) = 0 := by
    norm_num [Finset.sum_range_succ]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hlin, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_zero, add_zero] at h
  push_cast at h
  exact h

/-- State-zero cap: with `χ > 0`, `a < 1`, `χ a > 11/2`, the product `ν_0 / b_0 < 1`. -/
theorem state_zero_ratio_lt_one {χ a : ℝ} (hχ : 0 < χ) (ha1 : a < 1) (hca : 11 / 2 < χ * a) :
    ∏ k ∈ Finset.range 12, (χ * (1 - a) + 2 * k) / (χ + k) < 1 := by
  have hapos : 0 < a := by
    by_contra h; push Not at h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hχ.le h]
  have hfac : ∀ k ∈ Finset.range 12, (χ * (1 - a) + 2 * k) / (χ + k) ≤
      Real.exp ((k - χ * a) / (χ + k)) := by
    intro k _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (χ * (1 - a) + 2 * k) / (χ + k) = (k - χ * a) / (χ + k) + 1 := by
      field_simp; ring
    rw [this]
    exact Real.add_one_le_exp _
  have hnn : ∀ k ∈ Finset.range 12, 0 ≤ (χ * (1 - a) + 2 * k) / (χ + k) := by
    intro k _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    apply div_nonneg
    · have : 0 < 1 - a := by linarith
      positivity
    · linarith
  calc ∏ k ∈ Finset.range 12, (χ * (1 - a) + 2 * k) / (χ + k)
      ≤ ∏ k ∈ Finset.range 12, Real.exp ((k - χ * a) / (χ + k)) := Finset.prod_le_prod₀ hnn hfac
    _ = Real.exp (∑ k ∈ Finset.range 12, ((k : ℝ) - χ * a) / (χ + k)) := (Real.exp_sum _ _).symm
    _ < 1 := by
      rw [Real.exp_lt_one_iff]
      have hcpos : 0 < χ + χ * a := by nlinarith
      have h := sum_tangent hχ hcpos (c := χ * a)
      have hm : 0 < χ + 11 / 2 := by linarith
      have : (11 / 2 - χ * a) / (χ + 11 / 2) < 0 := div_neg_of_neg_of_pos (by linarith) hm
      linarith

end BecknerOnofri.V2.FiniteState
