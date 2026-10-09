module

public import BecknerOnofri.V2.ThetaTail.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-! # Binomial stage, one-dimensional part (Appendix A.1, "Binomial domination")

With `x = (n+1/2)^{-1}`:

* `a_n(j+1)(n+j+1) = a_n(j)(n-j)`;
* `a_n(j) ≤ e^{-x j²}` for all `j ≥ 0` (artanh bound `2 artanh t ≥ 2t`);
* `a_n(j) e^{x j²}` is nonincreasing in `j ≥ 0` (for `0 ≤ j ≤ n`, and `0` beyond). -/
noncomputable section
open Finset
namespace BecknerOnofri.V2.ThetaTail

lemma aCoef_nonneg (n : ℕ) (j : ℤ) : 0 ≤ aCoef n j := by unfold aCoef; positivity

lemma aCoef_neg (n : ℕ) (j : ℤ) : aCoef n (-j) = aCoef n j := by unfold aCoef; simp

lemma aCoef_natCast (n j : ℕ) :
    aCoef n (j : ℤ) = ((2 * n).choose (n + j) : ℝ) / ((2 * n).choose n : ℝ) := by
  unfold aCoef; simp

lemma aCoef_zero (n : ℕ) : aCoef n 0 = 1 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, aCoef_natCast]
  have : ((2 * n).choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  simp [this]

lemma aCoef_eq_zero_of_lt (n : ℕ) (j : ℕ) (h : n < j) : aCoef n (j : ℤ) = 0 := by
  rw [aCoef_natCast, Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma choose_ratio (n j : ℕ) :
    ((2 * n).choose (n + (j + 1)) : ℝ) * ((n : ℝ) + j + 1)
      = ((2 * n).choose (n + j) : ℝ) * ((n : ℝ) - j) := by
  by_cases hj : j ≤ n
  · have h := Nat.choose_succ_right_eq (2 * n) (n + j)
    have h2 : ((2 * n).choose (n + j + 1) : ℝ) * ((n + j + 1 : ℕ) : ℝ)
        = ((2 * n).choose (n + j) : ℝ) * ((2 * n - (n + j) : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub (by omega)] at h2
    push_cast at h2
    rw [← add_assoc]
    linarith
  · have h1 : (2 * n).choose (n + j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (2 * n).choose (n + (j + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2]; simp

lemma aCoef_succ (n j : ℕ) :
    aCoef n ((j : ℤ) + 1) * ((n : ℝ) + j + 1) = aCoef n (j : ℤ) * ((n : ℝ) - j) := by
  have e : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, aCoef_natCast, aCoef_natCast]
  have hc : ((2 * n).choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have := choose_ratio n j
  field_simp
  linarith

/-- the artanh-type step: `(n-j)/(n+j+1) ≤ exp(-x(2j+1))` for `0 ≤ j < n`, `x = 1/(n+1/2)`. -/
lemma ratio_le_exp (n j : ℕ) (hj : j < n) :
    ((n : ℝ) - j) ≤ ((n : ℝ) + j + 1) * Real.exp (-((1 / ((n : ℝ) + 1 / 2)) * (2 * j + 1))) := by
  set t : ℝ := (2 * j + 1) / (2 * n + 1) with ht
  have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  have h0 : 0 ≤ t := by positivity
  have h1 : t < 1 := by
    rw [ht, div_lt_one (by positivity)]; linarith
  have hlog := Real.sum_range_le_log_div h0 h1 1
  simp only [range_one, sum_singleton, mul_zero, zero_add, pow_one, Nat.cast_zero, div_one] at hlog
  have hr : (1 + t) / (1 - t) = ((n : ℝ) + j + 1) / ((n : ℝ) - j) := by
    have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : ((n : ℝ) - j) ≠ 0 := by linarith
    have e1 : 1 + t = 2 * ((n : ℝ) + j + 1) / (2 * n + 1) := by rw [ht]; field_simp; ring
    have e2 : 1 - t = 2 * ((n : ℝ) - j) / (2 * n + 1) := by rw [ht]; field_simp; ring
    rw [e1, e2]
    field_simp
  rw [hr] at hlog
  have hpos : (0 : ℝ) < (n : ℝ) - j := by linarith
  have hx : (1 / ((n : ℝ) + 1 / 2)) * (2 * j + 1) = 2 * t := by
    rw [ht]; field_simp
  rw [hx]
  have hl2 : 2 * t ≤ Real.log (((n : ℝ) + j + 1) / ((n : ℝ) - j)) := by linarith
  have := Real.exp_le_exp.2 hl2
  rw [Real.exp_log (by positivity)] at this
  rw [Real.exp_neg]
  have hE : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [le_div_iff₀ hpos] at this
  rw [← div_eq_mul_inv, le_div_iff₀ hE]
  linarith

/-- `x = (n+1/2)^{-1}` -/
def xn (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1 / 2)

lemma xn_pos (n : ℕ) : 0 < xn n := by unfold xn; positivity

lemma aCoef_natAbs (n : ℕ) (k : ℤ) : aCoef n k = aCoef n (k.natAbs : ℤ) := by
  unfold aCoef; rw [Int.natAbs_natCast]

lemma natAbs_sq_real (k : ℤ) : ((k.natAbs : ℕ) : ℝ) ^ 2 = (k : ℝ) ^ 2 := by
  have := congrArg (Int.cast : ℤ → ℝ) (Int.natAbs_sq k)
  simpa using this

/-- `a_n(j+1) e^{x(j+1)²} ≤ a_n(j) e^{x j²}` -/
lemma step_le (n j : ℕ) :
    aCoef n ((j + 1 : ℕ) : ℤ) * Real.exp (xn n * ((j + 1 : ℕ) : ℝ) ^ 2)
      ≤ aCoef n (j : ℤ) * Real.exp (xn n * (j : ℝ) ^ 2) := by
  by_cases hj : j < n
  · have hs := aCoef_succ n j
    have hr := ratio_le_exp n j hj
    have ha := aCoef_nonneg n (j : ℤ)
    have hden : (0 : ℝ) < (n : ℝ) + j + 1 := by positivity
    have e : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e] at hs
    -- a(j+1) ≤ a(j) exp(-x(2j+1))
    have h1 : aCoef n ((j + 1 : ℕ) : ℤ) ≤ aCoef n (j : ℤ) * Real.exp (-(xn n * (2 * j + 1))) := by
      have : aCoef n ((j + 1 : ℕ) : ℤ) * ((n : ℝ) + j + 1)
          ≤ aCoef n (j : ℤ) * Real.exp (-(xn n * (2 * j + 1))) * ((n : ℝ) + j + 1) := by
        rw [hs]
        calc aCoef n (j : ℤ) * ((n : ℝ) - j)
            ≤ aCoef n (j : ℤ) * (((n : ℝ) + j + 1) * Real.exp (-(xn n * (2 * j + 1)))) :=
              mul_le_mul_of_nonneg_left hr ha
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hden
    have h2 : Real.exp (xn n * ((j + 1 : ℕ) : ℝ) ^ 2)
        = Real.exp (xn n * (j : ℝ) ^ 2) * Real.exp (xn n * (2 * j + 1)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [h2]
    calc aCoef n ((j + 1 : ℕ) : ℤ) * (Real.exp (xn n * (j : ℝ) ^ 2) * Real.exp (xn n * (2 * j + 1)))
        ≤ aCoef n (j : ℤ) * Real.exp (-(xn n * (2 * j + 1))) *
            (Real.exp (xn n * (j : ℝ) ^ 2) * Real.exp (xn n * (2 * j + 1))) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = aCoef n (j : ℤ) * Real.exp (xn n * (j : ℝ) ^ 2) := by
          rw [Real.exp_neg]
          have : Real.exp (xn n * (2 * j + 1)) ≠ 0 := (Real.exp_pos _).ne'
          field_simp
  · have h0 : aCoef n ((j + 1 : ℕ) : ℤ) = 0 := aCoef_eq_zero_of_lt n (j + 1) (by omega)
    rw [h0]; simp
    exact mul_nonneg (aCoef_nonneg n _) (Real.exp_pos _).le

/-- monotonicity of `a_n(j) e^{x j²}` in `j ≥ 0` -/
theorem aCoef_mul_exp_antitone (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    aCoef n (j : ℤ) * Real.exp (xn n * (j : ℝ) ^ 2) ≤ aCoef n (i : ℤ) * Real.exp (xn n * (i : ℝ) ^ 2) := by
  have : Antitone (fun j : ℕ => aCoef n (j : ℤ) * Real.exp (xn n * (j : ℝ) ^ 2)) :=
    antitone_nat_of_succ_le fun j => by simpa using step_le n j
  exact this hij

/-- `a_n(j) ≤ e^{-x j²}` for natural `j` -/
theorem aCoef_le_exp_nat (n j : ℕ) : aCoef n (j : ℤ) ≤ Real.exp (-(xn n * (j : ℝ) ^ 2)) := by
  have h := aCoef_mul_exp_antitone n (Nat.zero_le j)
  rw [show ((0 : ℕ) : ℤ) = 0 by rfl, aCoef_zero] at h
  simp at h
  have hE := Real.exp_pos (xn n * (j : ℝ) ^ 2)
  have := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hE.le)
  rw [mul_assoc, mul_inv_cancel₀ hE.ne', mul_one, one_mul] at this
  rwa [Real.exp_neg]

/-- `a_n(k) ≤ e^{-x k²}` for integer `k` -/
theorem aCoef_le_exp (n : ℕ) (k : ℤ) : aCoef n k ≤ Real.exp (-(xn n * (k : ℝ) ^ 2)) := by
  rw [aCoef_natAbs]
  have := aCoef_le_exp_nat n k.natAbs
  have e := natAbs_sq_real k
  rwa [e] at this

/-- for `|k| ≥ 2`: `a_n(k) ≤ a_n(2) e^{4x} e^{-x k²}` -/
theorem aCoef_le_two (n : ℕ) (k : ℤ) (hk : 2 ≤ k.natAbs) :
    aCoef n k ≤ aCoef n 2 * Real.exp (4 * xn n) * Real.exp (-(xn n * (k : ℝ) ^ 2)) := by
  rw [aCoef_natAbs]
  have h := aCoef_mul_exp_antitone n hk
  have e := natAbs_sq_real k
  rw [e] at h
  have h2 : aCoef n ((2 : ℕ) : ℤ) = aCoef n 2 := rfl
  rw [h2] at h
  have e4 : Real.exp (xn n * ((2 : ℕ) : ℝ) ^ 2) = Real.exp (4 * xn n) := by
    congr 1; push_cast; ring
  rw [e4] at h
  have hE := Real.exp_pos (xn n * (k : ℝ) ^ 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hE]
  exact h

end BecknerOnofri.V2.ThetaTail
