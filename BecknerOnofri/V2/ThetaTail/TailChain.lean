module

public import BecknerOnofri.V2.ThetaTail.ExpLower
public import BecknerOnofri.V2.ThetaTail.Harmonic
public import BecknerOnofri.V2.ThetaTail.TailGauss

@[expose] public section

/-! # The case `n ≥ 4` (`d12-tail-eq:logxy`, `Qtail`, `tailBern`)

With `x = (n+1/2)^{-1} ≤ 2/9` and `y = 1 - 9x/2 ∈ [0,1)`: `R_n − U(x) > Q(x,y) > 0`.
Unconditional (`U` is only a function here). -/
noncomputable section
open Finset
namespace BecknerOnofri.V2.ThetaTail

lemma aCoef_one (n : ℕ) : aCoef n 1 = (n : ℝ) / ((n : ℝ) + 1) := by
  have h := aCoef_succ n 0
  have e : (((0 : ℕ) : ℤ) + 1) = 1 := by norm_num
  rw [e, show ((0 : ℕ) : ℤ) = 0 by rfl, aCoef_zero] at h
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  simpa using h

lemma aCoef_two (n : ℕ) : aCoef n 2 = (n : ℝ) * ((n : ℝ) - 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have h := aCoef_succ n 1
  have e : (((1 : ℕ) : ℤ) + 1) = 2 := by norm_num
  rw [e, show ((1 : ℕ) : ℤ) = 1 by rfl, aCoef_one] at h
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  push_cast at h
  field_simp at h
  nlinarith [h]

lemma aCoef_three (n : ℕ) : aCoef n 3 =
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have h := aCoef_succ n 2
  have e : (((2 : ℕ) : ℤ) + 1) = 3 := by norm_num
  rw [e, show ((2 : ℕ) : ℤ) = 2 by rfl, aCoef_two] at h
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  push_cast at h
  field_simp at h
  nlinarith [h]

lemma xn_eq (n : ℕ) : xn n = 2 / (2 * (n : ℝ) + 1) := by
  unfold xn; field_simp

lemma aCoef_one_x (n : ℕ) : aCoef n 1 = aRat1 (xn n) := by
  rw [aCoef_one, xn_eq]; unfold aRat1
  have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma aCoef_two_x (n : ℕ) : aCoef n 2 = aRat2 (xn n) := by
  rw [aCoef_two, xn_eq]; unfold aRat2
  have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : 2 + 3 * (2 / (2 * (n : ℝ) + 1)) ≠ 0 := by positivity
  field_simp
  ring

lemma aCoef_three_x (n : ℕ) : aCoef n 3 = aRat3 (xn n) := by
  rw [aCoef_three, xn_eq]; unfold aRat3
  have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

/-- `U(x) < R_n` for `n ≥ 4`, `x = (n+1/2)^{-1}`. -/
theorem Ufun_lt_Rn {n : ℕ} (hn : 4 ≤ n) : Ufun (xn n) < Rn n := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  set x := xn n with hx
  have hxpos : 0 < x := xn_pos n
  have hxle : x ≤ 2 / 9 := by
    rw [hx, xn_eq, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set y : ℝ := 1 - 9 * x / 2 with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hy1 : y < 1 := by rw [hy]; linarith
  have hxy : x = 2 * (1 - y) / 9 := by rw [hy]; ring
  -- logarithm
  have hL : 3 / 2 + y < -Real.log x := by
    have h92 : (3 : ℝ) / 2 < Real.log (9 / 2) := by
      have h1 := logLower_le_log 16 (9 / 2) (by norm_num)
      have h2 := ratCast_lt log92_lower
      push_cast at h1 h2 ⊢; linarith
    have hlog1 : Real.log (1 - y) ≤ -y := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 - y by linarith); linarith
    have hx' : x = (1 - y) / (9 / 2) := by rw [hxy]; ring
    have : Real.log x = Real.log (1 - y) - Real.log (9 / 2) := by
      rw [hx', Real.log_div (by linarith) (by norm_num)]
    rw [this]; linarith
  have hH : -Real.log x + 577 / 1000 < Hn n := by
    have := Hn_gt n (by omega)
    have e : -Real.log x = Real.log ((n : ℝ) + 1 / 2) := by
      rw [hx]; unfold xn; rw [one_div, Real.log_inv]; ring
    rw [e]; exact this
  have hS := tailL_le_expSum hy0 hxy
  have hQ := tailQ_pos y hy0 hy1.le
  rw [← hxy] at hQ
  unfold Ufun Rn
  unfold tailQ at hQ
  rw [aCoef_one_x, aCoef_two_x, aCoef_three_x]
  linarith

end BecknerOnofri.V2.ThetaTail
