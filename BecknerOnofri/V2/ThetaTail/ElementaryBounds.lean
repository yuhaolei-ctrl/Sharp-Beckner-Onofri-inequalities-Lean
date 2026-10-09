module

public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-! # Elementary algebraic bounds of Appendix A.1

* `(1-v)^n ≤ 1 - n v + C(n,2) v^2` for `0 ≤ v ≤ 1` (the source's Taylor estimate for `n = 12`);
* `q (1-q²)^12 ≤ q - 12 q³ + 66 q⁵` for `0 ≤ q ≤ 1`;
* the polynomial part `(1+2q)^12 - 1 - 16(q - 12q³ + 66q⁵) = ∑ s^6 d_s q^s`
  with the exceptional `d_1, d_3, d_5` of `(d12-tail-eq:bexceptions)`. -/
noncomputable section
namespace BecknerOnofri.V2.ThetaTail

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem one_sub_pow_le (v : K) (h0 : 0 ≤ v) (h1 : v ≤ 1) (n : ℕ) :
    (1 - v) ^ n ≤ 1 - n * v + (Nat.choose n 2 : K) * v ^ 2 := by
  have hv : 0 ≤ 1 - v := sub_nonneg.2 h1
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (Nat.choose (n + 1) 2 : K) = n + (Nat.choose n 2 : K) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]; push_cast; ring
    have hcn : (0 : K) ≤ (Nat.choose n 2 : K) := Nat.cast_nonneg _
    have step : (1 - v) ^ (n + 1) ≤ (1 - v) * (1 - n * v + (Nat.choose n 2 : K) * v ^ 2) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left ih hv
    have eq : (1 - v) * (1 - n * v + (Nat.choose n 2 : K) * v ^ 2)
        = (1 - ((n + 1 : ℕ) : K) * v + (Nat.choose (n + 1) 2 : K) * v ^ 2)
          - (Nat.choose n 2 : K) * v ^ 3 := by
      rw [hc]; push_cast; ring
    rw [eq] at step
    exact step.trans (sub_le_self _ (mul_nonneg hcn (pow_nonneg h0 3)))

/-- `(1-v)^12 ≤ 1 - 12 v + 66 v²`. -/
theorem one_sub_pow_twelve_le (v : K) (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    (1 - v) ^ 12 ≤ 1 - 12 * v + 66 * v ^ 2 := by
  have h := one_sub_pow_le v h0 h1 12
  have hc : (Nat.choose 12 2 : K) = 66 := by norm_num [Nat.choose]
  simpa [hc] using h

/-- `q ∏ (1-q^{2m})^12 ≤ q (1-q²)^12 ≤ q - 12 q³ + 66 q⁵` (finite part: second inequality). -/
theorem q_mul_one_sub_sq_pow_le (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    q * (1 - q ^ 2) ^ 12 ≤ q - 12 * q ^ 3 + 66 * q ^ 5 := by
  have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have h := one_sub_pow_twelve_le (q ^ 2) (pow_nonneg h0 2) hq2
  have := mul_le_mul_of_nonneg_left h h0
  calc q * (1 - q ^ 2) ^ 12 ≤ q * (1 - 12 * q ^ 2 + 66 * (q ^ 2) ^ 2) := this
    _ = q - 12 * q ^ 3 + 66 * q ^ 5 := by ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- polynomial part, in `d_s s^6` form: coefficients `8, 264·…` are `2^s C(12,s)` except
`s = 1,3,5` which are corrected by `-16, +192, -1056`. -/
theorem polynomial_part (q : K) :
    (1 + 2 * q) ^ 12 - 1 - 16 * (q - 12 * q ^ 3 + 66 * q ^ 5)
      = 8 * q + 264 * q ^ 2 + 1952 * q ^ 3 + 7920 * q ^ 4 + 24288 * q ^ 5 + 59136 * q ^ 6
        + 101376 * q ^ 7 + 126720 * q ^ 8 + 112640 * q ^ 9 + 67584 * q ^ 10
        + 24576 * q ^ 11 + 4096 * q ^ 12 := by
  ring

end BecknerOnofri.V2.ThetaTail
