module

public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

/-! # The two completions of squares in Lemma 5.16 (`d12-circle-eq:complete-start`, `d12-circle-eq:ABC`)

For ARBITRARY elements `a b` of an ordered field (no moment-feasibility hypothesis):

* `C (b - t a)^2 + δ b^2 ≥ (δ C / (C + δ)) t^2 a^2`      for `C ≥ 0`, `δ > 0`;
* `A a^2 + B (a - u)^2 ≥ (A B / (A + B)) u^2`           for `A > 0`, `B > 0`.

Both are exact identities with a nonnegative square; every denominator is strictly positive.
Generic in the ordered field so that it compiles against the oleans available early; it is
used at `K = ℝ`. -/
noncomputable section
namespace BecknerOnofri.V2.Circle

variable {K : Type*} [Field K]

/-- Exact identity behind the second completion. -/
theorem complete_a_identity (A B u a : K) (hAB : A + B ≠ 0) :
    A * a ^ 2 + B * (a - u) ^ 2 - A * B * u ^ 2 / (A + B) =
      (A + B) * (a - B * u / (A + B)) ^ 2 := by
  have hs : (A + B) * (A + B)⁻¹ = 1 := mul_inv_cancel₀ hAB
  set s := (A + B)⁻¹ with hsdef
  have e1 : A * B * u ^ 2 / (A + B) = A * B * u ^ 2 * s := by rw [div_eq_mul_inv]
  have e2 : B * u / (A + B) = B * u * s := by rw [div_eq_mul_inv]
  rw [e1, e2]
  have hc : A * a ^ 2 + B * (a - u) ^ 2 - A * B * u ^ 2 * s - (A + B) * (a - B * u * s) ^ 2 =
      (1 - (A + B) * s) * (B * u ^ 2 + B ^ 2 * u ^ 2 * s - 2 * B * u * a) := by ring
  rw [hs, sub_self, zero_mul] at hc
  exact sub_eq_zero.mp hc

/-- Exact identity behind the first completion; `δ` is the constant `11/120` of the source. -/
theorem complete_b_identity (C δ t a b : K) (hCδ : C + δ ≠ 0) :
    C * (b - t * a) ^ 2 + δ * b ^ 2 - δ * C / (C + δ) * (t ^ 2 * a ^ 2) =
      (C + δ) * (b - C * t * a / (C + δ)) ^ 2 := by
  have hs : (C + δ) * (C + δ)⁻¹ = 1 := mul_inv_cancel₀ hCδ
  set s := (C + δ)⁻¹ with hsdef
  have e1 : δ * C / (C + δ) = δ * C * s := by rw [div_eq_mul_inv]
  have e2 : C * t * a / (C + δ) = C * t * a * s := by rw [div_eq_mul_inv]
  rw [e1, e2]
  have hc : C * (b - t * a) ^ 2 + δ * b ^ 2 - δ * C * s * (t ^ 2 * a ^ 2) -
      (C + δ) * (b - C * t * a * s) ^ 2 =
      (1 - (C + δ) * s) * (C * t ^ 2 * a ^ 2 + C ^ 2 * t ^ 2 * a ^ 2 * s - 2 * C * t * a * b) := by
    ring
  rw [hs, sub_self, zero_mul] at hc
  exact sub_eq_zero.mp hc

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Second completion of squares (`Aa²+B(a-u)² ≥ AB/(A+B) u²`). -/
theorem complete_a_lower (A B u a : K) (hA : 0 < A) (hB : 0 < B) :
    A * B * u ^ 2 / (A + B) ≤ A * a ^ 2 + B * (a - u) ^ 2 := by
  have h := complete_a_identity A B u a (add_pos hA hB).ne'
  have hnn : 0 ≤ (A + B) * (a - B * u / (A + B)) ^ 2 :=
    mul_nonneg (add_pos hA hB).le (sq_nonneg _)
  rw [← h] at hnn
  exact sub_nonneg.mp hnn

/-- First completion of squares (`C(b-ta)²+δb² ≥ δC/(C+δ) t²a²`). -/
theorem complete_b_lower (C δ t a b : K) (hC : 0 ≤ C) (hδ : 0 < δ) :
    δ * C / (C + δ) * (t ^ 2 * a ^ 2) ≤ C * (b - t * a) ^ 2 + δ * b ^ 2 := by
  have hpos : 0 < C + δ := add_pos_of_nonneg_of_pos hC hδ
  have h := complete_b_identity C δ t a b hpos.ne'
  have hnn : 0 ≤ (C + δ) * (b - C * t * a / (C + δ)) ^ 2 := mul_nonneg hpos.le (sq_nonneg _)
  rw [← h] at hnn
  exact sub_nonneg.mp hnn

/-- With `δ = 11/120` the coefficient is `11 C u/(120 C + 11)` when `u = t²`:
`δ C/(C+δ) = 11 C /(120 C + 11)`. -/
theorem delta_coeff (C : K) (hC : 0 ≤ C) [CharZero K] :
    (11 / 120 : K) * C / (C + 11 / 120) = 11 * C / (120 * C + 11) := by
  have h1 : (C + 11 / 120 : K) ≠ 0 := by
    have : (0:K) < C + 11 / 120 := by
      have : (0:K) < 11 / 120 := by norm_num
      exact add_pos_of_nonneg_of_pos hC this
    exact this.ne'
  have h2 : (120 * C + 11 : K) ≠ 0 := by
    have : (0:K) < 120 * C + 11 := by
      have : (0:K) ≤ 120 * C := mul_nonneg (by norm_num) hC
      exact add_pos_of_nonneg_of_pos this (by norm_num)
    exact this.ne'
  rw [div_eq_div_iff h1 h2]
  ring

end BecknerOnofri.V2.Circle
