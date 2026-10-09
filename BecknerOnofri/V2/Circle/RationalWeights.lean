module

public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import BecknerOnofri.CircleWeightIntegral
public import BecknerOnofri.V2.Circle.ScalarCircle

@[expose] public section

/-! # Exact remainders for the rational weights (Appendix A.2.2, `d12-circle-eq:Wremainder`, `d12-circle-eq:Wlower`)

For `j = 1, 2` let `pi_1 = x^3 - 12/7 x^2 + 6/7 x - 4/35`, `pi_2 = x^3 - 15/8 x^2 + 15/14 x - 5/28`
and `Q_j(u) = 1 + a u + b u^2 + c u^3 = u^3 pi_j(1/u)` as a POLYNOMIAL in `u` (`Qpoly`), so that no
evaluation of `u^3 pi_j(1/u)` at `u = 0` is needed.

* `quotient_identity`: `Q(u) - u^3 pi(x) = (1 - u x) S(u,x)` with `S` a polynomial of degree two in `x`.
* `pi1_orth`, `pi2_orth`: the three moment cancellations `int_0^1 x^(j+k) pi_j = 0`, `k = 0,1,2`.
* `weight_remainder_identity`: `Q^2 w_j - Q M_j = u^6 int_0^1 x^j pi_j^2/(1-u x)` where
  `M_j = int_0^1 x^j S`, using the orthogonalities (this is `d12-circle-eq:Wremainder` cleared of
  denominators; it holds also at `u = 0`).
* `weight_one_remainder`, `weight_two_remainder`: `w_j(t) - L_j(t^2) = t^12/Q_j(t^2)^2 int x^j pi_j^2/(1-t^2 x)`
  for `0 <= t < 1`, with the repository weight `weight j t = int_0^1 s^j/(1-t^2 s)`.
* `weight_one_ge`, `weight_two_ge`: `L_j(t^2) <= weight j t` (`d12-circle-eq:Wlower`). -/
noncomputable section
open intervalIntegral MeasureTheory Set
namespace BecknerOnofri.V2.Circle
open BecknerOnofri.HighDim.CircleScalar

theorem integral_monomial (c : ℝ) (m : ℕ) : ∫ x in (0:ℝ)..1, c * x ^ m = c / (m + 1) := by
  rw [intervalIntegral.integral_const_mul, integral_pow]; simp [div_eq_mul_inv]

/-- Kernel integrability: `x ↦ f(x)/(1-ux)` is interval integrable on `[0,1]` for `u<1`, `u ≥ 0`. -/
theorem kernel_intervalIntegrable {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) {f : ℝ → ℝ}
    (hf : Continuous f) : IntervalIntegrable (fun x => f x / (1 - u * x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div hf.continuousOn (by fun_prop)
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  have : u * x ≤ u := by nlinarith [hx.1, hx.2]
  linarith


/-- The cubic `π(x) = x³ + a x² + b x + c`. -/
def cub (a b c x : ℝ) : ℝ := x ^ 3 + a * x ^ 2 + b * x + c

/-- `Q(u) = u³ π(1/u) = 1 + a u + b u² + c u³` as a polynomial in `u`. -/
def Qpoly (a b c u : ℝ) : ℝ := 1 + a * u + b * u ^ 2 + c * u ^ 3

/-- The quotient `S(u,x)` with `Q(u) - u³ π(x) = (1 - u x) S(u,x)`. -/
def Squot (a b u x : ℝ) : ℝ := (1 + u * x + u ^ 2 * x ^ 2) + a * u * (1 + u * x) + b * u ^ 2

theorem quotient_identity (a b c u x : ℝ) :
    Qpoly a b c u - u ^ 3 * cub a b c x = (1 - u * x) * Squot a b u x := by
  unfold Qpoly cub Squot; ring

/-- Moment of `S` against `x^j`. -/
def Smoment (a b u : ℝ) (j : ℕ) : ℝ :=
  (1 + a * u + b * u ^ 2) / (j + 1) + (u + a * u ^ 2) / (j + 2) + u ^ 2 / (j + 3)

theorem integral_Squot (a b u : ℝ) (j : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ j * Squot a b u x = Smoment a b u j := by
  have e : ∀ x : ℝ, x ^ j * Squot a b u x = (1 + a * u + b * u ^ 2) * x ^ j + (u + a * u ^ 2) * x ^ (j + 1)
      + u ^ 2 * x ^ (j + 2) := by
    intro x; unfold Squot; ring
  simp_rw [e]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, integral_monomial, integral_monomial,
    integral_monomial]
  · unfold Smoment; push_cast; ring
  all_goals exact (Continuous.intervalIntegrable (by fun_prop) _ _)


theorem weight_remainder_identity (j : ℕ) (a b c u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1)
    (o0 : ∫ x in (0:ℝ)..1, x ^ j * cub a b c x = 0)
    (o1 : ∫ x in (0:ℝ)..1, x ^ (j + 1) * cub a b c x = 0)
    (o2 : ∫ x in (0:ℝ)..1, x ^ (j + 2) * cub a b c x = 0) :
    Qpoly a b c u ^ 2 * (∫ x in (0:ℝ)..1, x ^ j / (1 - u * x)) - Qpoly a b c u * Smoment a b u j =
      u ^ 6 * ∫ x in (0:ℝ)..1, x ^ j * cub a b c x ^ 2 / (1 - u * x) := by
  set q := Qpoly a b c u with hq
  have hden : ∀ x ∈ Icc (0:ℝ) 1, 1 - u * x ≠ 0 := by
    intro x hx
    have : u * x ≤ u := by nlinarith [hx.1, hx.2]
    linarith
  have hII1 : IntervalIntegrable (fun x : ℝ => x ^ j / (1 - u * x)) volume 0 1 :=
    kernel_intervalIntegrable h0 h1 (f := fun x => x ^ j) (by fun_prop)
  have hII2 : IntervalIntegrable (fun x : ℝ => x ^ j * cub a b c x / (1 - u * x)) volume 0 1 :=
    kernel_intervalIntegrable h0 h1 (f := fun x => x ^ j * cub a b c x) (by unfold cub; fun_prop)
  have hII3 : IntervalIntegrable (fun x : ℝ => x ^ j * cub a b c x ^ 2 / (1 - u * x)) volume 0 1 :=
    kernel_intervalIntegrable h0 h1 (f := fun x => x ^ j * cub a b c x ^ 2) (by unfold cub; fun_prop)
  have hPol1 : IntervalIntegrable (fun x : ℝ => x ^ j * Squot a b u x) volume 0 1 :=
    Continuous.intervalIntegrable (by unfold Squot; fun_prop) _ _
  have hPol2 : IntervalIntegrable (fun x : ℝ => x ^ j * cub a b c x * Squot a b u x) volume 0 1 :=
    Continuous.intervalIntegrable (by unfold Squot cub; fun_prop) _ _
  -- step 1
  have step1 : u ^ 3 * (∫ x in (0:ℝ)..1, x ^ j * cub a b c x / (1 - u * x)) =
      q * (∫ x in (0:ℝ)..1, x ^ j / (1 - u * x)) - Smoment a b u j := by
    rw [← integral_Squot, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hII1.const_mul q) hPol1]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have hne := hden x hx
    have := quotient_identity a b c u x
    simp only
    field_simp
    rw [← hq] at this
    linear_combination (x ^ j) * (-1 : ℝ) * this
  -- step 2
  have step2 : u ^ 3 * (∫ x in (0:ℝ)..1, x ^ j * cub a b c x ^ 2 / (1 - u * x)) =
      q * (∫ x in (0:ℝ)..1, x ^ j * cub a b c x / (1 - u * x)) := by
    have e0 : ∫ x in (0:ℝ)..1, x ^ j * cub a b c x * Squot a b u x = 0 := by
      have e : ∀ x : ℝ, x ^ j * cub a b c x * Squot a b u x =
          (1 + a * u + b * u ^ 2) * (x ^ j * cub a b c x) + (u + a * u ^ 2) * (x ^ (j + 1) * cub a b c x)
            + u ^ 2 * (x ^ (j + 2) * cub a b c x) := by
        intro x; unfold Squot; ring
      simp_rw [e]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, o0, o1, o2]
      · ring
      all_goals exact (Continuous.intervalIntegrable (by unfold cub; fun_prop) _ _)
    have key : u ^ 3 * (∫ x in (0:ℝ)..1, x ^ j * cub a b c x ^ 2 / (1 - u * x)) =
        q * (∫ x in (0:ℝ)..1, x ^ j * cub a b c x / (1 - u * x)) -
          ∫ x in (0:ℝ)..1, x ^ j * cub a b c x * Squot a b u x := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (hII2.const_mul q) hPol2]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      have hne := hden x hx
      have := quotient_identity a b c u x
      simp only
      field_simp
      rw [← hq] at this
      linear_combination (x ^ j * cub a b c x) * (-1 : ℝ) * this
    rw [key, e0, sub_zero]
  have : u ^ 6 * (∫ x in (0:ℝ)..1, x ^ j * cub a b c x ^ 2 / (1 - u * x)) =
      q * (u ^ 3 * ∫ x in (0:ℝ)..1, x ^ j * cub a b c x / (1 - u * x)) := by
    rw [show u ^ 6 = u ^ 3 * u ^ 3 by ring, mul_assoc, step2]; ring
  rw [this, step1]; ring


theorem integral_xpow_cub (m : ℕ) (a b c : ℝ) :
    ∫ x in (0:ℝ)..1, x ^ m * cub a b c x = 1 / (m + 4) + a / (m + 3) + b / (m + 2) + c / (m + 1) := by
  have e : ∀ x : ℝ, x ^ m * cub a b c x = 1 * x ^ (m + 3) + a * x ^ (m + 2) + b * x ^ (m + 1) + c * x ^ m := by
    intro x; unfold cub; ring
  simp_rw [e]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add,
    integral_monomial, integral_monomial, integral_monomial, integral_monomial]
  · push_cast; ring_nf
  all_goals exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- `π₁ = x³ - 12/7 x² + 6/7 x - 4/35` -/
abbrev pi1 (x : ℝ) : ℝ := cub (-12 / 7) (6 / 7) (-4 / 35) x
/-- `π₂ = x³ - 15/8 x² + 15/14 x - 5/28` -/
abbrev pi2 (x : ℝ) : ℝ := cub (-15 / 8) (15 / 14) (-5 / 28) x

theorem pi1_orth (k : ℕ) (hk : k ≤ 2) : ∫ x in (0:ℝ)..1, x ^ (1 + k) * pi1 x = 0 := by
  unfold pi1; rw [integral_xpow_cub]
  interval_cases k <;> norm_num

theorem pi2_orth (k : ℕ) (hk : k ≤ 2) : ∫ x in (0:ℝ)..1, x ^ (2 + k) * pi2 x = 0 := by
  unfold pi2; rw [integral_xpow_cub]
  interval_cases k <;> norm_num



theorem Q1_eq (u : ℝ) : Qpoly (-12 / 7) (6 / 7) (-4 / 35) u = (35 - 60 * u + 30 * u ^ 2 - 4 * u ^ 3) / 35 := by
  unfold Qpoly; ring

theorem Q2_eq (u : ℝ) : Qpoly (-15 / 8) (15 / 14) (-5 / 28) u = (56 - 105 * u + 60 * u ^ 2 - 10 * u ^ 3) / 56 := by
  unfold Qpoly; ring

theorem Smoment1_eq (u : ℝ) :
    Smoment (-12 / 7) (6 / 7) u 1 = 3 * u ^ 2 / 28 - 11 * u / 21 + 1 / 2 := by
  unfold Smoment; push_cast; ring

theorem L1_eq_moment {u : ℝ} (h1 : u ≤ 1) :
    L1 u = Smoment (-12 / 7) (6 / 7) u 1 / Qpoly (-12 / 7) (6 / 7) (-4 / 35) u := by
  have hd := (d1_pos h1).ne'
  rw [Q1_eq, Smoment1_eq]
  unfold L1 L1num L1den
  field_simp
  ring

theorem Smoment2_eq (u : ℝ) :
    Smoment (-15 / 8) (15 / 14) u 2 = 99 * u ^ 2 / 1120 - 3 * u / 8 + 1 / 3 := by
  unfold Smoment; push_cast; ring

theorem L2_eq_moment {u : ℝ} (h1 : u ≤ 1) :
    L2 u = Smoment (-15 / 8) (15 / 14) u 2 / Qpoly (-15 / 8) (15 / 14) (-5 / 28) u := by
  have hd := (d2_pos h1).ne'
  rw [Q2_eq, Smoment2_eq]
  unfold L2 L2num L2den
  field_simp
  ring


theorem integral_sq_kernel_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) (j : ℕ) (f : ℝ → ℝ) :
    0 ≤ ∫ x in (0:ℝ)..1, x ^ j * f x ^ 2 / (1 - u * x) := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x hx
  have : u * x ≤ u := by nlinarith [hx.1, hx.2]
  exact div_nonneg (mul_nonneg (pow_nonneg hx.1 j) (sq_nonneg _)) (by linarith)

theorem alg_remainder (w M q u6 W : ℝ) (hq : q ≠ 0) (h : q ^ 2 * w - q * M = u6 * W) :
    w - M / q = u6 / q ^ 2 * W := by
  field_simp
  linear_combination h

/-- Exact remainder `d12-circle-eq:Wremainder` for `j = 1`:
`w₁(t) - L₁(t²) = t¹² / Q₁(t²)² ∫₀¹ x π₁(x)² / (1 - t² x) dx`, `Q₁ = (35-60u+30u²-4u³)/35`. -/
theorem weight_one_remainder {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    weight 1 t - L1 (t ^ 2) =
      (t ^ 2) ^ 6 / Qpoly (-12 / 7) (6 / 7) (-4 / 35) (t ^ 2) ^ 2 *
        ∫ x in (0:ℝ)..1, x ^ 1 * pi1 x ^ 2 / (1 - t ^ 2 * x) := by
  have hu0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hu1 : t ^ 2 < 1 := by nlinarith
  have hid := weight_remainder_identity 1 (-12 / 7) (6 / 7) (-4 / 35) (t ^ 2) hu0 hu1
    (by simpa using pi1_orth 0 (by norm_num)) (by simpa using pi1_orth 1 (by norm_num))
    (by simpa using pi1_orth 2 (by norm_num))
  have hq : 0 < Qpoly (-12 / 7) (6 / 7) (-4 / 35) (t ^ 2) := by
    rw [Q1_eq]; exact div_pos (d1_pos hu1.le) (by norm_num)
  rw [weight_integral 1 t h0 h1, L1_eq_moment hu1.le]
  exact alg_remainder _ _ _ _ _ hq.ne' hid

theorem weight_two_remainder {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    weight 2 t - L2 (t ^ 2) =
      (t ^ 2) ^ 6 / Qpoly (-15 / 8) (15 / 14) (-5 / 28) (t ^ 2) ^ 2 *
        ∫ x in (0:ℝ)..1, x ^ 2 * pi2 x ^ 2 / (1 - t ^ 2 * x) := by
  have hu0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hu1 : t ^ 2 < 1 := by nlinarith
  have hid := weight_remainder_identity 2 (-15 / 8) (15 / 14) (-5 / 28) (t ^ 2) hu0 hu1
    (by simpa using pi2_orth 0 (by norm_num)) (by simpa using pi2_orth 1 (by norm_num))
    (by simpa using pi2_orth 2 (by norm_num))
  have hq : 0 < Qpoly (-15 / 8) (15 / 14) (-5 / 28) (t ^ 2) := by
    rw [Q2_eq]; exact div_pos (d2_pos hu1.le) (by norm_num)
  rw [weight_integral 2 t h0 h1, L2_eq_moment hu1.le]
  exact alg_remainder _ _ _ _ _ hq.ne' hid

/-- `w₁(√u) ≥ L₁(u) > 0` (`d12-circle-eq:Wlower`), `0 ≤ u < 1`, here `u = t²`. -/
theorem weight_one_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : L1 (t ^ 2) ≤ weight 1 t := by
  have hu0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hu1 : t ^ 2 < 1 := by nlinarith
  have := weight_one_remainder h0 h1
  have hI := integral_sq_kernel_nonneg hu0 hu1 1 pi1
  have : 0 ≤ weight 1 t - L1 (t ^ 2) := by
    rw [this]; positivity
  linarith

theorem weight_two_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : L2 (t ^ 2) ≤ weight 2 t := by
  have hu0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hu1 : t ^ 2 < 1 := by nlinarith
  have := weight_two_remainder h0 h1
  have hI := integral_sq_kernel_nonneg hu0 hu1 2 pi2
  have : 0 ≤ weight 2 t - L2 (t ^ 2) := by
    rw [this]; positivity
  linarith

end BecknerOnofri.V2.Circle
