module

public import BecknerOnofri.TwelveThetaIntegrability
public import BecknerOnofri.ElevenThetaIntegral
public import BecknerOnofri.ExponentialIntegralBound

@[expose] public section

/-! # The dimension-twelve theta certificate

Lemma 3.2 (lem:theta-integral-certificate) for `d = 12`: `J_12 < 3.29`.

For `r ≥ 1` we use `ϑ(πr) - 1 ≤ q e^{-π(r-1)}` with `q = 2e^{-π}/(1-e^{-3π})`, expand
`(1 + q e^{-π(r-1)})^12 - 1` binomially, integrate the `r^5` part exactly and bound the `r⁻¹`
part by Lemma 3.1. Numerically `e^{-π} < 0.04322` and `π > 3.1415` are enough. All infinite
series and improper integrals keep their mathematical meanings. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
open Legacy.BecknerOnofri.ThetaDomination
open BecknerOnofri.HighDim.Eleven.ThetaBound (theta_geometric laplacePolynomial
  shifted_moment_integral shifted_moment_integrable)
open BecknerOnofri.HighDim.ThetaElementary

namespace BecknerOnofri.HighDim.Twelve.ThetaBound

/-- Rational upper bound for `e^{-π}`. -/
def expBound : ℝ := 2161 / 50000

/-- Rational lower bound for `π`, used as the decay rate. -/
def rate : ℝ := 6283 / 2000

/-- Rational upper bound for `q = 2e^{-π}/(1-e^{-3π})`. -/
def base : ℝ := 2 * expBound / (1 - expBound ^ 3)

theorem exp_neg_pi_lt : Real.exp (-Real.pi) < expBound := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6283 / 2000) 25
  have hpoly :
      (50000 : ℝ) / 2161 < ∑ j ∈ Finset.range 25, ((6283 : ℝ) / 2000) ^ j / j.factorial := by
    norm_num [Finset.sum_range_succ]
  have he : (50000 : ℝ) / 2161 < Real.exp Real.pi :=
    (hpoly.trans_le h).trans (Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_d4]))
  rw [Real.exp_neg, ← one_div, expBound]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  linarith

theorem theta_uniform {r : ℝ} (hr : 1 ≤ r) :
    realTheta (Real.pi * r) ≤ 1 + (2 / (1 - expBound ^ 3)) * Real.exp (-Real.pi * r) := by
  have ht : 0 < Real.pi * r := mul_pos Real.pi_pos (zero_lt_one.trans_le hr)
  have hg := theta_geometric ht
  have hsmall : Real.exp (-3 * (Real.pi * r)) ≤ expBound ^ 3 := by
    calc
      _ ≤ Real.exp (-3 * Real.pi) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      _ = Real.exp (-Real.pi) ^ 3 := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := by gcongr; exact exp_neg_pi_lt.le
  have hd : (0 : ℝ) < 1 - expBound ^ 3 := by norm_num [expBound]
  have hfrac := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 2 * Real.exp (-(Real.pi * r))) hd (by linarith :
      1 - expBound ^ 3 ≤ 1 - Real.exp (-3 * (Real.pi * r)))
  have he : 2 * Real.exp (-(Real.pi * r)) / (1 - expBound ^ 3) =
      (2 / (1 - expBound ^ 3)) * Real.exp (-Real.pi * r) := by rw [neg_mul]; ring
  linarith

/-- `ϑ(πr) - 1 ≤ q e^{-π(r-1)}` for `r ≥ 1`, with rational constants. -/
theorem theta_shifted {r : ℝ} (hr : 1 ≤ r) :
    realTheta (Real.pi * r) ≤ 1 + base * Real.exp (-rate * (r - 1)) := by
  have he : Real.exp (-Real.pi * r) ≤ expBound * Real.exp (-rate * (r - 1)) := by
    rw [show -Real.pi * r = -Real.pi + (-Real.pi * (r - 1)) by ring, Real.exp_add]
    apply mul_le_mul exp_neg_pi_lt.le ?_ (Real.exp_pos _).le (by norm_num [expBound])
    apply Real.exp_le_exp.mpr
    have hp : rate ≤ Real.pi := by unfold rate; linarith [Real.pi_gt_d4]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left he
    (by norm_num [expBound] : (0 : ℝ) ≤ 2 / (1 - expBound ^ 3))
  have h := theta_uniform hr
  have hb : base = 2 / (1 - expBound ^ 3) * expBound := by unfold base; ring
  rw [hb]
  linarith

theorem base_pos : 0 < base := by norm_num [base, expBound]

theorem exp_scaled (j : ℕ) (r : ℝ) :
    Real.exp (-(((j + 1 : ℕ) : ℝ) * rate) * (r - 1)) =
      (Real.exp (-rate * (r - 1))) ^ (j + 1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem polynomial_identity (b e : ℝ) :
    (1 + b * e) ^ 12 - 1 = ∑ j ∈ Finset.range 12,
      ((12 : ℕ).choose (j + 1) : ℝ) * b ^ (j + 1) * e ^ (j + 1) := by
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- The `j`-th binomial row of the majorant of the dimension-twelve integrand. -/
def row (j : ℕ) (r : ℝ) : ℝ :=
  ((12 : ℕ).choose (j + 1) : ℝ) * base ^ (j + 1) *
    ((r ^ 5 + r⁻¹) * Real.exp (-(((j + 1 : ℕ) : ℝ) * rate) * (r - 1)))

theorem integrand_le_rows {r : ℝ} (hr : 1 ≤ r) :
    thetaIntegrand realTheta 12 r ≤ ∑ j ∈ Finset.range 12, row j r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ht := one_le_realTheta (mul_pos Real.pi_pos hr0)
  have hp := pow_le_pow_left₀ (zero_le_one.trans ht) (theta_shifted hr) 12
  have hw : 0 ≤ r ^ 5 + r⁻¹ := by positivity
  have hrp : r ^ (5 : ℝ) = r ^ 5 := by exact_mod_cast Real.rpow_natCast r 5
  unfold thetaIntegrand
  norm_num only [Nat.cast_ofNat, show (12 : ℝ) / 2 - 1 = 5 by norm_num]
  rw [hrp]
  calc
    _ ≤ (r ^ 5 + r⁻¹) * ((1 + base * Real.exp (-rate * (r - 1))) ^ 12 - 1) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hp 1) hw
    _ = ∑ j ∈ Finset.range 12, row j r := by
      rw [polynomial_identity, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [row, exp_scaled]
      ring

theorem weighted_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => (r ^ 5 + r⁻¹) * Real.exp (-a * (r - 1))) (Ici 1) := by
  refine ((shifted_moment_integrable 5 ha).add (inv_mul_exp_integrableOn ha)).congr_fun
    (fun r _ => ?_) measurableSet_Ici
  simp only [Pi.add_apply]
  ring

theorem weighted_integral_le {a : ℝ} (ha : 0 < a) :
    ∫ r in Ici (1 : ℝ), (r ^ 5 + r⁻¹) * Real.exp (-a * (r - 1)) ≤
      laplacePolynomial 5 a + e1Majorant a := by
  have he : (fun r : ℝ => (r ^ 5 + r⁻¹) * Real.exp (-a * (r - 1))) =
      fun r => r ^ 5 * Real.exp (-a * (r - 1)) + r⁻¹ * Real.exp (-a * (r - 1)) := by
    funext r
    ring
  rw [he, integral_add (shifted_moment_integrable 5 ha) (inv_mul_exp_integrableOn ha),
    shifted_moment_integral 5 ha]
  linarith [integral_inv_mul_exp_le ha]

theorem rate_mul_pos (j : ℕ) : 0 < ((j + 1 : ℕ) : ℝ) * rate := by
  unfold rate; positivity

theorem row_integrable (j : ℕ) : IntegrableOn (row j) (Ici (1 : ℝ)) :=
  (weighted_integrable (rate_mul_pos j)).const_mul _

theorem row_integral_le (j : ℕ) :
    ∫ r in Ici (1 : ℝ), row j r ≤
      ((12 : ℕ).choose (j + 1) : ℝ) * base ^ (j + 1) *
        (laplacePolynomial 5 (((j + 1 : ℕ) : ℝ) * rate) +
          e1Majorant (((j + 1 : ℕ) : ℝ) * rate)) := by
  unfold row
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (weighted_integral_le (rate_mul_pos j))
    (by have := base_pos; positivity)

/-- The rational right-hand side
`Σ_{k=1}^{12} C(12,k) q^k [R_5(kπ) + g(kπ)]`, evaluated at the rational bounds. -/
def rationalUpper : ℝ :=
  ∑ j ∈ Finset.range 12, ((12 : ℕ).choose (j + 1) : ℝ) * base ^ (j + 1) *
    (laplacePolynomial 5 (((j + 1 : ℕ) : ℝ) * rate) + e1Majorant (((j + 1 : ℕ) : ℝ) * rate))

theorem rationalUpper_lt : rationalUpper < 329 / 100 := by
  norm_num [rationalUpper, base, expBound, rate, laplacePolynomial, e1Majorant,
    Finset.sum_range_succ, Nat.choose, Nat.factorial]

/-- Lemma 3.2 (lem:theta-integral-certificate), `J_12 < 3.29`: the full dimension-twelve
improper theta integral, with its rational certificate completely discharged. -/
theorem thetaIntegral_lt : thetaIntegral realTheta 12 < 329 / 100 := by
  have hi : IntegrableOn (fun r => ∑ j ∈ Finset.range 12, row j r) (Ici (1 : ℝ)) :=
    integrable_finsetSum _ (fun j _ => row_integrable j)
  have hb := setIntegral_mono_on theta_integrable hi measurableSet_Ici
    (fun r hr => integrand_le_rows hr)
  have he : ∫ r in Ici (1 : ℝ), ∑ j ∈ Finset.range 12, row j r ≤ rationalUpper := by
    rw [integral_finsetSum _ (fun j _ => row_integrable j)]
    exact Finset.sum_le_sum fun j _ => row_integral_le j
  exact (hb.trans he).trans_lt rationalUpper_lt

end BecknerOnofri.HighDim.Twelve.ThetaBound
