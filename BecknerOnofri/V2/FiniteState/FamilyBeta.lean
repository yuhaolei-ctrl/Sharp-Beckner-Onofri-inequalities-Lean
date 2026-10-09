module

public import BecknerOnofri.V2.FiniteState.FamilyJensen
public import BecknerOnofri.V2.FiniteState.FamilyVariance
public import Mathlib.Probability.Distributions.Beta

@[expose] public section

/-!
# Explicit family: normalisation, mean and variance by Euler's beta integral (Lemma 5.19)

This file follows the written route of Appendix A.3 (`subsec:appendix-family-feasibility`),
proof of `d12-spin-lem:feasible`, and of the variance paragraph before `d12-spin-eq:variance-x`.
It is independent of the finite Vandermonde identities of `FamilyFeasible`
(`vandermonde_mass/first/second`, `betaBinom_sum/first/second`, `famNu_sum`, `famNu_mean`,
`famNu_second_moment`), which are kept as a cross-check; every theorem here has a distinct name
(suffix `_beta`) and the same statement as its Vandermonde counterpart.

The integral identity used is Euler's beta integral (DLMF 5.12.1), in the form
`∫_{(0,1)} θ^(a-1) (1-θ)^(b-1) dθ = B(a,b) = Γ(a)Γ(b)/Γ(a+b)` for `a, b > 0`
(`integral_Ioo_eulerW`, obtained from Mathlib's `ProbabilityTheory.beta_eq_betaIntegralReal` and
`Complex.betaIntegral_convergent`; the same chain as Mathlib's `lintegral_betaPDF_eq_one`).
With `α = χ(1+a)/2`, `β = χ(1-a)/2` it gives
`ν_j = ∫_0^1 C(12,j) θ^j (1-θ)^(12-j) θ^(α-1)(1-θ)^(β-1)/B(α,β) dθ`
(`eulerBinom_eq_integral`), identified with the rising-factorial form through
`Γ(x+n) = Γ(x)(x)_n` (`gamma_add_nat`, `eulerBinom_eq_betaBinom`).  Summing the binomial
probabilities under the integral (`sum_eulerBinom_poly`, `binom_poly_one`) gives
`∑ν_j = 1`; the conditional mean `2θ-1` gives `∑x_jν_j = 2α/(α+β)-1 = a`; the conditional variance
decomposition `E[x² | θ] = m² + (1-m²)/12`, `m = 2θ-1`, together with
`Var(2θ-1) = (1-a²)/(χ+1)` gives the second moment.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MeasureTheory Set
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

def eulerW (a b x : ℝ) : ℝ := x ^ (a - 1) * (1 - x) ^ (b - 1)

theorem integral_Ioo_eulerW {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Ioo (0:ℝ) 1, eulerW a b x = ProbabilityTheory.beta a b := by
  unfold eulerW
  rw [ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb, Complex.betaIntegral,
    intervalIntegral.integral_of_le (by norm_num),
    ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx₂⟩ ↦ ?_
    norm_cast
    rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
      Complex.re_mul_ofReal, Complex.ofReal_re]
    all_goals linarith
  · convert! Complex.betaIntegral_convergent (u := a) (v := b) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]

theorem integrableOn_eulerW {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (eulerW a b) (Ioo (0:ℝ) 1) := by
  have h := Complex.betaIntegral_convergent (u := (a:ℂ)) (v := (b:ℂ)) (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp)] at h
  have h2 := h.re
  refine (h2.mono_set Ioo_subset_Ioc_self).congr_fun (fun x hx => ?_) measurableSet_Ioo
  obtain ⟨hx1, hx2⟩ := hx
  unfold eulerW
  have e : ((x:ℂ) ^ ((a:ℂ) - 1) * (1 - (x:ℂ)) ^ ((b:ℂ) - 1)) =
    (((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ)) : ℂ) := by
    push_cast
    rw [Complex.ofReal_cpow hx1.le, Complex.ofReal_cpow (by linarith)]
    push_cast; ring
  simp only [e]
  simp


theorem eulerW_shift {a b : ℝ} (i k : ℕ) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    x ^ i * (1 - x) ^ k * eulerW a b x = eulerW (a + i) (b + k) x := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : 0 < 1 - x := by linarith
  unfold eulerW
  have e1 : x ^ (a + i - 1) = x ^ i * x ^ (a - 1) := by
    rw [show a + i - 1 = (a - 1) + i by ring, Real.rpow_add h0, Real.rpow_natCast]; ring
  have e2 : (1 - x) ^ (b + k - 1) = (1 - x) ^ k * (1 - x) ^ (b - 1) := by
    rw [show b + k - 1 = (b - 1) + k by ring, Real.rpow_add h1', Real.rpow_natCast]; ring
  rw [e1, e2]; ring

theorem integral_poly_eulerW {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i k : ℕ) :
    ∫ x in Ioo (0:ℝ) 1, x ^ i * (1 - x) ^ k * eulerW a b x =
      ProbabilityTheory.beta (a + i) (b + k) := by
  rw [← integral_Ioo_eulerW (by positivity) (by positivity)]
  exact setIntegral_congr_fun measurableSet_Ioo (fun x hx => eulerW_shift i k hx)

theorem integrableOn_poly_eulerW {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ i * (1 - x) ^ k * eulerW a b x) (Ioo (0:ℝ) 1) :=
  (integrableOn_eulerW (a := a + i) (b := b + k) (by positivity) (by positivity)).congr_fun
    (fun x hx => (eulerW_shift i k hx).symm) measurableSet_Ioo

theorem gamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * risingProd x n := by
  induction n with
  | zero => simp [risingProd]
  | succ n ih =>
    have hpos : 0 < x + n := by positivity
    rw [show x + ((n + 1 : ℕ) : ℝ) = (x + n) + 1 by push_cast; ring,
      Real.Gamma_add_one hpos.ne', ih]
    unfold risingProd
    rw [Finset.prod_range_succ]
    ring

theorem beta_shift_ratio {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {j : ℕ} (hj : j ≤ 12) :
    ProbabilityTheory.beta (α + j) (β + ((12 - j : ℕ) : ℝ)) / ProbabilityTheory.beta α β =
      risingProd α j * risingProd β (12 - j) / risingProd (α + β) 12 := by
  have h3 : (α + j) + (β + ((12 - j : ℕ) : ℝ)) = (α + β) + ((12 : ℕ) : ℝ) := by
    have : ((12 - j : ℕ) : ℝ) = 12 - j := by rw [Nat.cast_sub hj]; norm_num
    rw [this]; push_cast; ring
  have hs : 0 < α + β := add_pos hα hβ
  have g1 := Real.Gamma_pos_of_pos hα
  have g2 := Real.Gamma_pos_of_pos hβ
  have g3 := Real.Gamma_pos_of_pos hs
  have r1 := risingProd_pos hα j
  have r2 := risingProd_pos hβ (12 - j)
  have r3 := risingProd_pos hs 12
  unfold ProbabilityTheory.beta
  rw [h3, gamma_add_nat hα, gamma_add_nat hβ, gamma_add_nat hs]
  field_simp


/-- Euler-route beta-binomial probability: `C(12,j) B(α+j, β+12-j) / B(α,β)`. -/
def eulerBinom (α β : ℝ) (j : ℕ) : ℝ :=
  ((12).choose j : ℝ) * ProbabilityTheory.beta (α + j) (β + ((12 - j : ℕ) : ℝ)) /
    ProbabilityTheory.beta α β

/-- Agreement of the Euler-integral form with the rising-factorial form. -/
theorem eulerBinom_eq_betaBinom {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {j : ℕ} (hj : j ≤ 12) :
    eulerBinom α β j = betaBinom α β j := by
  unfold eulerBinom betaBinom
  rw [mul_div_assoc, beta_shift_ratio hα hβ hj]
  ring

theorem eulerBinom_eq_integral {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (j : ℕ) :
    eulerBinom α β j =
      (∫ x in Ioo (0:ℝ) 1, ((12).choose j : ℝ) * (x ^ j * (1 - x) ^ (12 - j) * eulerW α β x)) /
        ProbabilityTheory.beta α β := by
  rw [integral_const_mul, integral_poly_eulerW hα hβ]
  unfold eulerBinom
  ring

/-- Summing binomial probabilities under the Euler integral. -/
theorem sum_eulerBinom_poly {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (c : ℕ → ℝ) (P : ℝ → ℝ)
    (hP : ∀ x ∈ Ioo (0:ℝ) 1,
      ∑ j ∈ Finset.range 13, c j * (((12).choose j : ℝ) * (x ^ j * (1 - x) ^ (12 - j))) = P x) :
    ∑ j ∈ Finset.range 13, c j * eulerBinom α β j =
      (∫ x in Ioo (0:ℝ) 1, P x * eulerW α β x) / ProbabilityTheory.beta α β := by
  have hint : ∀ j ∈ Finset.range 13, IntegrableOn
      (fun x : ℝ => c j * (((12).choose j : ℝ) * (x ^ j * (1 - x) ^ (12 - j) * eulerW α β x)))
      (Ioo (0:ℝ) 1) := by
    intro j _
    exact ((integrableOn_poly_eulerW hα hβ j (12 - j)).const_mul _).const_mul _
  have h1 : ∑ j ∈ Finset.range 13, c j * eulerBinom α β j =
      (∑ j ∈ Finset.range 13,
        ∫ x in Ioo (0:ℝ) 1,
          c j * (((12).choose j : ℝ) * (x ^ j * (1 - x) ^ (12 - j) * eulerW α β x))) /
        ProbabilityTheory.beta α β := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_const_mul, mul_div_assoc, ← eulerBinom_eq_integral hα hβ]
  rw [h1, ← integral_finsetSum _ hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  rw [← hP x hx, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring


theorem integral_moment_eulerW {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (i : ℕ) :
    ∫ x in Ioo (0:ℝ) 1, x ^ i * eulerW α β x = ProbabilityTheory.beta (α + i) β := by
  simpa using integral_poly_eulerW hα hβ i 0

theorem integrableOn_moment_eulerW {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (i : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ i * eulerW α β x) (Ioo (0:ℝ) 1) := by
  simpa using integrableOn_poly_eulerW hα hβ i 0

/-- `B(α+i, β)/B(α,β) = (α)_i/(α+β)_i`. -/
theorem beta_moment_ratio {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (i : ℕ) :
    ProbabilityTheory.beta (α + i) β / ProbabilityTheory.beta α β =
      risingProd α i / risingProd (α + β) i := by
  have hs : 0 < α + β := add_pos hα hβ
  have g1 := Real.Gamma_pos_of_pos hα
  have g2 := Real.Gamma_pos_of_pos hβ
  have g3 := Real.Gamma_pos_of_pos hs
  have r3 := risingProd_pos hs i
  unfold ProbabilityTheory.beta
  rw [show α + i + β = (α + β) + i by ring, gamma_add_nat hα, gamma_add_nat hs]
  field_simp

/-- Integral of a quadratic polynomial against the Euler weight. -/
theorem integral_quad_eulerW {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (A B C : ℝ) :
    ∫ x in Ioo (0:ℝ) 1, (A * x ^ 2 + B * x + C) * eulerW α β x =
      A * ProbabilityTheory.beta (α + 2) β + B * ProbabilityTheory.beta (α + 1) β +
        C * ProbabilityTheory.beta α β := by
  have i2 := integrableOn_moment_eulerW hα hβ 2
  have i1 := integrableOn_moment_eulerW hα hβ 1
  have i0 := integrableOn_moment_eulerW hα hβ 0
  have m2 := integral_moment_eulerW hα hβ 2
  have m1 := integral_moment_eulerW hα hβ 1
  have m0 := integral_moment_eulerW hα hβ 0
  simp only [pow_zero, one_mul, Nat.cast_zero, add_zero, pow_one, Nat.cast_one,
    Nat.cast_ofNat] at i2 i1 i0 m2 m1 m0
  have e : (fun x : ℝ => (A * x ^ 2 + B * x + C) * eulerW α β x) =
      fun x => A * (x ^ 2 * eulerW α β x) + B * (x * eulerW α β x) + C * eulerW α β x := by
    funext x; ring
  have h12 : IntegrableOn (fun x : ℝ => A * (x ^ 2 * eulerW α β x) + B * (x * eulerW α β x))
      (Ioo (0:ℝ) 1) := (i2.const_mul A).add (i1.const_mul B)
  rw [e, integral_add h12 (i0.const_mul C),
    integral_add (i2.const_mul A) (i1.const_mul B), integral_const_mul, integral_const_mul,
    integral_const_mul, m2, m1, m0]

theorem binom_poly_one (x : ℝ) :
    ∑ j ∈ Finset.range 13, (1 : ℝ) * (((12).choose j : ℝ) * (x ^ j * (1 - x) ^ (12 - j))) = 1 := by
  have h := add_pow x (1 - x) 12
  rw [show x + (1 - x) = 1 by ring, one_pow] at h
  refine Eq.trans (Finset.sum_congr rfl (fun j _ => ?_)) h.symm
  ring

/-- Euler-integral proof of normalisation (replaces `vandermonde_mass`/`betaBinom_sum`). -/
theorem betaBinom_sum_beta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ j ∈ Finset.range 13, betaBinom α β j = 1 := by
  have h := sum_eulerBinom_poly hα hβ (fun _ => 1) (fun _ => 1)
    (fun x _ => binom_poly_one x)
  have hB := ProbabilityTheory.beta_pos hα hβ
  simp only [one_mul] at h
  rw [integral_Ioo_eulerW hα hβ, div_self hB.ne'] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  exact (eulerBinom_eq_betaBinom hα hβ (by have := Finset.mem_range.mp hj; omega)).symm


theorem ratio_one {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ProbabilityTheory.beta (α + 1) β / ProbabilityTheory.beta α β = α / (α + β) := by
  have := beta_moment_ratio hα hβ 1
  simpa [risingProd] using this

theorem ratio_two {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ProbabilityTheory.beta (α + 2) β / ProbabilityTheory.beta α β =
      α * (α + 1) / ((α + β) * (α + β + 1)) := by
  have := beta_moment_ratio hα hβ 2
  simpa [risingProd, Finset.prod_range_succ] using this

/-- Euler-integral proof of the first moment `E j = 12 α/(α+β)` (conditional mean `12 θ`). -/
theorem betaBinom_first_beta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ j ∈ Finset.range 13, (j : ℝ) * betaBinom α β j = 12 * α / (α + β) := by
  have h := sum_eulerBinom_poly hα hβ (fun j => (j : ℝ)) (fun x => 0 * x ^ 2 + 12 * x + 0)
    (fun x _ => by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [Nat.choose]
      ring)
  rw [integral_quad_eulerW hα hβ] at h
  have hB := ProbabilityTheory.beta_pos hα hβ
  have r1 := ratio_one hα hβ
  have hs : 0 < α + β := add_pos hα hβ
  have : ∑ j ∈ Finset.range 13, (j : ℝ) * betaBinom α β j =
      ∑ j ∈ Finset.range 13, (j : ℝ) * eulerBinom α β j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [eulerBinom_eq_betaBinom hα hβ (by have := Finset.mem_range.mp hj; omega)]
  rw [this, h]
  field_simp at r1 ⊢
  nlinarith [r1]

/-- Conditional mean of the spin average is `2θ-1`: `E[x] = 2α/(α+β) - 1`. -/
theorem betaBinom_spin_mean_beta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ j ∈ Finset.range 13, ((2 * (j : ℝ) - 12) / 12) * betaBinom α β j = (α - β) / (α + β) := by
  have h := sum_eulerBinom_poly hα hβ (fun j => (2 * (j : ℝ) - 12) / 12)
    (fun x => 0 * x ^ 2 + 2 * x + (-1))
    (fun x _ => by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [Nat.choose]
      ring)
  rw [integral_quad_eulerW hα hβ] at h
  have hB := ProbabilityTheory.beta_pos hα hβ
  have r1 := ratio_one hα hβ
  have hs : 0 < α + β := add_pos hα hβ
  have : ∑ j ∈ Finset.range 13, ((2 * (j : ℝ) - 12) / 12) * betaBinom α β j =
      ∑ j ∈ Finset.range 13, ((2 * (j : ℝ) - 12) / 12) * eulerBinom α β j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [eulerBinom_eq_betaBinom hα hβ (by have := Finset.mem_range.mp hj; omega)]
  rw [this, h]
  field_simp at r1 ⊢
  nlinarith [r1]

/-- Conditional-variance decomposition: given `θ`, the twelve spins are independent with
bias `m = 2θ-1`, so `E[x² | θ] = m² + (1-m²)/12`; hence
`E x² = (11 E[m²] + 1)/12` with `E[m²] = 4 E θ² - 4 E θ + 1`. -/
theorem betaBinom_spin_second_beta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ j ∈ Finset.range 13, ((2 * (j : ℝ) - 12) / 12) ^ 2 * betaBinom α β j =
      (11 * (4 * (α * (α + 1) / ((α + β) * (α + β + 1))) - 4 * (α / (α + β)) + 1) + 1) / 12 := by
  have h := sum_eulerBinom_poly hα hβ (fun j => ((2 * (j : ℝ) - 12) / 12) ^ 2)
    (fun x => (11 / 3) * x ^ 2 + (-(11 / 3)) * x + 1)
    (fun x _ => by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [Nat.choose]
      ring)
  rw [integral_quad_eulerW hα hβ] at h
  have hB := ProbabilityTheory.beta_pos hα hβ
  have r1 := ratio_one hα hβ
  have r2 := ratio_two hα hβ
  have hs : 0 < α + β := add_pos hα hβ
  have : ∑ j ∈ Finset.range 13, ((2 * (j : ℝ) - 12) / 12) ^ 2 * betaBinom α β j =
      ∑ j ∈ Finset.range 13, ((2 * (j : ℝ) - 12) / 12) ^ 2 * eulerBinom α β j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [eulerBinom_eq_betaBinom hα hβ (by have := Finset.mem_range.mp hj; omega)]
  rw [this, h]
  have e : ((11 / 3) * ProbabilityTheory.beta (α + 2) β +
      (-(11 / 3)) * ProbabilityTheory.beta (α + 1) β + 1 * ProbabilityTheory.beta α β) /
        ProbabilityTheory.beta α β =
      (11 / 3) * (ProbabilityTheory.beta (α + 2) β / ProbabilityTheory.beta α β) -
        (11 / 3) * (ProbabilityTheory.beta (α + 1) β / ProbabilityTheory.beta α β) + 1 := by
    field_simp
    ring
  rw [e, r1, r2]
  have : 0 < α + β + 1 := by linarith
  field_simp
  ring

/-- Variance of the conditional bias: `Var(2θ-1) = 4αβ/((α+β)²(α+β+1))`. -/
theorem beta_bias_variance {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (4 * (α * (α + 1) / ((α + β) * (α + β + 1))) - 4 * (α / (α + β)) + 1) -
        ((α - β) / (α + β)) ^ 2 = 4 * α * β / ((α + β) ^ 2 * (α + β + 1)) := by
  have hs : 0 < α + β := add_pos hα hβ
  have : 0 < α + β + 1 := by linarith
  field_simp
  ring


/-- Euler route to the Vandermonde identity of order twelve (agreement with `vandermonde_mass`
for positive parameters). -/
theorem vandermonde_mass_of_beta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∑ j ∈ Finset.range 13, ((12).choose j : ℝ) * risingProd α j * risingProd β (12 - j) =
      risingProd (α + β) 12 := by
  have hpos : 0 < risingProd (α + β) 12 := risingProd_pos (add_pos hα hβ) 12
  have h := betaBinom_sum_beta hα hβ
  unfold betaBinom at h
  rw [← Finset.sum_div, div_eq_one_iff_eq hpos.ne'] at h
  exact h

/-! ### The family `ν(t)`, `p(t)` by the Euler route -/

theorem famNu_eq_eulerBinom {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (j : Count) :
    famNu t j = eulerBinom (famAlpha t) (famBeta t) j.val := by
  rw [famNu_eq_betaBinom ht0 ht1,
    eulerBinom_eq_betaBinom (famAlpha_pos ht0 ht1) (famBeta_pos ht0 ht1)
      (by have := j.isLt; omega)]

/-- `ν_j` as the integral of the conditional binomial probability against the `Beta(α,β)` law. -/
theorem famNu_eq_integral {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (j : Count) :
    famNu t j =
      (∫ θ in Ioo (0 : ℝ) 1, ((12).choose j.val : ℝ) *
          (θ ^ j.val * (1 - θ) ^ (12 - j.val) * eulerW (famAlpha t) (famBeta t) θ)) /
        ProbabilityTheory.beta (famAlpha t) (famBeta t) := by
  rw [famNu_eq_eulerBinom ht0 ht1,
    eulerBinom_eq_integral (famAlpha_pos ht0 ht1) (famBeta_pos ht0 ht1)]

/-- Agreement of the two routes: the Euler-integral probabilities sum to the same total as `famNu`. -/
theorem sum_eulerBinom_eq_sum_famNu {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∑ j : Count, eulerBinom (famAlpha t) (famBeta t) j.val = ∑ j : Count, famNu t j :=
  (Finset.sum_congr rfl (fun j _ => (famNu_eq_eulerBinom ht0 ht1 j).symm))

/-- Normalisation of `ν` via Euler's beta integral. -/
theorem famNu_sum_beta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ∑ j : Count, famNu t j = 1 := by
  simp_rw [famNu_eq_betaBinom ht0 ht1]
  rw [Fin.sum_univ_eq_sum_range (fun j => betaBinom (famAlpha t) (famBeta t) j) 13]
  exact betaBinom_sum_beta (famAlpha_pos ht0 ht1) (famBeta_pos ht0 ht1)

/-- Mean of `ν` via the conditional mean `2θ-1`: `∑ x_j ν_j = 2α/(α+β) - 1 = a`. -/
theorem famNu_mean_beta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∑ j : Count, meanCoordinate j * famNu t j = famBias t := by
  have hχ := famChi_pos ht0 ht1
  have e : ∀ j : Count, meanCoordinate j * famNu t j =
      ((2 * (j.val : ℝ) - 12) / 12) * betaBinom (famAlpha t) (famBeta t) j.val := by
    intro j
    rw [famNu_eq_betaBinom ht0 ht1, meanCoordinate_eq_real]
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ((2 * (j : ℝ) - 12) / 12) * betaBinom (famAlpha t) (famBeta t) j) 13,
    betaBinom_spin_mean_beta (famAlpha_pos ht0 ht1) (famBeta_pos ht0 ht1),
    famAlpha_add_famBeta]
  unfold famAlpha famBeta
  field_simp
  ring

/-- `Var(2θ-1) = (1-a²)/(χ+1)` for `θ ~ Beta(α,β)` (the variance of the conditional spin bias). -/
theorem famBias_variance_beta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (4 * (famAlpha t * (famAlpha t + 1) / (famChi t * (famChi t + 1))) -
        4 * (famAlpha t / famChi t) + 1) - famBias t ^ 2 =
      (1 - famBias t ^ 2) / (famChi t + 1) := by
  have hχ := famChi_pos ht0 ht1
  have h := beta_bias_variance (famAlpha_pos ht0 ht1) (famBeta_pos ht0 ht1)
  rw [famAlpha_add_famBeta] at h
  have hm : (famAlpha t - famBeta t) / famChi t = famBias t := by
    unfold famAlpha famBeta; field_simp; ring
  rw [hm] at h
  rw [h]
  have hχ1 : 0 < famChi t + 1 := by linarith
  unfold famAlpha famBeta
  field_simp
  ring

/-- Second moment of the spin average under `ν` by conditional-variance decomposition:
`E x² = (11 E[m²] + 1)/12`, `E[m²] = a² + (1-a²)/(χ+1)`. -/
theorem famNu_second_moment_beta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∑ j : Count, meanCoordinate j ^ 2 * famNu t j =
      famBias t ^ 2 + (1 - famBias t ^ 2) * (famChi t + 12) / (12 * (famChi t + 1)) := by
  have hχ := famChi_pos ht0 ht1
  have e : ∀ j : Count, meanCoordinate j ^ 2 * famNu t j =
      ((2 * (j.val : ℝ) - 12) / 12) ^ 2 * betaBinom (famAlpha t) (famBeta t) j.val := by
    intro j
    rw [famNu_eq_betaBinom ht0 ht1, meanCoordinate_eq_real]
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ((2 * (j : ℝ) - 12) / 12) ^ 2 * betaBinom (famAlpha t) (famBeta t) j) 13,
    betaBinom_spin_second_beta (famAlpha_pos ht0 ht1) (famBeta_pos ht0 ht1),
    famAlpha_add_famBeta]
  have hV := famBias_variance_beta ht0 ht1
  have hE : 4 * (famAlpha t * (famAlpha t + 1) / (famChi t * (famChi t + 1))) -
        4 * (famAlpha t / famChi t) + 1 = famBias t ^ 2 + (1 - famBias t ^ 2) / (famChi t + 1) := by
    linarith
  rw [hE]
  have hχ1 : 0 < famChi t + 1 := by linarith
  field_simp
  ring

theorem famLaw_sum_beta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ∑ j : Count, famLaw t j = 1 :=
  famLaw_sum_of_nu (famNu_sum_beta ht0 ht1)

theorem famLaw_mean_beta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : mean (famLaw t) = t :=
  famLaw_mean_of_nu ht0 (famNu_mean_beta ht0 ht1)

/-- Lemma 5.19 feasibility with the written route throughout: Euler beta integral for mass and
mean, `log(1+u) ≤ u` and Jensen for the state-zero cap. -/
theorem famLaw_feasibleAt_beta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    FeasibleAt t (famLaw t) :=
  famLaw_feasibleAt_of_parts ht0 ht1 (famLaw_sum_beta ht0 ht1) (famLaw_mean_beta ht0 ht1)
    (famLaw_zero_state_lt_jensen ht0 ht1)

/-- `d12-spin-eq:variance-x` with the conditional-variance route. -/
theorem famSpinVar_eq_formula_beta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    famSpinVar t = famVarFormula t :=
  famSpinVar_eq_formula_of_moments ht0 ht1 (famLaw_sum_beta ht0 ht1) (famLaw_mean_beta ht0 ht1)
    (famNu_second_moment_beta ht0 ht1)

theorem famSpinVar_pos_beta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < famSpinVar t := by
  rw [famSpinVar_eq_formula_beta ht0 ht1]
  exact famVarFormula_pos ht0 ht1

/-- Feasibility for `0 ≤ t < 1` (at `t = 0` the fair vector), written route. -/
theorem famLaw_feasibleAt_of_nonneg_beta {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    FeasibleAt t (famLaw t) := by
  rcases ht0.eq_or_lt with h | h
  · subst h; rw [famLaw_zero]; exact reference_feasibleAt
  · exact famLaw_feasibleAt_beta h ht1

theorem famSpinVar_pos_of_nonneg_beta {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < famSpinVar t := by
  rcases ht0.eq_or_lt with h | h
  · subst h; rw [famSpinVar_zero]; norm_num
  · exact famSpinVar_pos_beta h ht1

end BecknerOnofri.V2.FiniteState
