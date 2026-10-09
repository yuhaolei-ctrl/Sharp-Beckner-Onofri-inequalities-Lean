module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import BecknerOnofri.V2.ThetaTail.ZetaBridge

@[expose] public section

/-! # The sinh product and the logarithmic inequalities of Appendix A.1

For `y > 0`:  `y²/6 - y⁴/180 ≤ log(sinh y / y) ≤ y²/6`, from Euler's product
`sinh y / y = ∏_{m≥1} (1 + y²/(π² m²))` (obtained from `Complex.tendsto_euler_sin_prod` at
`z = i y / π`) and `y - y²/2 ≤ log(1+y) ≤ y`; then, for `x > 0`,

* `(d12-tail-eq:loglower)`: `-log(1 - e^{-x}) ≤ -log x + x/2 - x²/24 + x⁴/2880`;
* `log(1 - e^{-4x}) ≤ log(4x) - 2x + 2x²/3`. -/
noncomputable section
open Finset Filter Topology
namespace BecknerOnofri.V2.ThetaTail

/-- the factor `1 + y²/(π² (j+1)²)` -/
def sinhFactor (y : ℝ) (j : ℕ) : ℝ := 1 + y ^ 2 / (Real.pi ^ 2 * ((j : ℝ) + 1) ^ 2)

theorem tendsto_sinh_prod (y : ℝ) (hy : y ≠ 0) :
    Tendsto (fun n : ℕ => ∏ j ∈ range n, sinhFactor y j) atTop (𝓝 (Real.sinh y / y)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := Complex.tendsto_euler_sin_prod (Complex.I * (y : ℂ) / Real.pi)
  have e1 : (Real.pi : ℂ) * (Complex.I * (y : ℂ) / Real.pi) = (y : ℂ) * Complex.I := by
    field_simp
  have hprod : ∀ n : ℕ, (Real.pi : ℂ) * (Complex.I * (y : ℂ) / Real.pi)
      * ∏ j ∈ range n, ((1 : ℂ) - (Complex.I * (y : ℂ) / Real.pi) ^ 2 / ((j : ℂ) + 1) ^ 2)
      = (y : ℂ) * Complex.I * ((∏ j ∈ range n, sinhFactor y j : ℝ) : ℂ) := by
    intro n
    rw [e1]
    congr 1
    push_cast
    refine prod_congr rfl fun j _ => ?_
    unfold sinhFactor
    push_cast
    have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    field_simp
    rw [Complex.I_sq]
    ring
  have h' : Tendsto (fun n : ℕ => (y : ℂ) * Complex.I * ((∏ j ∈ range n, sinhFactor y j : ℝ) : ℂ))
      atTop (𝓝 (Complex.sinh (y : ℂ) * Complex.I)) := by
    have := h.congr (fun n => hprod n)
    rwa [e1, Complex.sin_mul_I] at this
  have h2 := h'.const_mul (((y : ℂ) * Complex.I)⁻¹)
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
  have e2 : ((y : ℂ) * Complex.I)⁻¹ * ((Complex.sinh (y : ℂ)) * Complex.I)
      = ((Real.sinh y / y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sinh]
    push_cast
    field_simp
  have e3 : ∀ n : ℕ, ((y : ℂ) * Complex.I)⁻¹ * ((y : ℂ) * Complex.I *
      ((∏ j ∈ range n, sinhFactor y j : ℝ) : ℂ)) = ((∏ j ∈ range n, sinhFactor y j : ℝ) : ℂ) := by
    intro n
    field_simp
  have h3 : Tendsto (fun n : ℕ => ((∏ j ∈ range n, sinhFactor y j : ℝ) : ℂ)) atTop
      (𝓝 ((Real.sinh y / y : ℝ) : ℂ)) := by
    have := h2.congr (fun n => e3 n)
    rwa [e2] at this
  have h4 := (Complex.continuous_re.tendsto _).comp h3
  simp only [Function.comp_def, Complex.ofReal_re] at h4
  exact h4

lemma sinhFactor_pos (y : ℝ) (j : ℕ) : 0 < sinhFactor y j := by
  unfold sinhFactor; positivity

lemma hasSum_sinh_u (y : ℝ) :
    HasSum (fun j : ℕ => y ^ 2 / (Real.pi ^ 2 * ((j : ℝ) + 1) ^ 2)) (y ^ 2 / 6) := by
  have h := (summable_zetaTerm (p := 2) le_rfl).hasSum
  have hz : zetaR 2 = Real.pi ^ 2 / 6 := zetaR_two
  unfold zetaR at hz
  rw [hz] at h
  have := h.mul_left (y ^ 2 / Real.pi ^ 2)
  convert this using 1
  · ext j
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  · have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp

lemma hasSum_sinh_u_sq (y : ℝ) :
    HasSum (fun j : ℕ => (y ^ 2 / (Real.pi ^ 2 * ((j : ℝ) + 1) ^ 2)) ^ 2) (y ^ 4 / 90) := by
  have h := (summable_zetaTerm (p := 4) (by norm_num)).hasSum
  have hz : zetaR 4 = Real.pi ^ 4 / 90 := zetaR_four
  unfold zetaR at hz
  rw [hz] at h
  have := h.mul_left (y ^ 4 / Real.pi ^ 4)
  convert this using 1
  · ext j
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  · have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp

theorem log_sinh_div_le (y : ℝ) (hy : 0 < y) :
    Real.log (Real.sinh y / y) ≤ y ^ 2 / 6 := by
  have hT := tendsto_sinh_prod y hy.ne'
  have hpos : 0 < Real.sinh y / y := div_pos (Real.sinh_pos_iff.mpr hy) hy
  have hL := (Real.continuousAt_log hpos.ne').tendsto.comp hT
  refine le_of_tendsto hL (Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply]
  rw [Real.log_prod (fun j _ => (sinhFactor_pos y j).ne')]
  have hs := hasSum_sinh_u y
  calc ∑ j ∈ range n, Real.log (sinhFactor y j)
      ≤ ∑ j ∈ range n, y ^ 2 / (Real.pi ^ 2 * ((j : ℝ) + 1) ^ 2) := by
        refine sum_le_sum fun j _ => ?_
        unfold sinhFactor
        have := Real.log_le_sub_one_of_pos (sinhFactor_pos y j)
        unfold sinhFactor at this
        linarith
    _ ≤ y ^ 2 / 6 := sum_le_hasSum _ (fun j _ => by positivity) hs

lemma sub_sq_half_le_log (u : ℝ) (hu : 0 ≤ u) : u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  have h := Real.le_log_one_add_of_nonneg hu
  have h2 : u - u ^ 2 / 2 ≤ 2 * u / (u + 2) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [pow_nonneg hu 3, sq_nonneg u]
  linarith

theorem log_sinh_div_ge (y : ℝ) (hy : 0 < y) :
    y ^ 2 / 6 - y ^ 4 / 180 ≤ Real.log (Real.sinh y / y) := by
  have hT := tendsto_sinh_prod y hy.ne'
  have hpos : 0 < Real.sinh y / y := div_pos (Real.sinh_pos_iff.mpr hy) hy
  have hL := (Real.continuousAt_log hpos.ne').tendsto.comp hT
  have h1 := hasSum_sinh_u y
  have h2 := hasSum_sinh_u_sq y
  have hlow : HasSum (fun j : ℕ => (y ^ 2 / (Real.pi ^ 2 * ((j : ℝ) + 1) ^ 2))
      - (y ^ 2 / (Real.pi ^ 2 * ((j : ℝ) + 1) ^ 2)) ^ 2 / 2) (y ^ 2 / 6 - y ^ 4 / 180) := by
    have := h1.sub (h2.div_const 2)
    convert this using 1
    ring
  have hlim := hlow.tendsto_sum_nat
  refine le_of_tendsto_of_tendsto hlim hL (Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply]
  rw [Real.log_prod (fun j _ => (sinhFactor_pos y j).ne')]
  refine sum_le_sum fun j _ => ?_
  unfold sinhFactor
  exact sub_sq_half_le_log _ (by positivity)

/-! ### the two logarithmic inequalities -/

lemma one_sub_exp_neg_eq (x : ℝ) (hx : 0 < x) :
    1 - Real.exp (-x) = x * Real.exp (-(x / 2)) * (Real.sinh (x / 2) / (x / 2)) := by
  have h1 : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.sinh (x / 2) = (Real.exp (x / 2) - Real.exp (-(x / 2))) / 2 := Real.sinh_eq _
  have h3 : Real.exp (-(x / 2)) * Real.exp (x / 2) = 1 := by
    rw [← Real.exp_add]; simp
  rw [h1, h2]
  field_simp
  nlinarith [h3]

theorem neg_log_one_sub_exp_neg_le (x : ℝ) (hx : 0 < x) :
    -Real.log (1 - Real.exp (-x)) ≤ -Real.log x + x / 2 - x ^ 2 / 24 + x ^ 4 / 2880 := by
  have hy : 0 < x / 2 := by positivity
  have hr : 0 < Real.sinh (x / 2) / (x / 2) := div_pos (Real.sinh_pos_iff.mpr hy) hy
  have hpos : 0 < 1 - Real.exp (-x) := by
    have : Real.exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have := log_sinh_div_ge (x / 2) hy
  have hlog : Real.log (1 - Real.exp (-x)) =
      Real.log x + (-(x / 2)) + Real.log (Real.sinh (x / 2) / (x / 2)) := by
    rw [one_sub_exp_neg_eq x hx, Real.log_mul (by positivity) hr.ne',
      Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [hlog]
  nlinarith [this]

theorem log_one_sub_exp_neg_four_le (x : ℝ) (hx : 0 < x) :
    Real.log (1 - Real.exp (-(4 * x))) ≤ Real.log (4 * x) - 2 * x + 2 * x ^ 2 / 3 := by
  have h4 : 0 < 4 * x := by positivity
  have hy : 0 < 2 * x := by positivity
  have hr : 0 < Real.sinh (2 * x) / (2 * x) := div_pos (Real.sinh_pos_iff.mpr hy) hy
  have e := one_sub_exp_neg_eq (4 * x) h4
  have h24 : 4 * x / 2 = 2 * x := by ring
  rw [h24] at e
  have := log_sinh_div_le (2 * x) hy
  have hlog : Real.log (1 - Real.exp (-(4 * x))) =
      Real.log (4 * x) + (-(2 * x)) + Real.log (Real.sinh (2 * x) / (2 * x)) := by
    rw [e, Real.log_mul (by positivity) hr.ne', Real.log_mul h4.ne' (Real.exp_pos _).ne',
      Real.log_exp]
  rw [hlog]
  nlinarith [this]

end BecknerOnofri.V2.ThetaTail
