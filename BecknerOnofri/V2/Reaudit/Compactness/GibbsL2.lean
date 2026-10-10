module

public import BecknerOnofri.V2.Reaudit.Compactness.Limit

@[expose] public section

/-! # Gibbs densities converge to `1` in `L²` when the potentials tend to `0`

Manuscript (Section 4, proof of `prop:section4-first-order-coexistence`, exclusion of the zero limit):
"Suppose `u_0 = 0`.  Taking `p = 4` gives `\sup_n ∫ e^{4 u_n} < ∞`
(`eq:section4-uniform-fourth-exponential-moment`).  Since `u_n → 0` almost everywhere, this makes
`(e^{u_n} - 1)²` uniformly integrable.  Vitali's theorem therefore gives
`ρ_n = e^{u_n}/∫ e^{u_n} → 1` in `L²(m_{11})`" (`eq:section4-rho-n-to-one-L2`).

This module proves that statement for a sequence of admissible `L²` potentials with a uniform
fourth exponential moment, almost everywhere convergence to `0`, and converging partition
functions (the latter is already Vitali's theorem for `e^{u_n}`, proved in `Limit.lean`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace BecknerOnofri.V2.Reaudit.Compactness
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

variable {d : ℕ}

theorem aestronglyMeasurable_comp_re (U : TorusL2 d) {g : ℝ → ℝ} (hg : Continuous g) :
    AEStronglyMeasurable (fun x => g (U x).re) (torusMeasure d) :=
  (hg.comp Complex.continuous_re).comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)

theorem sq_sub_one_pow_four_le {a : ℝ} (ha : 0 ≤ a) : ((a - 1) ^ 2) ^ 2 ≤ 8 * (a ^ 4 + 1) := by
  nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (a - 1), sq_nonneg a, mul_nonneg ha (sq_nonneg (a - 1)),
    sq_nonneg (a ^ 2 + a), sq_nonneg (a ^ 2 - a)]

/-- **`eq:section4-rho-n-to-one-L2`.**  Admissible `L²` potentials with `∫ e^{4 Re U_n} ≤ M`, `Re U_n → 0`
almost everywhere and `∫ e^{Re U_n} → 1` have Gibbs densities `e^{Re U_n}/∫ e^{Re U_n} → 1` in `L²`. -/
theorem gibbs_sq_tendsto_zero {b Ab M : ℝ} (hR : RoughExponentialBound d b Ab) {U : ℕ → TorusL2 d}
    (hU : ∀ n, Admissible (U n))
    (h4 : ∀ n, ∫ x, Real.exp (4 * (U n x).re) ∂torusMeasure d ≤ M)
    (hae : ∀ᵐ x ∂torusMeasure d, Tendsto (fun n => (U n x).re) atTop (𝓝 0))
    (hZ : Tendsto (fun n => partition (U n)) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, (Real.exp ((U n x).re) / partition (U n) - 1) ^ 2 ∂torusMeasure d)
      atTop (𝓝 0) := by
  -- measurability and integrability facts
  have hmeas : ∀ (n : ℕ) (p : ℝ), AEStronglyMeasurable (fun x => Real.exp (p * (U n x).re))
      (torusMeasure d) := fun n p => aestronglyMeasurable_exp_re (U n) p
  have hint : ∀ (n : ℕ) (p : ℝ), 0 < p →
      Integrable (fun x => Real.exp (p * (U n x).re)) (torusMeasure d) :=
    fun n p hp => rough_integrable hR (hU n) hp
  have hint1 : ∀ n, Integrable (fun x => Real.exp ((U n x).re)) (torusMeasure d) := fun n => by
    simpa using hint n 1 one_pos
  -- `(e^u - 1)²` has an integrable square, bounded by `8 (e^{4u} + 1)`
  have hsqint : ∀ n, Integrable (fun x => ((Real.exp ((U n x).re) - 1) ^ 2) ^ 2) (torusMeasure d) := by
    intro n
    have hb : Integrable (fun x => 8 * (Real.exp (4 * (U n x).re) + 1)) (torusMeasure d) :=
      ((hint n 4 (by norm_num)).add (integrable_const 1)).const_mul 8
    refine hb.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact aestronglyMeasurable_comp_re (U n) (g := fun t => ((Real.exp t - 1) ^ 2) ^ 2) (by fun_prop)
    · have h := sq_sub_one_pow_four_le (Real.exp_pos ((U n x).re)).le
      have e4 : Real.exp ((U n x).re) ^ 4 = Real.exp (4 * (U n x).re) := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [e4] at h
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h
  have hsqbound : ∀ n, ∫ x, ((Real.exp ((U n x).re) - 1) ^ 2) ^ 2 ∂torusMeasure d ≤ 8 * (M + 1) := by
    intro n
    have hb : Integrable (fun x => 8 * (Real.exp (4 * (U n x).re) + 1)) (torusMeasure d) :=
      ((hint n 4 (by norm_num)).add (integrable_const 1)).const_mul 8
    calc ∫ x, ((Real.exp ((U n x).re) - 1) ^ 2) ^ 2 ∂torusMeasure d
        ≤ ∫ x, 8 * (Real.exp (4 * (U n x).re) + 1) ∂torusMeasure d := by
          refine integral_mono (hsqint n) hb fun x => ?_
          have h := sq_sub_one_pow_four_le (Real.exp_pos ((U n x).re)).le
          have e4 : Real.exp ((U n x).re) ^ 4 = Real.exp (4 * (U n x).re) := by
            rw [← Real.exp_nat_mul]; norm_num
          rw [e4] at h
          exact h
      _ = 8 * (∫ x, Real.exp (4 * (U n x).re) ∂torusMeasure d + 1) := by
          rw [integral_const_mul, integral_add (hint n 4 (by norm_num)) (integrable_const 1)]
          simp
      _ ≤ 8 * (M + 1) := by
          have := h4 n; linarith
  -- Vitali for `(e^{u_n} - 1)²`
  have hI : Tendsto (fun n => ∫ x, (Real.exp ((U n x).re) - 1) ^ 2 ∂torusMeasure d) atTop (𝓝 0) := by
    have := tendsto_integral_of_sq_bound (μ := torusMeasure d)
      (f := fun n x => (Real.exp ((U n x).re) - 1) ^ 2) (g := fun _ => (0 : ℝ))
      (fun n => aestronglyMeasurable_comp_re (U n) (g := fun t => (Real.exp t - 1) ^ 2) (by fun_prop))
      hsqint (8 * (M + 1)) hsqbound (integrable_const 0)
      (by
        filter_upwards [hae] with x hx
        have h1 : Tendsto (fun n => Real.exp ((U n x).re)) atTop (𝓝 (Real.exp 0)) :=
          (Real.continuous_exp.tendsto _).comp hx
        have h2 := ((h1.sub_const 1).pow 2)
        simpa using h2)
    simpa using this
  -- the partition functions are positive and tend to `1`
  have hZpos : ∀ n, 0 < partition (U n) := fun n => partition_pos hR (hU n)
  have hZone : Tendsto (fun n => ((1 - partition (U n)) / partition (U n)) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (1 - partition (U n)) / partition (U n)) atTop
        (𝓝 ((1 - 1) / 1)) := (tendsto_const_nhds.sub hZ).div hZ one_ne_zero
    simpa using h1.pow 2
  have hrecip : Tendsto (fun n => 2 / partition (U n) ^ 2) atTop (𝓝 2) := by
    have h1 : Tendsto (fun n => partition (U n) ^ 2) atTop (𝓝 (1 ^ 2)) := hZ.pow 2
    convert (tendsto_const_nhds (x := (2 : ℝ))).div h1 (by norm_num) using 2
    norm_num
  have hbound : Tendsto (fun n => 2 / partition (U n) ^ 2 *
      (∫ x, (Real.exp ((U n x).re) - 1) ^ 2 ∂torusMeasure d) +
        2 * ((1 - partition (U n)) / partition (U n)) ^ 2) atTop (𝓝 0) := by
    have := (hrecip.mul hI).add (hZone.const_mul 2)
    simpa using this
  refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hbound
  -- pointwise bound and integration
  have hZn := hZpos n
  have hsq1 : Integrable (fun x => (Real.exp ((U n x).re) - 1) ^ 2) (torusMeasure d) := by
    refine ((hsqint n).add (integrable_const (1 : ℝ))).mono' (aestronglyMeasurable_comp_re (U n)
      (g := fun t => (Real.exp t - 1) ^ 2) (by fun_prop)) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Pi.add_apply]
    nlinarith [sq_nonneg ((Real.exp ((U n x).re) - 1) ^ 2 - 1)]
  have hrhs : Integrable (fun x => 2 / partition (U n) ^ 2 * (Real.exp ((U n x).re) - 1) ^ 2 +
      2 * ((1 - partition (U n)) / partition (U n)) ^ 2) (torusMeasure d) :=
    (hsq1.const_mul _).add (integrable_const _)
  have hpt : ∀ x, (Real.exp ((U n x).re) / partition (U n) - 1) ^ 2 ≤
      2 / partition (U n) ^ 2 * (Real.exp ((U n x).re) - 1) ^ 2 +
        2 * ((1 - partition (U n)) / partition (U n)) ^ 2 := by
    intro x
    set Z := partition (U n)
    set a := Real.exp ((U n x).re)
    have e : a / Z - 1 = (a - 1) / Z + (1 - Z) / Z := by field_simp; ring
    rw [e]
    have h2 : ((a - 1) / Z + (1 - Z) / Z) ^ 2 ≤
        2 * ((a - 1) / Z) ^ 2 + 2 * ((1 - Z) / Z) ^ 2 := by
      nlinarith [sq_nonneg ((a - 1) / Z - (1 - Z) / Z)]
    calc _ ≤ _ := h2
      _ = _ := by rw [div_pow]; ring
  have hlhs : Integrable (fun x => (Real.exp ((U n x).re) / partition (U n) - 1) ^ 2)
      (torusMeasure d) := by
    refine hrhs.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact aestronglyMeasurable_comp_re (U n)
        (g := fun t => (Real.exp t / partition (U n) - 1) ^ 2) (by fun_prop)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt x
  calc ∫ x, (Real.exp ((U n x).re) / partition (U n) - 1) ^ 2 ∂torusMeasure d
      ≤ ∫ x, (2 / partition (U n) ^ 2 * (Real.exp ((U n x).re) - 1) ^ 2 +
        2 * ((1 - partition (U n)) / partition (U n)) ^ 2) ∂torusMeasure d :=
        integral_mono hlhs hrhs hpt
    _ = _ := by
        rw [integral_add (hsq1.const_mul _) (integrable_const _), integral_const_mul]
        simp

end BecknerOnofri.V2.Reaudit.Compactness
