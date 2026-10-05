import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# From polynomial integral bounds to an exponential integral bound

The polynomial inequalities are explicit hypotheses here. They must be
established separately, for example by finite weighted convolution and
Parseval. This module proves the limiting step using pointwise convergence
and Fatou's lemma, with no uniform-convergence premise.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Legacy.TorusEndpoint.ExponentialLimit

set_option maxHeartbeats 800000

lemma norm_exp_sq (z : ℂ) : ‖Complex.exp z‖ ^ 2 = Real.exp (2 * z.re) := by
  rw [Complex.norm_exp, pow_two, ← Real.exp_add, two_mul]

lemma polynomial_norm_sq_tendsto (z : ℂ) :
    Tendsto (fun n : ℕ => ‖(1 + z / n) ^ n‖ ^ 2) atTop
      (𝓝 (Real.exp (2 * z.re))) := by
  simpa only [norm_exp_sq] using (Complex.tendsto_one_add_div_pow_exp z).norm.pow 2

/--
General measure-space version, with all necessary integrability assumptions
explicit. The bound is needed only for positive integers, not for `n = 0`.
-/
theorem integral_exp_le_of_polynomial_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℂ) (B : ℝ)
    (hpoly : ∀ n : ℕ, Integrable (fun x => ‖(1 + F x / n) ^ n‖ ^ 2) μ)
    (hexp : Integrable (fun x => Real.exp (2 * (F x).re)) μ)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (∫ x, ‖(1 + F x / n) ^ n‖ ^ 2 ∂μ) ≤ (1 + B / n) ^ n) :
    (∫ x, Real.exp (2 * (F x).re) ∂μ) ≤ Real.exp B := by
  have hpoint (x : X) :
      Tendsto (fun n : ℕ => ENNReal.ofReal (‖(1 + F x / n) ^ n‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (2 * (F x).re)))) :=
    ENNReal.continuous_ofReal.tendsto _ |>.comp (polynomial_norm_sq_tendsto (F x))
  have hfatou :
      (∫⁻ x, ENNReal.ofReal (Real.exp (2 * (F x).re)) ∂μ) ≤
        liminf (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (‖(1 + F x / n) ^ n‖ ^ 2) ∂μ)
          atTop := by
    calc
      _ = ∫⁻ x, liminf
          (fun n : ℕ => ENNReal.ofReal (‖(1 + F x / n) ^ n‖ ^ 2)) atTop ∂μ := by
        apply lintegral_congr
        intro x
        exact (hpoint x).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' (fun n =>
        (hpoly n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hcomparison :
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ x, ENNReal.ofReal (‖(1 + F x / n) ^ n‖ ^ 2) ∂μ) ≤
          ENNReal.ofReal ((1 + B / n) ^ n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hpoly n)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hbound n hn)
  have hscalar :
      Tendsto (fun n : ℕ => ENNReal.ofReal ((1 + B / n) ^ n)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp B))) :=
    ENNReal.continuous_ofReal.tendsto _ |>.comp (Real.tendsto_one_add_div_pow_exp B)
  have htotal :
      (∫⁻ x, ENNReal.ofReal (Real.exp (2 * (F x).re)) ∂μ) ≤
        ENNReal.ofReal (Real.exp B) := by
    exact hfatou.trans ((liminf_le_liminf hcomparison).trans_eq hscalar.liminf_eq)
  rw [← ofReal_integral_eq_lintegral_ofReal hexp
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))] at htotal
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos B).le).mp htotal

/-- The logarithmic conclusion, with nonzero measure explicitly required. -/
theorem log_integral_exp_le_of_polynomial_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [NeZero μ]
    (F : X → ℂ) (B : ℝ)
    (hpoly : ∀ n : ℕ, Integrable (fun x => ‖(1 + F x / n) ^ n‖ ^ 2) μ)
    (hexp : Integrable (fun x => Real.exp (2 * (F x).re)) μ)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (∫ x, ‖(1 + F x / n) ^ n‖ ^ 2 ∂μ) ≤ (1 + B / n) ^ n) :
    Real.log (∫ x, Real.exp (2 * (F x).re) ∂μ) ≤ B := by
  apply (Real.log_le_iff_le_exp (integral_exp_pos hexp)).mpr
  exact integral_exp_le_of_polynomial_bounds μ F B hpoly hexp hbound

/--
On a compact probability space with measurable open sets, continuity supplies
all integrability hypotheses. The polynomial bounds remain explicit.
-/
theorem continuous_compact_integral_exp_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℂ) (B : ℝ)
    (hF : Continuous F)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (∫ x, ‖(1 + F x / n) ^ n‖ ^ 2 ∂μ) ≤ (1 + B / n) ^ n) :
    (∫ x, Real.exp (2 * (F x).re) ∂μ) ≤ Real.exp B := by
  apply integral_exp_le_of_polynomial_bounds μ F B
  · intro n
    have hc : Continuous (fun x => ‖(1 + F x / n) ^ n‖ ^ 2) :=
      ((continuous_const.add (hF.div_const (n : ℂ))).pow n).norm.pow 2
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hc : Continuous (fun x => Real.exp (2 * (F x).re)) :=
      (continuous_const.mul (Complex.continuous_re.comp hF)).rexp
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hbound

theorem continuous_compact_log_integral_exp_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℂ) (B : ℝ)
    (hF : Continuous F)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (∫ x, ‖(1 + F x / n) ^ n‖ ^ 2 ∂μ) ≤ (1 + B / n) ^ n) :
    Real.log (∫ x, Real.exp (2 * (F x).re) ∂μ) ≤ B := by
  have hc : Continuous (fun x => Real.exp (2 * (F x).re)) :=
    (continuous_const.mul (Complex.continuous_re.comp hF)).rexp
  have hexp : Integrable (fun x => Real.exp (2 * (F x).re)) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply (Real.log_le_iff_le_exp (integral_exp_pos hexp)).mpr
  exact continuous_compact_integral_exp_le μ F B hF hbound

end Legacy.TorusEndpoint.ExponentialLimit

#print axioms Legacy.TorusEndpoint.ExponentialLimit.polynomial_norm_sq_tendsto
#print axioms Legacy.TorusEndpoint.ExponentialLimit.integral_exp_le_of_polynomial_bounds
#print axioms Legacy.TorusEndpoint.ExponentialLimit.log_integral_exp_le_of_polynomial_bounds
#print axioms Legacy.TorusEndpoint.ExponentialLimit.continuous_compact_integral_exp_le
#print axioms Legacy.TorusEndpoint.ExponentialLimit.continuous_compact_log_integral_exp_le
