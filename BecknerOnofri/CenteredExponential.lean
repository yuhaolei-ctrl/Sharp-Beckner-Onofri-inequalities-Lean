module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

@[expose] public section

/-! An actual second-order exponential moment bound for bounded real random variables. -/

noncomputable section
open MeasureTheory
open scoped Interval

namespace BecknerOnofri.HighDim

theorem exp_le_quadratic_of_abs_le {x C : ℝ} (hC : 0 ≤ C) (hxC : |x| ≤ C) :
    Real.exp x ≤ 1 + x + (Real.exp C / 2) * x ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  have hx' : (0 : ℝ) ≠ x := Ne.symm hx
  have hu := uniqueDiffOn_uIcc hx'
  have hd : derivWithin Real.exp (Set.uIcc 0 x) 0 = 1 := by
    simpa using (Real.hasDerivAt_exp 0).hasDerivWithinAt.derivWithin
      (hu 0 (Set.left_mem_uIcc))
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) (f := Real.exp) hx' Real.contDiff_exp.contDiffOn
  have htaylor : taylorWithinEval Real.exp 1 (Set.uIcc 0 x) 0 x = 1 + x := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, taylorWithinEval_succ]
    simp [hd]
  rw [htaylor] at heq
  have hderiv : iteratedDeriv 2 Real.exp = Real.exp := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    simp [Real.deriv_exp]
  rw [hderiv] at heq
  norm_num at heq
  have hyC : y ≤ C := by
    have hymax := hy.2
    have hxle : x ≤ C := (abs_le.mp hxC).2
    exact le_trans hymax.le (max_le hC hxle)
  have hexp := Real.exp_le_exp.mpr hyC
  have hmul := mul_le_mul_of_nonneg_right hexp (sq_nonneg x)
  nlinarith

theorem integrable_exp_of_ae_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w : Ω → ℝ} {B : ℝ}
    (hw : AEStronglyMeasurable w μ) (hbound : ∀ᵐ x ∂μ, |w x| ≤ B) :
    Integrable (fun x => Real.exp (w x)) μ := by
  apply Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable hw) (Real.exp B)
  filter_upwards [hbound] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans hx)

theorem integrable_sq_of_ae_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w : Ω → ℝ} {B : ℝ}
    (hw : AEStronglyMeasurable w μ) (hbound : ∀ᵐ x ∂μ, |w x| ≤ B) :
    Integrable (fun x => (w x) ^ 2) μ := by
  apply Integrable.of_bound (hw.pow 2) (B ^ 2)
  filter_upwards [hbound] with x hx
  have hs := mul_self_le_mul_self (abs_nonneg (w x)) hx
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (w x)), ← pow_two, sq_abs] using hs

theorem centered_exponential_variance_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (B : ℝ)
    (hw : AEStronglyMeasurable w μ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ, |w x| ≤ B) :
    Real.log (∫ x, Real.exp (w x) ∂μ) ≤
      (∫ x, w x ∂μ) + (Real.exp (2 * B) / 2) * ProbabilityTheory.variance w μ := by
  let m : ℝ := ∫ x, w x ∂μ
  let u : Ω → ℝ := fun x => w x - m
  let A : ℝ := Real.exp (2 * B) / 2
  have hwint : Integrable w μ :=
    Integrable.of_bound hw B (by simpa only [Real.norm_eq_abs] using hbound)
  have hm : |m| ≤ B := by
    simpa [m, Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (f := w) (μ := μ) (C := B)
        (by simpa only [Real.norm_eq_abs] using hbound))
  have hum : AEStronglyMeasurable u μ := hw.sub aestronglyMeasurable_const
  have hu : ∀ᵐ x ∂μ, |u x| ≤ 2 * B := by
    filter_upwards [hbound] with x hx
    dsimp [u]
    calc
      |w x - m| ≤ |w x| + |m| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have huint : Integrable u μ := hwint.sub (integrable_const m)
  have huexpint := integrable_exp_of_ae_abs_le hum hu
  have husqint := integrable_sq_of_ae_abs_le hum hu
  have huzero : (∫ x, u x ∂μ) = 0 := by
    dsimp [u]
    rw [integral_sub hwint (integrable_const m)]
    simp [m]
  have hi : (∫ x, Real.exp (u x) ∂μ) ≤ 1 + A * ∫ x, (u x) ^ 2 ∂μ := by
    have ht : (fun x => Real.exp (u x)) ≤ᵐ[μ]
        (fun x => 1 + u x + A * (u x) ^ 2) := by
      filter_upwards [hu] with x hx
      exact exp_le_quadratic_of_abs_le (by positivity) hx
    have hint := ((integrable_const 1).add huint).add (husqint.const_mul A)
    have h := integral_mono_ae huexpint hint ht
    rw [integral_add' ((integrable_const 1).add huint) (husqint.const_mul A),
      integral_add' (integrable_const 1) huint, integral_const_mul, huzero] at h
    simpa using h
  have hlog : Real.log (∫ x, Real.exp (u x) ∂μ) ≤ A * ∫ x, (u x) ^ 2 ∂μ := by
    have h := Real.log_le_sub_one_of_pos (integral_exp_pos huexpint)
    linarith
  have hexp : (∫ x, Real.exp (w x) ∂μ) =
      Real.exp m * ∫ x, Real.exp (u x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  rw [hexp, Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos huexpint).ne',
    Real.log_exp]
  rw [ProbabilityTheory.variance_eq_integral hw.aemeasurable]
  change m + Real.log (∫ x, Real.exp (u x) ∂μ) ≤ m + A * ∫ x, (u x) ^ 2 ∂μ
  linarith

end BecknerOnofri.HighDim
