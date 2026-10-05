module

public import Legacy.TorusEndpoint.GreenMellinPairing

@[expose] public section

/-!
# A genuine almost-everywhere lower bound for the torus Green function

The actual L2 Green representative is tested against all nonnegative L2
functions. The heat lower estimates are combined into one integrable Gamma
majorant in time, and the previously proved actual Mellin pairing identifies
the result. No common lower bound for finite Fourier sums is assumed.
-/

open MeasureTheory Set Filter

namespace Legacy.TorusEndpoint.GreenLowerBound

open TorusHeatPositivity TorusHeatBounds TorusHeatPairing GreenMellinMultiplier
  GreenMellinPairing GreenKernelReal GreenPairing

noncomputable def heatLowerAmplitude (d : ℕ) : ℝ :=
  Real.exp (Real.pi / 2) + heatTailMass d

theorem heatLowerAmplitude_pos (d : ℕ) : 0 < heatLowerAmplitude d :=
  add_pos_of_pos_of_nonneg (Real.exp_pos _) (heatTailMass_nonneg d)

noncomputable def greenLowerConstant (d : ℕ) : ℝ :=
  heatLowerAmplitude d *
    ((1 / (Real.pi / 2)) ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)) / 2

theorem greenLowerConstant_pos {d : ℕ} (hd : 0 < d) : 0 < greenLowerConstant d := by
  unfold greenLowerConstant
  exact div_pos (mul_pos (heatLowerAmplitude_pos d)
    (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr (by positivity)) _)
      (Real.Gamma_pos_of_pos (by positivity)))) (by norm_num)

/-- One decaying lower estimate works at every positive time, with no time split
remaining in the statement. The test need not be normalized to have mass one. -/
theorem real_heat_pairing_all_time_lower_bound {d : ℕ} {t : ℝ} (ht : 0 < t)
    {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d))
    (hpos : ∀ᵐ x ∂torusMeasure d, 0 ≤ f x) :
    -(heatLowerAmplitude d * Real.exp (-Real.pi * t / 2) *
        ∫ x, f x ∂torusMeasure d) ≤
      ∫ x, ((torusTheta t x).re - 1) * f x ∂torusMeasure d := by
  have hmass : 0 ≤ ∫ x, f x ∂torusMeasure d := integral_nonneg_of_ae hpos
  have he : 0 ≤ Real.exp (-Real.pi * t / 2) := (Real.exp_pos _).le
  by_cases ht1 : t ≤ 1
  · have hexp : 1 ≤ Real.exp (Real.pi / 2) * Real.exp (-Real.pi * t / 2) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hcoef : 1 ≤ heatLowerAmplitude d * Real.exp (-Real.pi * t / 2) := by
      have hamp : Real.exp (Real.pi / 2) ≤ heatLowerAmplitude d := by
        dsimp [heatLowerAmplitude]
        exact le_add_of_nonneg_right (heatTailMass_nonneg d)
      exact hexp.trans (mul_le_mul_of_nonneg_right hamp he)
    have hmul := mul_le_mul_of_nonneg_right hcoef hmass
    have hsmall := real_heat_pairing_lower_bound ht hf hpos
    nlinarith
  · have hamp : heatTailMass d ≤ heatLowerAmplitude d := by
      dsimp [heatLowerAmplitude]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hamp he) hmass
    exact (neg_le_neg hmul).trans
      (real_heat_pairing_large_time_lower_bound (le_of_not_ge ht1) hf hpos)

/-- This is a proved inequality for the actual Green function and every actual
nonnegative L2 test, not a lower-bound assumption on an unspecified kernel. -/
theorem realGreen_test_lower_bound {d : ℕ} (hd : 0 < d)
    {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d))
    (hpos : ∀ᵐ x ∂torusMeasure d, 0 ≤ f x) :
    -(greenLowerConstant d * ∫ x, f x ∂torusMeasure d) ≤
      ∫ x, realGreen d x * f x ∂torusMeasure d := by
  have ha : 0 < (d : ℝ) / 2 := by positivity
  have hr : 0 < Real.pi / 2 := by positivity
  have hlo : IntegrableOn (fun t : ℝ =>
      -(heatLowerAmplitude d * ∫ x, f x ∂torusMeasure d) *
        (t ^ ((d : ℝ) / 2 - 1) * Real.exp (-(Real.pi / 2 * t)))) (Ioi 0) :=
    (gamma_integrand_integrable ha hr).const_mul _
  have hm := integral_mono_ae hlo (mellin_heat_pairing_integrable hd hf) ?_
  · rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr,
      realGreen_mellin_heat_pairing hd hf] at hm
    unfold greenLowerConstant
    nlinarith
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have h := mul_le_mul_of_nonneg_left
    (real_heat_pairing_all_time_lower_bound ht hf hpos)
    (Real.rpow_nonneg ht.le ((d : ℝ) / 2 - 1))
  have he : -(Real.pi / 2 * t) = -Real.pi * t / 2 := by ring
  rw [he]
  convert h using 1
  ring

/-- The genuine mean-zero Green representative is bounded below almost
everywhere. This does not assert any bound on its finite Fourier partial sums. -/
theorem realGreen_ae_lower_bound {d : ℕ} (hd : 0 < d) :
    ∀ᵐ x ∂torusMeasure d, -greenLowerConstant d ≤ realGreen d x := by
  apply ae_lower_bound_of_L2_tests (realGreen_memLp d) (greenLowerConstant d)
  intro f hf hpos
  exact realGreen_test_lower_bound hd hf hpos

theorem realGreen_add_constant_nonneg_ae {d : ℕ} (hd : 0 < d) :
    ∀ᵐ x ∂torusMeasure d, 0 ≤ realGreen d x + greenLowerConstant d := by
  filter_upwards [realGreen_ae_lower_bound hd] with x hx
  linarith

end Legacy.TorusEndpoint.GreenLowerBound
