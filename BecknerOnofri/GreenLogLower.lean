module

public import BecknerOnofri.GreenFirstImageLower
public import BecknerOnofri.E1LogLower
public import BecknerOnofri.RadialGreenE1

@[expose] public section

/-! Matching logarithmic lower estimate for the actual heat-Mellin Green function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Legacy.TorusEndpoint
namespace BecknerOnofri.AdamsEndpoint
open Legacy.BecknerOnofri GreenHeatPointwise

theorem reciprocal_integral_cutoff {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    (∫ t in Ioo (0 : ℝ) T, LogGaussianIntegral.integrand A t) =
      HighDim.RadialE1.E1 (A / T) := by
  have himage : (fun t : ℝ => A/t) '' Ioo (0 : ℝ) T = Ioi (A/T) := by
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact div_lt_div_of_pos_left hA ht.1 ht.2
    · intro hy
      have hyp : 0 < y := (div_pos hA hT).trans hy
      refine ⟨A/y, ⟨div_pos hA hyp, ?_⟩, ?_⟩
      · apply (div_lt_iff₀ hyp).mpr
        have hh := (div_lt_iff₀ hT).mp hy
        nlinarith
      · field_simp
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      HasDerivWithinAt (fun s : ℝ => A/s) (-A/t^2) (Ioo (0 : ℝ) T) t := by
    convert! ((hasDerivAt_const t A).div (hasDerivAt_id t) ht.1.ne').hasDerivWithinAt using 1 <;> simp
  have hinj : InjOn (fun t : ℝ => A/t) (Ioo (0 : ℝ) T) := by
    intro s hs t ht he
    have hh := (div_eq_div_iff hs.1.ne' ht.1.ne').mp he
    exact (mul_left_cancel₀ hA.ne' hh).symm
  have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj
    (fun t : ℝ => Real.exp (-t)/t)
  rw [himage] at hh
  rw [HighDim.RadialE1.E1,hh]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [abs_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hA) (sq_pos_of_pos ht.1))]
  simp only [smul_eq_mul,neg_div,neg_neg,LogGaussianIntegral.integrand]
  field_simp [hA.ne',ht.1.ne']

theorem small_integral_lower {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (hx0 : x ≠ 0) :
    HighDim.RadialE1.E1 (4 * Real.pi * coordinateRadiusSq x) -
      (∫ t in Ioo 0 (1/4), t^((d : ℝ)/2-1)) ≤
      ∫ t in Ioo 0 (1/4), heatMellin (fun i => (x i : UnitAddCircle)) t := by
  have hA : 0 < Real.pi * coordinateRadiusSq x :=
    mul_pos Real.pi_pos (coordinateRadiusSq_pos hx0)
  have hh := integral_mono_ae
    ((LogGaussianIntegral.integrable hA (by norm_num : (0 : ℝ) ≤ 1/4)).sub
      (integrable_smallPower hd)) (integrable_heatMellin_small hd x hx hx0)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact heatMellin_first_image_lower ht.1 x)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (LogGaussianIntegral.integrable hA (by norm_num))
    (integrable_smallPower hd), reciprocal_integral_cutoff hA (by norm_num)] at hh
  convert hh using 1 <;> congr 2 <;> ring

def logarithmicLowerConstant (d : ℕ) : ℝ :=
  lowerConstant d + (Real.log (4 * Real.pi) + 1) / 2

theorem heatGreen_log_lower {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (hx0 : x ≠ 0) :
    -Real.log (Real.sqrt (coordinateRadiusSq x)) - logarithmicLowerConstant d ≤
      heatGreen (fun i => (x i : UnitAddCircle)) := by
  have hr := coordinateRadiusSq_pos hx0
  have hs := small_integral_lower hd x hx hx0
  have he := HighDim.RadialE1.logarithmic_lower (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos) hr)
  have ht := (abs_le.mp (tail_integral_abs_le hd (fun i => (x i : UnitAddCircle)))).1
  rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos).ne' hr.ne'] at he
  rw [Real.log_sqrt hr.le]
  unfold heatGreen logarithmicLowerConstant lowerConstant
  rw [heatMellin_integral_split hd x hx hx0]
  linarith

#print axioms heatGreen_log_lower
end BecknerOnofri.AdamsEndpoint
