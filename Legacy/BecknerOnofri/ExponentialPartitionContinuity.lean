module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Quantitative exponential partition continuity from actual square-integrability. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Legacy.BecknerOnofri.ExponentialPartitionContinuity

theorem exp_sub_le (x y : ℝ) : Real.exp x - Real.exp y ≤ (x-y)*Real.exp x := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y-x)) (Real.exp_nonneg x)
  rw [← Real.exp_add] at hh
  have he : x + (y-x) = y := by ring
  rw [he] at hh
  nlinarith

theorem abs_exp_sub_le (x y : ℝ) :
    |Real.exp x-Real.exp y| ≤ |x-y| *(Real.exp x+Real.exp y) := by
  apply abs_le.mpr
  constructor
  · have hh := exp_sub_le y x
    have hbound := mul_le_mul_of_nonneg_right (le_abs_self (y-x)) (Real.exp_nonneg y)
    rw [abs_sub_comm y x] at hbound
    have hp := mul_nonneg (abs_nonneg (x-y)) (Real.exp_nonneg x)
    nlinarith
  · have hh := exp_sub_le x y
    have hbound := mul_le_mul_of_nonneg_right (le_abs_self (x-y)) (Real.exp_nonneg x)
    have hp := mul_nonneg (abs_nonneg (x-y)) (Real.exp_nonneg y)
    nlinarith

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_norm_sq_Lp (u : Lp ℂ 2 μ) : ∫ x, ‖u x‖^2 ∂μ = ‖u‖^2 := by
  simpa only [L2.inner_def, real_inner_self_eq_norm_sq] using (real_inner_self_eq_norm_sq u)

theorem integral_sq_toLp {f : X → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, f x^2 ∂μ = ‖hf.toLp f‖^2 := by
  have hh := real_inner_self_eq_norm_sq (hf.toLp f)
  rw [L2.inner_def] at hh
  calc
    _ = ∫ x, inner ℝ ((hf.toLp f) x) ((hf.toLp f) x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      simp [hx]
    _ = _ := hh

theorem integral_mul_le_sqrt {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, f x*g x ∂μ ≤ Real.sqrt (∫ x, f x^2 ∂μ) * Real.sqrt (∫ x, g x^2 ∂μ) := by
  have hh := real_inner_le_norm (hf.toLp f) (hg.toLp g)
  rw [L2.inner_def] at hh
  have he : (∫ x, f x*g x ∂μ) =
      ∫ x, inner ℝ ((hf.toLp f) x) ((hg.toLp g) x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]
  rw [he, integral_sq_toLp hf, integral_sq_toLp hg, Real.sqrt_sq_eq_abs,
    Real.sqrt_sq_eq_abs, abs_norm, abs_norm]
  exact hh

theorem exp_memLp_two (u : Lp ℂ 2 μ)
    (hu : Integrable (fun x => Real.exp (2*(u x).re)) μ) :
    MemLp (fun x => Real.exp (u x).re) 2 μ := by
  apply (memLp_two_iff_integrable_sq (Real.continuous_exp.comp_aestronglyMeasurable
    (Complex.continuous_re.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)))).mpr
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hu

theorem integral_norm_sub_sq (u v : Lp ℂ 2 μ) :
    (∫ x, ‖u x-v x‖^2 ∂μ) = ‖u-v‖^2 := by
  rw [← integral_norm_sq_Lp (u-v)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v] with x hx
  simp only [hx, Pi.sub_apply]

theorem integral_norm_sub_mul_exp_le (u v w : Lp ℂ 2 μ)
    (hw : Integrable (fun x => Real.exp (2*(w x).re)) μ) :
    (∫ x, ‖u x-v x‖ * Real.exp (w x).re ∂μ) ≤
      ‖u-v‖ * Real.sqrt (∫ x, Real.exp (2*(w x).re) ∂μ) := by
  have hn : MemLp (fun x => ‖u x-v x‖) 2 μ := by
    simpa only [Pi.sub_apply] using ((Lp.memLp u).sub (Lp.memLp v)).norm
  have hh := integral_mul_le_sqrt hn (exp_memLp_two w hw)
  rw [integral_norm_sub_sq, Real.sqrt_sq_eq_abs, abs_norm] at hh
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hh

theorem partition_difference_bound [IsFiniteMeasure μ] (u v : Lp ℂ 2 μ)
    (hu : Integrable (fun x => Real.exp (2*(u x).re)) μ)
    (hv : Integrable (fun x => Real.exp (2*(v x).re)) μ) :
    |(∫ x, Real.exp (u x).re ∂μ) - (∫ x, Real.exp (v x).re ∂μ)| ≤
      ‖u-v‖ * (Real.sqrt (∫ x, Real.exp (2*(u x).re) ∂μ) +
        Real.sqrt (∫ x, Real.exp (2*(v x).re) ∂μ)) := by
  have hu2 := exp_memLp_two u hu
  have hv2 := exp_memLp_two v hv
  have hu1 := hu2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hv1 := hv2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hn : MemLp (fun x => ‖u x-v x‖) 2 μ := by
    simpa only [Pi.sub_apply] using ((Lp.memLp u).sub (Lp.memLp v)).norm
  have hnu := hn.integrable_mul hu2
  have hnv := hn.integrable_mul hv2
  rw [← integral_sub hu1 hv1]
  calc
    _ ≤ ∫ x, |Real.exp (u x).re-Real.exp (v x).re| ∂μ :=
      by simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun x => Real.exp (u x).re-Real.exp (v x).re) (μ := μ))
    _ ≤ ∫ x, ‖u x-v x‖ * (Real.exp (u x).re+Real.exp (v x).re) ∂μ := by
      apply integral_mono_ae (hu1.sub hv1).norm (hn.integrable_mul (hu2.add hv2))
      filter_upwards [] with x
      apply (abs_exp_sub_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (u x-v x)
    _ = (∫ x, ‖u x-v x‖ * Real.exp (u x).re ∂μ) +
        (∫ x, ‖u x-v x‖ * Real.exp (v x).re ∂μ) := by
      simp_rw [mul_add]
      exact integral_add hnu hnv
    _ ≤ _ := by
      have h1 := integral_norm_sub_mul_exp_le u v u hu
      have h2 := integral_norm_sub_mul_exp_le u v v hv
      nlinarith

#print axioms partition_difference_bound

end Legacy.BecknerOnofri.ExponentialPartitionContinuity
