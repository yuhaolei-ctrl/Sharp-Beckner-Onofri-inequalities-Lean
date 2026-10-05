module

public import Legacy.TorusEndpoint.AbsolutePhysicalFourier
public import Legacy.TorusEndpoint.TorusHeatBounds
public import Legacy.TorusEndpoint.GreenKernelReal
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

/-!
# Actual heat regularizations and their L2 limit

The Gaussian-damped Green multiplier is absolutely summable. Its continuous
Fourier series and L2 representative have the actual stated coefficients.
The L2 convergence below uses square summability of the critical multiplier,
not absolute summability of the undamped Green Fourier series.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Legacy.TorusEndpoint.GreenHeatRegularization

open TorusHeatBounds GreenMultiplierSummability GreenKernelReal

theorem heatWeight_le_one {d : ℕ} {t : ℝ} (ht : 0 ≤ t) (k : Frequency d) :
    heatWeight t k ≤ 1 := by
  unfold heatWeight
  apply Real.exp_le_one_iff.mpr
  have h := mul_nonneg (mul_nonneg Real.pi_pos.le ht) (radiusSq_nonneg k)
  nlinarith

noncomputable def heatGreenWeight (d : ℕ) (t : ℝ) (k : Frequency d) : ℝ :=
  greenMultiplier d k * heatWeight t k

theorem heatGreenWeight_norm_summable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (fun k => ‖heatGreenWeight d t k‖) := by
  have hs := ((summable_greenMultiplier_sq d).add (heatWeight_summable (d := d) ht)).div_const 2
  apply hs.of_nonneg_of_le (fun k => norm_nonneg _)
  intro k
  have hw := heatWeight_pos t k
  have hw1 := heatWeight_le_one ht.le k
  have h := sq_nonneg (|greenMultiplier d k| - heatWeight t k)
  have hsq := sq_abs (greenMultiplier d k)
  have hwq : heatWeight t k ^ 2 ≤ heatWeight t k := by nlinarith
  change ‖greenMultiplier d k * heatWeight t k‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hw.le]
  nlinarith

theorem heatGreenWeight_complex_norm_summable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (fun k => ‖(heatGreenWeight d t k : ℂ)‖) := by
  simpa only [Complex.norm_real] using heatGreenWeight_norm_summable (d := d) ht

noncomputable def heatGreenKernel (d : ℕ) (t : ℝ) : Torus d → ℂ :=
  absoluteFourierSeries (fun k => (heatGreenWeight d t k : ℂ))

theorem heatGreenKernel_continuous {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Continuous (heatGreenKernel d t) :=
  absoluteFourierSeries_continuous _ (heatGreenWeight_complex_norm_summable ht)

theorem heatGreenKernel_memLp {d : ℕ} {t : ℝ} (ht : 0 < t) :
    MemLp (heatGreenKernel d t) 2 (torusMeasure d) :=
  (heatGreenKernel_continuous ht).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem heatGreenKernel_fourierCoeff {d : ℕ} {t : ℝ} (ht : 0 < t) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (heatGreenKernel d t) k = (heatGreenWeight d t k : ℂ) :=
  absoluteFourierSeries_coefficient _ (heatGreenWeight_complex_norm_summable ht) k

noncomputable def heatGreenLp {d : ℕ} {t : ℝ} (ht : 0 < t) : Lp ℂ 2 (torusMeasure d) :=
  (heatGreenKernel_memLp ht).toLp (heatGreenKernel d t)

theorem heatGreenLp_coe_ae {d : ℕ} {t : ℝ} (ht : 0 < t) :
    heatGreenLp (d := d) ht =ᵐ[torusMeasure d] heatGreenKernel d t :=
  (heatGreenKernel_memLp ht).coeFn_toLp

theorem heatGreenLp_fourierCoeff {d : ℕ} {t : ℝ} (ht : 0 < t) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (heatGreenLp ht) k = (heatGreenWeight d t k : ℂ) := by
  rw [← heatGreenKernel_fourierCoeff ht k]
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [heatGreenLp_coe_ae ht] with x hx
  rw [hx]

theorem L2_norm_sq_eq_tsum_fourier {d : ℕ} (f : Lp ℂ 2 (torusMeasure d)) :
    ‖f‖ ^ 2 = ∑' k, ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
  let e := (UnitAddTorus.mFourierBasis (d := Fin d)).repr
  calc
    _ = ‖e f‖ ^ 2 := congrArg (fun r : ℝ => r ^ 2) (e.norm_map f).symm
    _ = ∑' k : Frequency d, ‖e f k‖ ^ 2 := by
      have h := lp.norm_rpow_eq_tsum (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num) (e f)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
    _ = _ := by
      apply tsum_congr
      intro k
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (UnitAddTorus.mFourierBasis_repr f k)

theorem heatGreenLp_sub_fourierCoeff {d : ℕ} {t : ℝ} (ht : 0 < t) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff ((heatGreenLp (d := d) ht - greenL2 d) : Lp ℂ 2 (torusMeasure d)) k =
      ((greenMultiplier d k * (heatWeight t k - 1) : ℝ) : ℂ) := by
  calc
    _ = UnitAddTorus.mFourierBasis.repr (heatGreenLp (d := d) ht - greenL2 d) k :=
      (UnitAddTorus.mFourierBasis_repr (heatGreenLp (d := d) ht - greenL2 d) k).symm
    _ = UnitAddTorus.mFourierCoeff (heatGreenLp ht) k -
        UnitAddTorus.mFourierCoeff (greenL2 d) k := by
      have hm := congrArg (fun a : lp (fun _ : Frequency d => ℂ) 2 => a k)
        ((UnitAddTorus.mFourierBasis (d := Fin d)).repr.map_sub
          (heatGreenLp (d := d) ht) (greenL2 d))
      exact hm.trans (congrArg₂ (fun a b : ℂ => a - b)
        (UnitAddTorus.mFourierBasis_repr (heatGreenLp (d := d) ht) k)
        (UnitAddTorus.mFourierBasis_repr (greenL2 d) k))
    _ = _ := by
      rw [heatGreenLp_fourierCoeff ht, greenL2_fourierCoeff]
      unfold heatGreenWeight
      push_cast
      ring

theorem heatWeight_tendsto_one {d : ℕ} {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (k : Frequency d) :
    Tendsto (fun n => heatWeight (t n) k) atTop (𝓝 1) := by
  have h := ((ht.const_mul (-Real.pi)).mul_const (radiusSq k)).rexp
  simpa only [mul_zero, zero_mul, Real.exp_zero, heatWeight] using h

theorem heatGreenLp_tendsto {d : ℕ} (t : ℕ → ℝ) (hpos : ∀ n, 0 < t n)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => heatGreenLp (d := d) (hpos n)) atTop (𝓝 (greenL2 d)) := by
  have hpt (k : Frequency d) : Tendsto
      (fun n => ‖greenMultiplier d k * (heatWeight (t n) k - 1)‖ ^ 2) atTop (𝓝 0) := by
    have h := (((heatWeight_tendsto_one ht k).sub_const 1).const_mul
      (greenMultiplier d k)).norm.pow 2
    simpa only [sub_self, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h
  have hbound : ∀ᶠ n in atTop, ∀ k : Frequency d,
      ‖‖greenMultiplier d k * (heatWeight (t n) k - 1)‖ ^ 2‖ ≤ greenMultiplier d k ^ 2 := by
    apply Eventually.of_forall
    intro n k
    have hw := heatWeight_pos (t n) k
    have hw1 := heatWeight_le_one (hpos n).le k
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow, Real.norm_eq_abs,
      sq_abs, Real.norm_eq_abs, sq_abs]
    have hsq : (heatWeight (t n) k - 1) ^ 2 ≤ 1 := by nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (sq_nonneg (greenMultiplier d k))
  have hsum := tendsto_tsum_of_dominated_convergence (summable_greenMultiplier_sq d) hpt hbound
  have hsq : Tendsto (fun n => ‖heatGreenLp (d := d) (hpos n) - greenL2 d‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [L2_norm_sq_eq_tsum_fourier, heatGreenLp_sub_fourierCoeff,
      Complex.norm_real, tsum_zero] using hsum
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, Function.comp_def] using h

end Legacy.TorusEndpoint.GreenHeatRegularization
