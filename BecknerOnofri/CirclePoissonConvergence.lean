import BecknerOnofri.CirclePoissonProbability
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! A uniform quantitative approach to the constant density as the Poisson
radius tends to zero. This is a value estimate, not yet smooth convergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson

local instance : (AddCircle.haarAddCircle (T:=1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T:=1)=(volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T:=1)).symm
  rw [he]
  infer_instance

theorem kernel_deviation (q : ℝ) (hq : 0≤q) (hq1 : q≤1/2) (x : UnitAddCircle) :
    |kernel q x-1|≤12*q := by
  have hq' : q<1 := by linarith
  have hc : |(fourier 1 x).re|≤1 := by
    simpa only [fourier_apply,Circle.norm_coe] using Complex.abs_re_le_norm (fourier 1 x)
  have hc' := abs_le.mp hc
  let d := 1-2*q*(fourier 1 x).re+q^2
  have hd : 0<d := denominator_pos q hq hq' x
  have hd4 : (1/4:ℝ)≤d := by
    dsimp only [d]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hc'.2),sq_nonneg (q-1/2)]
  have he : kernel q x-1=(2*q*((fourier 1 x).re-q))/d := by
    change (1-q^2)/d-1=_
    rw [div_sub_one hd.ne']
    congr 1
    dsimp only [d]
    ring
  rw [he,abs_div,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hnum : |2*q*((fourier 1 x).re-q)|≤3*q := by
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hq (sub_nonneg.mpr hc'.2),
      mul_nonneg hq (by linarith [hc'.1] : 0≤(fourier 1 x).re+1),
      mul_nonneg hq (by linarith : 0≤1/2-q)]
  nlinarith [mul_le_mul_of_nonneg_left hd4 hq]

theorem smoothing_deviation (q : ℝ) (hq : 0≤q) (hq1 : q≤1/2)
    (p : UnitAddCircle → ℝ) (hp : Continuous p) (hn : ∀ x,0≤p x)
    (hm : (∫ x,p x ∂AddCircle.haarAddCircle)=1) (x : UnitAddCircle) :
    |smoothing q p x-1|≤12*q := by
  have hq' : q<1 := by linarith
  have hpc : Continuous (fun y => p (x-y)) := hp.comp (continuous_const.sub continuous_id)
  have hpi : Integrable (fun y => p (x-y)) AddCircle.haarAddCircle :=
    hpc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hki : Integrable (fun y => kernel q y*p (x-y)) AddCircle.haarAddCircle :=
    ((kernel_continuous q hq hq').mul hpc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun y => (kernel q y-1)*p (x-y)) AddCircle.haarAddCircle :=
    (((kernel_continuous q hq hq').sub continuous_const).mul hpc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hm' : (∫ y,p (x-y) ∂AddCircle.haarAddCircle)=1 := by
    rw [integral_sub_left_eq_self,hm]
  have he : smoothing q p x-1=
      ∫ y,(kernel q y-1)*p (x-y) ∂AddCircle.haarAddCircle := by
    simp_rw [sub_mul,one_mul]
    rw [integral_sub hki hpi,hm']
    rfl
  rw [he]
  calc
    _ ≤ ∫ y,‖(kernel q y-1)*p (x-y)‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y,(12*q)*p (x-y) ∂AddCircle.haarAddCircle := by
      apply integral_mono hi.norm (hpi.const_mul (12*q))
      intro y
      change ‖(kernel q y-1)*p (x-y)‖≤12*q*p (x-y)
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hn (x-y))]
      exact mul_le_mul_of_nonneg_right (kernel_deviation q hq hq1 y) (hn (x-y))
    _ = _ := by rw [integral_const_mul,hm',mul_one]

#print axioms smoothing_deviation
end BecknerOnofri.HighDim.CirclePoisson
