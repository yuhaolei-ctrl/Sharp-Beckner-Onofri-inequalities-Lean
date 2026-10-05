module

public import BecknerOnofri.CircleVonMisesComparison
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! The actual mean lies in [0,1) for an increasing exponential cosine
profile. The sign comes from half-period pairing; strictness from positivity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem circle_cosine_bound (x : UnitAddCircle) : |(fourier 1 x).re|≤1 :=
  (Complex.abs_re_le_norm _).trans_eq (by simp [fourier_apply])

theorem circle_cosine_half_shift (x : UnitAddCircle) :
    (fourier 1 (x+((1/2:ℝ):UnitAddCircle))).re= -(fourier 1 x).re := by
  have he := congrArg Complex.re (fourier_add_half_inv_index (n:=1) (by norm_num) (by norm_num : (0:ℝ)<1) x)
  simpa using he

theorem circle_mean_nonneg (F : ℝ → ℝ) (hcF : Continuous F)
    (hF : MonotoneOn F (Icc (-1:ℝ) 1)) :
    0≤∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re ∂AddCircle.haarAddCircle := by
  let f : UnitAddCircle → ℝ := fun x => Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re
  let v : UnitAddCircle → ℝ := fun x => Real.exp (F (-(fourier 1 x).re))*(fourier 1 x).re
  have hi : Integrable f AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    dsimp [f]
    fun_prop
  have hv : Integrable v AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    dsimp [v]
    fun_prop
  have htrans := integral_add_right_eq_self (μ:=AddCircle.haarAddCircle) f ((1/2:ℝ):UnitAddCircle)
  have hshift : (fun x => f (x+((1/2:ℝ):UnitAddCircle)))=(fun x => -v x) := by
    funext x
    dsimp only [f,v]
    rw [circle_cosine_half_shift]
    ring
  rw [hshift,integral_neg] at htrans
  have hpoint : ∀ x : UnitAddCircle,0≤f x-v x := by
    intro x
    have hx := abs_le.mp (circle_cosine_bound x)
    have hx' : -(fourier 1 x).re ∈ Icc (-1:ℝ) 1 := ⟨by linarith,by linarith⟩
    change 0≤Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re-
      Real.exp (F (-(fourier 1 x).re))*(fourier 1 x).re
    rw [← sub_mul]
    by_cases hz : 0≤(fourier 1 x).re
    · exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (hF hx' hx (by linarith)))) hz
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (Real.exp_le_exp.mpr (hF hx hx' (by linarith)))) (le_of_not_ge hz)
  have hnon : 0≤∫ x,f x-v x ∂AddCircle.haarAddCircle := integral_nonneg hpoint
  rw [integral_sub hi hv] at hnon
  change 0≤∫ x,f x ∂AddCircle.haarAddCircle
  linarith

theorem circle_mean_lt_one (F : ℝ → ℝ) (hcF : Continuous F)
    (hmass : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re)) ∂AddCircle.haarAddCircle)=1) :
    (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re ∂AddCircle.haarAddCircle)<1 := by
  let p : UnitAddCircle → ℝ := fun x => Real.exp (F ((fourier 1 x).re))
  let v : UnitAddCircle → ℝ := fun x => p x*(1-(fourier 1 x).re)
  have hcp : Continuous p := Real.continuous_exp.comp (hcF.comp (Complex.continuous_re.comp (fourier 1).continuous))
  have hcv : Continuous v := hcp.mul (continuous_const.sub (Complex.continuous_re.comp (fourier 1).continuous))
  have hi {f : UnitAddCircle → ℝ} (hf : Continuous f) : Integrable f AddCircle.haarAddCircle :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hv : ∀ x,0≤v x := fun x => mul_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (abs_le.mp (circle_cosine_bound x)).2)
  have hpos : 0<∫ x,v x ∂AddCircle.haarAddCircle := by
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (integral_nonneg hv)
    have hae := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hv) (hi hcv)).mp hz
    have he := congrFun (MeasureTheory.Measure.eq_of_ae_eq hae hcv continuous_const) (((1/2:ℝ):UnitAddCircle))
    have hhalf : (fourier 1 (((1/2:ℝ):UnitAddCircle))).re= -1 := by
      simpa using circle_cosine_half_shift 0
    change p (((1/2:ℝ):UnitAddCircle))*(1-(fourier 1 (((1/2:ℝ):UnitAddCircle))).re)=0 at he
    rw [hhalf] at he
    have hp : 0<p (((1/2:ℝ):UnitAddCircle)) := Real.exp_pos _
    linarith
  have he : (∫ x,v x ∂AddCircle.haarAddCircle)=1-
      ∫ x,p x*(fourier 1 x).re ∂AddCircle.haarAddCircle := by
    change (∫ x,p x*(1-(fourier 1 x).re) ∂AddCircle.haarAddCircle)=_
    simp_rw [mul_sub,mul_one]
    rw [integral_sub (g:=fun x => p x*(fourier 1 x).re) (hi hcp) (hi (hcp.mul (Complex.continuous_re.comp (fourier 1).continuous))),hmass]
  rw [he] at hpos
  linarith

#print axioms circle_mean_nonneg
#print axioms circle_mean_lt_one
end BecknerOnofri.HighDim.CircleScalar
