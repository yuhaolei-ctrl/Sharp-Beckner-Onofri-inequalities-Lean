import BecknerOnofri.CirclePoissonInitial
import BecknerOnofri.CirclePoissonDeficitControl
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
namespace BecknerOnofri.HighDim.CirclePoisson

theorem smooth_deficit_differentiable (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (s : ℝ) (hs : 0<s) : DifferentiableAt ℝ (deficit p) s :=
  (smooth_deficit_dissipation p hp hpos he hm hsmooth s hs).1.differentiableAt

theorem smooth_deficit_deriv_nonpos (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (s : ℝ) (hs : 0<s) : 0≤-deriv (deficit p) s := by
  have h := smooth_deficit_dissipation p hp hpos he hm hsmooth s hs
  dsimp only at h
  exact le_trans (mul_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr h.2.1.le))
    (tsum_nonneg (fun n => sq_nonneg _))) h.2.2

theorem smooth_deficit_integral (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    IntegrableOn (fun s => -deriv (deficit p) s) (Ioi (0:ℝ)) ∧
      (∫ s in Ioi (0:ℝ),-deriv (deficit p) s)=deficit p 0 := by
  have hc := (smooth_deficit_continuous_initial p hp hpos he hm hsmooth).neg
  have hd (s : ℝ) (hs : s ∈ Ioi (0:ℝ)) :
      HasDerivAt (fun s => -deficit p s) (-deriv (deficit p) s) s :=
    (smooth_deficit_differentiable p hp hpos he hm hsmooth s hs).hasDerivAt.neg
  have hn (s : ℝ) (hs : s ∈ Ioi (0:ℝ)) := smooth_deficit_deriv_nonpos p hp hpos he hm hsmooth s hs
  have hl : Tendsto (fun s => -deficit p s) atTop (nhds 0) := by
    have h : Tendsto (deficit p) atTop (nhds 0) := deficit_tendsto_zero p hp hpos he hm
    simpa only [neg_zero] using h.neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd hn hl,?_⟩
  simpa only [zero_sub,Pi.neg_apply,neg_neg] using integral_Ioi_of_hasDerivAt_of_nonneg hc hd hn hl

#print axioms smooth_deficit_integral
end BecknerOnofri.HighDim.CirclePoisson
