import BecknerOnofri.CircleFourierRegularity
import BecknerOnofri.CircleOuterDefinitions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleRegularity

theorem torus_coefficient_circle (f : Torus 1 → ℂ) (n : ℤ) :
    UnitAddTorus.mFourierCoeff f (fun _ => n)=
      _root_.fourierCoeff (fun x : UnitAddCircle => f (fun _ => x)) n := by
  have h := (measurePreserving_funUnique AddCircle.haarAddCircle (Fin 1)).symm
    (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle)
  have hi := h.integral_comp' (fun x : Torus 1 => UnitAddTorus.mFourier (fun _ => -n) x * f x)
  change (∫ x,UnitAddTorus.mFourier (fun _ => -n) x*f x ∂torusMeasure 1)=_
  refine hi.symm.trans ?_
  unfold _root_.fourierCoeff
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Fintype.prod_unique,smul_eq_mul]
  congr 1

theorem circle_coefficient_on (f : UnitAddCircle → ℂ) (n : ℤ) :
    _root_.fourierCoeff f n=fourierCoeffOn (by norm_num : (0:ℝ)<1)
      (fun x : ℝ => f x) n := by
  rw [fourierCoeff_eq_intervalIntegral f n 0,fourierCoeffOn_eq_integral]
  simp

theorem torus_weighted_summable (f : Torus 1 → ℂ)
    (hf : ContDiff ℝ 3 (fun x : ℝ => f (fun _ => (x:UnitAddCircle)))) :
    Summable (fun k => CircleOuter.linearWeight k*‖UnitAddTorus.mFourierCoeff f k‖) := by
  have hp : Function.Periodic (fun x : ℝ => f (fun _ => (x:UnitAddCircle))) 1 := by
    intro x
    simp only [AddCircle.coe_add_period]
  have hs := weighted_summable_of_contDiff _ hf hp
  apply ((Equiv.funUnique (Fin 1) ℤ).symm.summable_iff).mp
  change Summable (fun n : ℤ => (1+|(n:ℝ)|)*‖UnitAddTorus.mFourierCoeff f (fun _ => n)‖)
  simpa only [torus_coefficient_circle,circle_coefficient_on] using hs

#print axioms torus_weighted_summable
end BecknerOnofri.HighDim.CircleRegularity
