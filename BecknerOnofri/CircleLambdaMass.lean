import BecknerOnofri.CircleLambda

noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleFisher
open CircleOuter

theorem lambda_integral_zero (g : Torus 1 → ℝ)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖)) :
    (∫ x,lambda g x ∂torusMeasure 1)=0 := by
  have h := lambda_coefficient g hw 0
  have h0 : UnitAddTorus.mFourierCoeff (fun x => (lambda g x:ℂ)) 0=0 := by
    simpa only [Pi.zero_apply,Int.cast_zero,abs_zero,Complex.ofReal_zero,zero_mul] using h
  simp only [UnitAddTorus.mFourierCoeff,neg_zero,UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply,one_smul,integral_complex_ofReal] at h0
  exact_mod_cast h0

#print axioms lambda_integral_zero
end BecknerOnofri.HighDim.CircleFisher
