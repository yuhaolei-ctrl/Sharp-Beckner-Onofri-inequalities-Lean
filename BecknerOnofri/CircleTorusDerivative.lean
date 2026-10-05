import BecknerOnofri.CircleFisherDefinitions
import BecknerOnofri.CircleExpSeriesDerivative
import BecknerOnofri.CircleOuterWeighted

/-! Transfer the exponential logarithmic derivative identity to the actual
one-dimensional product torus Fourier series. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleFisher
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WeightedWiener CircleOuter

theorem first_moment_summable (a : Frequency 1 → ℂ)
    (ha : Summable (fun k => linearWeight k*‖a k‖)) :
    Summable (fun k => |(k (0:Fin 1):ℝ)| * ‖a k‖) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ ha
  intro k
  unfold linearWeight
  nlinarith [norm_nonneg (a k)]

theorem signed_coefficients_summable (a : Frequency 1 → ℂ)
    (ha : Summable (fun k => linearWeight k*‖a k‖)) :
    Summable (fun k => ‖(k (0:Fin 1):ℂ)*a k‖) := by
  simpa only [norm_mul,Complex.norm_intCast] using first_moment_summable a ha

theorem series_eq_circle (a : Frequency 1 → ℂ) (x : Torus 1) :
    absoluteFourierSeries a x=
      ∑' n : ℤ,a (fun _ => n)*fourier n (x 0) := by
  rw [absoluteFourierSeries,← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  apply tsum_congr
  intro n
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Fintype.prod_unique]
  rfl

theorem signed_series_eq_circle (a : Frequency 1 → ℂ) (x : Torus 1) :
    signedSeries a x=
      ∑' n : ℤ,(n:ℂ)*a (fun _ => n)*fourier n (x 0) := by
  exact series_eq_circle (fun k => (k (0:Fin 1):ℂ)*a k) x

theorem exponential_signed_series (a b : Frequency 1 → ℂ)
    (ha : Summable (fun k => linearWeight k*‖a k‖))
    (hb : Summable (fun k => linearWeight k*‖b k‖))
    (he : ∀ x,absoluteFourierSeries b x=Complex.exp (absoluteFourierSeries a x))
    (x : Torus 1) :
    signedSeries b x=Complex.exp (absoluteFourierSeries a x)*signedSeries a x := by
  let e := (Equiv.funUnique (Fin 1) ℤ).symm
  have ha₀ := e.summable_iff.mpr (summable_norm linearWeight_isWeight ha)
  have ha₁ := e.summable_iff.mpr (first_moment_summable a ha)
  have hb₀ := e.summable_iff.mpr (summable_norm linearWeight_isWeight hb)
  have hb₁ := e.summable_iff.mpr (first_moment_summable b hb)
  have h := CircleRegularity.exponential_series_derivative
    (fun n => a (fun _ => n)) (fun n => b (fun _ => n)) ha₀ ha₁ hb₀ hb₁
    (fun z => by simpa only [series_eq_circle] using he (fun _ => z)) (x 0)
  simpa only [signed_series_eq_circle,series_eq_circle] using h

#print axioms exponential_signed_series
end BecknerOnofri.HighDim.CircleFisher
