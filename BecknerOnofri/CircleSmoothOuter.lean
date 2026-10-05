module

public import BecknerOnofri.CircleOuterFactorization
public import BecknerOnofri.CircleTorusRegularity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! The manuscript's smooth positive even circle density has a real Hardy factor.
Weighted absolute Fourier regularity is derived from C³ smoothness, not assumed. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleOuter

theorem smooth_probability_outer_representation (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    ∃ f : C(Torus 1,ℂ), ∃ u : CircleHardy.Space,
      (∀ x,Complex.normSq (f x)=p x) ∧ ‖u‖=1 ∧
      Summable (fun n : ℕ => (n:ℝ)*(u n)^2) ∧
      Summable (fun k => ‖UnitAddTorus.mFourierCoeff f k‖) ∧
      (∀ n : ℕ,(u n:ℂ)=UnitAddTorus.mFourierCoeff f (fun _ => (n:ℤ))) ∧
      (∀ k,k (0:Fin 1)<0 → UnitAddTorus.mFourierCoeff f k=0) ∧
      ∀ n : ℕ,CircleHardy.moment u n=
        (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re := by
  apply probability_outer_representation p hp hpos he hm
  apply CircleRegularity.torus_weighted_summable
  exact Complex.ofRealCLM.contDiff.comp
    (hsmooth.log (fun x => (hpos (fun _ => (x:UnitAddCircle))).ne'))

#print axioms smooth_probability_outer_representation
end BecknerOnofri.HighDim.CircleOuter
