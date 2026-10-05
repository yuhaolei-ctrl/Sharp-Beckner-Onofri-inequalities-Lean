import BecknerOnofri.CircleFisherBoundary
import BecknerOnofri.CircleFisherPairing
import BecknerOnofri.CircleTorusRegularity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The genuine circle Fisher integral equals twice the actual Hardy
coefficient energy for smooth positive even probability densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleFisher
open CircleOuter

theorem density_fisher_representation (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hw : Summable (fun k => linearWeight k*
      ‖UnitAddTorus.mFourierCoeff (fun x => (Real.log (p x):ℂ)) k‖)) :
    ∃ u : CircleHardy.Space, ‖u‖=1 ∧
      Summable (fun n : ℕ => (n:ℝ)*(u n)^2) ∧
      (∀ n : ℕ,CircleHardy.moment u n=
        (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re) ∧
      (∫ x,p x*lambda (fun y => Real.log (p y)) x ∂torusMeasure 1)=
        2*∑' n : ℕ,(n:ℝ)*(u n)^2 := by
  let g : Torus 1 → ℝ := fun x => Real.log (p x)
  have hg : Continuous g := hp.log (fun x => (hpos x).ne')
  have hge (x : Torus 1) : g (-x)=g x := by dsimp only [g]; rw [he]
  obtain ⟨f,hf,hfw,hfr,hfn,hpoint⟩ := logarithm_fisher_factor g hg hge hw
  have hfp (x : Torus 1) : Complex.normSq (f x)=p x := by
    rw [hf]
    exact Real.exp_log (hpos x)
  have hfm : (∫ x,Complex.normSq (f x) ∂torusMeasure 1)=1 := by
    simpa only [hfp] using hm
  obtain ⟨u,hu,huc⟩ := hardy_unit_vector f hfr hfn hfm
  have hE := hardy_weighted_energy f u hu huc hfw
  refine ⟨u,hu,hE,?_,?_⟩
  · intro n
    simpa only [hfp] using hardy_moment_eq_density_coefficient f u huc hfn n
  · have heq (x : Torus 1) : p x*lambda g x=
        2*((starRingEnd ℂ) (f x)*signedSeries (UnitAddTorus.mFourierCoeff f) x).re := by
      simpa only [g,Real.exp_log (hpos x)] using hpoint x
    change (∫ x,p x*lambda g x ∂torusMeasure 1)=_
    simp_rw [heq]
    rw [integral_const_mul,signed_pairing f u hfw huc hfn]

theorem smooth_density_fisher_representation (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    ∃ u : CircleHardy.Space, ‖u‖=1 ∧
      Summable (fun n : ℕ => (n:ℝ)*(u n)^2) ∧
      (∀ n : ℕ,CircleHardy.moment u n=
        (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re) ∧
      (∫ x,p x*lambda (fun y => Real.log (p y)) x ∂torusMeasure 1)=
        2*∑' n : ℕ,(n:ℝ)*(u n)^2 := by
  apply density_fisher_representation p hp hpos he hm
  apply CircleRegularity.torus_weighted_summable
  exact Complex.ofRealCLM.contDiff.comp
    (hsmooth.log (fun x => (hpos (fun _ => (x:UnitAddCircle))).ne'))

#print axioms smooth_density_fisher_representation
end BecknerOnofri.HighDim.CircleFisher
