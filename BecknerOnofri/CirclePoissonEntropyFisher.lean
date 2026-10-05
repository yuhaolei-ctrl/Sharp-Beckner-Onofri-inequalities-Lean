module

public import BecknerOnofri.CirclePoissonEntropyDerivative
public import BecknerOnofri.CirclePoissonRegularity
public import BecknerOnofri.CirclePoissonSymmetry
public import BecknerOnofri.CircleFisherBound

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleOuter CircleFisher

theorem torus_flow_positive (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (s : ℝ) (hs : 0<s) (x : Torus 1) : 0<torusFlow s p x := by
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hp.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hp.continuousOn
  exact (hpos xmin).trans_le (torus_flow_bounds p hp (p xmin) (p xmax)
    (fun x => hmin (Set.mem_univ x)) (fun x => hmax (Set.mem_univ x)) s hs x).1

theorem entropy_fisher_hasDerivAt (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (s : ℝ) (hs : 0<s) :
    HasDerivAt (fun t => ∫ x,torusFlow t p x * Real.log (torusFlow t p x) ∂torusMeasure 1)
      (-(∫ x,torusFlow s p x*lambda (fun y => Real.log (torusFlow s p y)) x ∂torusMeasure 1)) s := by
  have hP := torus_flow_continuous s hs p hp
  have hposP := torus_flow_positive p hp hpos s hs
  have hlog : Continuous (fun x => Real.log (torusFlow s p x)) := hP.log (fun x => (hposP x).ne')
  have hW := torus_flow_weighted s hs p hp hw
  have hLW : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff
      (fun x => (Real.log (torusFlow s p x):ℂ)) k‖) := by
    apply CircleRegularity.torus_weighted_summable
    exact Complex.ofRealCLM.contDiff.comp
      ((torus_flow_contDiff p hp hw s hs 3).log (fun x => (hposP (fun _ => (x:UnitAddCircle))).ne'))
  have hself := lambda_self_adjoint _ _ hP hlog hW hLW
  have h := entropy_hasDerivAt p hp hpos hw s hs
  rw [hself]
  simpa only [mul_comm] using h

theorem flow_fisher_lower_bound (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (s : ℝ) (hs : 0<s) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (torusFlow s p x:ℂ)) (fun _ => (n:ℤ))).re
    (r 1)^2<1 ∧
      2/(1-(r 1)^2)*(∑' n : ℕ,(r (n+2)-r 1*r (n+1))^2) ≤
        (∫ x,torusFlow s p x*lambda (fun y => Real.log (torusFlow s p y)) x ∂torusMeasure 1)-
          ((∫ x,(torusFlow s p x)^2 ∂torusMeasure 1)-1) := by
  exact smooth_fisher_lower_bound _ (torus_flow_continuous s hs p hp)
    (torus_flow_positive p hp hpos s hs) (torus_flow_even p he s)
    ((torus_flow_mass s hs p hp).trans hm) (torus_flow_contDiff p hp hw s hs 3)

#print axioms entropy_fisher_hasDerivAt
#print axioms flow_fisher_lower_bound
end BecknerOnofri.HighDim.CirclePoisson
