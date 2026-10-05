import BecknerOnofri.CirclePoissonBounds
import BecknerOnofri.CirclePoissonGenerator
import BecknerOnofri.CircleLambdaMass
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleOuter CircleFisher

theorem entropy_derivative_of_bounds (p : Torus 1 → ℝ) (hp : Continuous p)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (a b : ℝ) (ha : 0<a) (hlo : ∀ x,a≤p x) (hhi : ∀ x,p x≤b)
    (s : ℝ) (hs : 0<s) :
    HasDerivAt (fun t => ∫ x,torusFlow t p x * Real.log (torusFlow t p x) ∂torusMeasure 1)
      (-(∫ x,Real.log (torusFlow s p x)*lambda (torusFlow s p) x ∂torusMeasure 1)) s := by
  let P := fun t => torusFlow t p
  let F := fun t x => P t x * Real.log (P t x)
  let F' := fun t x => (Real.log (P t x)+1)*(-lambda (P t) x)
  let M := ∑' k,|(k (0:Fin 1):ℝ)| * ‖UnitAddTorus.mFourierCoeff (fun y => (p y:ℂ)) k‖
  let B := |Real.log a|+|Real.log b|+1
  have hb : 0<b := ha.trans_le ((hlo 0).trans (hhi 0))
  have hP (t : ℝ) (ht : 0<t) := torus_flow_continuous t ht p hp
  have hW (t : ℝ) (ht : 0<t) := torus_flow_weighted t ht p hp hw
  have hpos (t : ℝ) (ht : 0<t) (x : Torus 1) : 0<P t x :=
    ha.trans_le (torus_flow_bounds p hp a b hlo hhi t ht x).1
  have hlog (t : ℝ) (ht : 0<t) : Continuous (fun x => Real.log (P t x)) :=
    (hP t ht).log (fun x => (hpos t ht x).ne')
  have hL (t : ℝ) (ht : 0<t) : Continuous (lambda (P t)) := lambda_continuous _ (hW t ht)
  have hFc (t : ℝ) (ht : 0<t) : Continuous (F t) := (hP t ht).mul (hlog t ht)
  have hF'c (t : ℝ) (ht : 0<t) : Continuous (F' t) :=
    ((hlog t ht).add continuous_const).mul (hL t ht).neg
  have hbound (t : ℝ) (ht : 0<t) (x : Torus 1) : ‖F' t x‖≤B*M := by
    obtain ⟨hl,hu⟩ := torus_flow_bounds p hp a b hlo hhi t ht x
    have hll : Real.log a≤Real.log (P t x) := Real.log_le_log ha hl
    have hlu : Real.log (P t x)≤Real.log b := Real.log_le_log (hpos t ht x) hu
    have hab : |Real.log (P t x)|≤|Real.log a|+|Real.log b| := by
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),
        abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
    have hB : |Real.log (P t x)+1|≤B := by
      calc
        _ ≤ |Real.log (P t x)|+|1| := abs_add_le _ _
        _ ≤ B := by rw [abs_one]; dsimp [B]; linarith
    have hM : |lambda (P t) x|≤M := lambda_flow_bound p hp hw t ht x
    simpa only [F',norm_mul,Real.norm_eq_abs,abs_neg] using
      mul_le_mul hB hM (abs_nonneg _) (by dsimp [B]; positivity)
  have hd (t : ℝ) (ht : 0<t) (x : Torus 1) : HasDerivAt (fun t => F t x) (F' t x) t := by
    exact (Real.hasDerivAt_mul_log (hpos t ht x).ne').comp t (torus_flow_hasDerivAt p hp hw t ht x)
  have hm : ∀ᶠ t in nhds s,AEStronglyMeasurable (F t) (torusMeasure 1) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact (hFc t ht).aestronglyMeasurable
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=torusMeasure 1) (s:=Ioi (0:ℝ)) (F:=F) (F':=F') (bound:=fun _ => B*M)
    (isOpen_Ioi.mem_nhds hs) hm ((hFc s hs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hF'c s hs).aestronglyMeasurable
    (ae_of_all _ (fun x t ht => hbound t ht x)) (integrable_const _)
    (ae_of_all _ (fun x t ht => hd t ht x))
  have hLI : Integrable (lambda (P s)) (torusMeasure 1) :=
    (hL s hs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hprod : Integrable (fun x => Real.log (P s x)*lambda (P s) x) (torusMeasure 1) :=
    ((hlog s hs).mul (hL s hs)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFI : (∫ x,F' s x ∂torusMeasure 1)=
      -(∫ x,Real.log (P s x)*lambda (P s) x ∂torusMeasure 1) := by
    have hfun : F' s = fun x => -(Real.log (P s x)*lambda (P s) x)-lambda (P s) x := by
      funext x
      dsimp [F']
      ring
    rw [hfun]
    calc
      _ = (∫ x,-(Real.log (P s x)*lambda (P s) x) ∂torusMeasure 1) -
          (∫ x,lambda (P s) x ∂torusMeasure 1) := integral_sub hprod.neg hLI
      _ = _ := by rw [integral_neg,lambda_integral_zero _ (hW s hs),sub_zero]
  rw [hFI] at H
  exact H.2

theorem entropy_hasDerivAt (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (s : ℝ) (hs : 0<s) :
    HasDerivAt (fun t => ∫ x,torusFlow t p x * Real.log (torusFlow t p x) ∂torusMeasure 1)
      (-(∫ x,Real.log (torusFlow s p x)*lambda (torusFlow s p) x ∂torusMeasure 1)) s := by
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hp.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hp.continuousOn
  exact entropy_derivative_of_bounds p hp hw (p xmin) (p xmax) (hpos xmin)
    (fun x => hmin (Set.mem_univ x)) (fun x => hmax (Set.mem_univ x)) s hs

theorem smooth_entropy_hasDerivAt (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (s : ℝ) (hs : 0<s) :
    HasDerivAt (fun t => ∫ x,torusFlow t p x * Real.log (torusFlow t p x) ∂torusMeasure 1)
      (-(∫ x,Real.log (torusFlow s p x)*lambda (torusFlow s p) x ∂torusMeasure 1)) s := by
  exact entropy_hasDerivAt p hp hpos
    (CircleRegularity.torus_weighted_summable _ (Complex.ofRealCLM.contDiff.comp hsmooth)) s hs

#print axioms smooth_entropy_hasDerivAt
end BecknerOnofri.HighDim.CirclePoisson
