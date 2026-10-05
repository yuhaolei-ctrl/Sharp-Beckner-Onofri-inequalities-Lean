module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-! Parameter differentiation of continuous derivative families on a compact
integration space. Compactness proves the local domination, rather than
introducing it as an extra regularity assumption. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace BecknerOnofri.CompactParameter

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]

lemma integral_continuous (F : ℝ → Y → ℝ) (hc : Continuous F.uncurry) :
    Continuous (fun t => ∫ y,F t y ∂μ) := by
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support isCompact_univ hc.continuousOn (by simp)

lemma integral_hasDerivAt (F F' : ℝ → Y → ℝ)
    (hc : Continuous F.uncurry) (hc' : Continuous F'.uncurry)
    (hd : ∀ t y,HasDerivAt (fun x => F x y) (F' t y) t) (t : ℝ) :
    HasDerivAt (fun x => ∫ y,F x y ∂μ) (∫ y,F' t y ∂μ) t := by
  have hF (x : ℝ) : Continuous (F x) := hc.comp (continuous_const.prodMk continuous_id)
  have hF' (x : ℝ) : Continuous (F' x) := hc'.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set Y))).exists_bound_of_continuousOn
    hc'.continuousOn
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1))
    (Eventually.of_forall (fun x => (hF x).aestronglyMeasurable))
    ((hF t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hF' t).aestronglyMeasurable)
    (Eventually.of_forall (fun y x hx => hC (x,y) ⟨hx,mem_univ y⟩))
    (integrable_const C)
    (Eventually.of_forall (fun y x _ => hd x y))).2

/-- Every order of differentiation passes through the compact parameter integral. -/
theorem integral_contDiff_family (F : ℕ → ℝ → Y → ℝ)
    (hc : ∀ k,Continuous (F k).uncurry)
    (hd : ∀ k t y,HasDerivAt (fun x => F k x y) (F (k+1) t y) t) :
    ∀ k,ContDiff ℝ ∞ (fun t => ∫ y,F k t y ∂μ) := by
  have hfinite : ∀ n k : ℕ,ContDiff ℝ n (fun t => ∫ y,F k t y ∂μ) := by
    intro n
    induction n with
    | zero => intro k; exact contDiff_zero.mpr (integral_continuous μ (F k) (hc k))
    | succ n ih =>
      intro k
      apply contDiff_succ_iff_hasFDerivAt.mpr
      let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
      refine ⟨fun t => L (∫ y,F (k+1) t y ∂μ),L.contDiff.comp (ih (k+1)),?_⟩
      intro t
      exact (integral_hasDerivAt μ (F k) (F (k+1)) (hc k) (hc (k+1)) (hd k) t).hasFDerivAt
  intro k
  exact contDiff_iff_forall_nat_le.mpr (fun n _ => hfinite n k)

#print axioms integral_hasDerivAt
#print axioms integral_contDiff_family
end BecknerOnofri.CompactParameter
