import BecknerOnofri.CompactParameterDifferentiation
import Mathlib.Analysis.Complex.Basic

/-! Differentiation under a complex-valued compact parameter integral.
The domination is derived from joint continuity, rather than postulated. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BecknerOnofri.CompactParameter
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]

lemma complex_integral_hasDerivAt (F F' : ℝ → Y → ℂ)
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

end BecknerOnofri.CompactParameter
