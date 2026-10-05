module

public import BecknerOnofri.ConditionalExpectations
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Jensen's inequality for the actual density-weighted expectation. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

theorem weighted_jensen_of_nonneg {d : ℕ} {f u : Torus d → ℝ}
    (hf : BoundedMeasurable f) (hpos : ∀ x, 0 ≤ f x)
    (hm : (∫ x, f x ∂torusMeasure d) = 1)
    (hu : BoundedMeasurable u) {a b : ℝ} (hr : ∀ x, u x ∈ Icc a b)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc a b)) (hψ : ConvexOn ℝ (Icc a b) ψ) :
    ψ (∫ x, f x * u x ∂torusMeasure d) ≤
      ∫ x, f x * ψ (u x) ∂torusMeasure d := by
  let ν := (torusMeasure d).withDensity (fun x => ENNReal.ofReal (f x))
  have hfm : Measurable (fun x => ENNReal.ofReal (f x)) := hf.1.ennreal_ofReal
  have hft : ∀ᵐ x ∂torusMeasure d, ENNReal.ofReal (f x) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hreal (x : Torus d) : (ENNReal.ofReal (f x)).toReal = f x :=
    ENNReal.toReal_ofReal (hpos x)
  have hν : IsProbabilityMeasure ν := by
    constructor
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hf.integrable
        (Filter.Eventually.of_forall hpos), hm]
    norm_num
  letI := hν
  have huc : BoundedMeasurable (fun x => ψ (u x)) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hc.norm)
    refine ⟨hc.restrict.measurable.comp (hu.1.subtype_mk (h := hr)), C, fun x => ?_⟩
    exact hC (mem_image_of_mem (fun y => ‖ψ y‖) (hr x))
  have hνint (v : Torus d → ℝ) (hv : BoundedMeasurable v) : Integrable v ν := by
    apply (integrable_withDensity_iff_integrable_smul' hfm hft).mpr
    simpa only [hreal, smul_eq_mul] using (hf.mul hv).integrable
  have hi := hψ.map_integral_le (μ := ν) hc isClosed_Icc
    (Filter.Eventually.of_forall hr) (hνint u hu) (hνint _ huc)
  have hrewrite (v : Torus d → ℝ) :
      (∫ x, v x ∂ν) = ∫ x, f x * v x ∂torusMeasure d := by
    simpa only [hreal, smul_eq_mul] using
      (integral_withDensity_eq_integral_toReal_smul hfm hft v)
  rw [hrewrite, hrewrite] at hi
  exact hi

theorem weighted_jensen {d : ℕ} {f u : Torus d → ℝ}
    (hf : PositiveBounded f) (hm : (∫ x, f x ∂torusMeasure d) = 1)
    (hu : BoundedMeasurable u) {a b : ℝ} (hr : ∀ x, u x ∈ Icc a b)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc a b)) (hψ : ConvexOn ℝ (Icc a b) ψ) :
    ψ (∫ x, f x * u x ∂torusMeasure d) ≤
      ∫ x, f x * ψ (u x) ∂torusMeasure d :=
  weighted_jensen_of_nonneg hf.bounded (fun x => (hf.pos x).le) hm hu hr ψ hc hψ

theorem conditional_moment_jensen {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (hm : (∫ x, f x ∂torusMeasure d) = 1)
    (i : Fin d) (n : ℕ) {a b : ℝ}
    (hr : ∀ x, conditionalCosineMoment f i n x ∈ Icc a b)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc a b)) (hψ : ConvexOn ℝ (Icc a b) ψ) :
    ψ (∫ x, f x * (fourier (n : ℤ) (x i)).re ∂torusMeasure d) ≤
      ∫ x, f x * ψ (conditionalCosineMoment f i n x) ∂torusMeasure d := by
  rw [← conditional_moment_full_tower hf i n]
  exact weighted_jensen hf hm (conditional_moment_bounded hf i n) hr ψ hc hψ

#print axioms conditional_moment_jensen

end BecknerOnofri.HighDim.ConditionalEntropy
