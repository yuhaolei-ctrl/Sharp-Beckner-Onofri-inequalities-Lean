module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Integrability of absolutely integrable series

For a countable family of integrable functions, summability of the integrals
of their norms implies almost-everywhere absolute convergence and integrability
of the pointwise sum. No pointwise summability or finite-measure hypothesis is
assumed. Completeness of the normed additive group ensures that absolute convergence gives
an actual sum rather than only a finite total norm.
-/

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace Legacy.TorusEndpoint.IntegrableSeries

variable {ι α E : Type*} [Countable ι] [MeasurableSpace α]
  [NormedAddCommGroup E] {μ : Measure α}
  {F : ι → α → E}

/-- The integrated extended norm of the entire family is finite. -/
theorem lintegral_tsum_enorm_lt_top
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) :
    (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂μ) < ∞ := by
  rw [lintegral_tsum (fun i => (hF i).aestronglyMeasurable.enorm)]
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hF _)]
  exact hs.tsum_ofReal_lt_top

/-- Pointwise absolute summability is a conclusion, outside a null set. -/
theorem ae_summable_norm
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => ‖F i x‖) := by
  have htop := lintegral_tsum_enorm_lt_top hF hs
  have hae := ae_lt_top'
    (AEMeasurable.tsum (fun i => (hF i).aestronglyMeasurable.enorm)) htop.ne
  filter_upwards [hae] with x hx
  exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne

/-- In a complete normed group, the actual family is almost everywhere summable. -/
theorem ae_summable [CompleteSpace E]
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => F i x) := by
  filter_upwards [ae_summable_norm hF hs] with x hx
  exact hx.of_norm

/-- The pointwise total sum is integrable; no extra a.e. convergence premise is needed. -/
theorem integrable_tsum_of_summable_integral_norm [CompleteSpace E]
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, F i x) μ := by
  classical
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun s : Finset ι => ∑ i ∈ s, F i x) atTop
        (𝓝 (∑' i, F i x)) := by
    filter_upwards [ae_summable hF hs] with x hx
    exact hx.hasSum
  refine ⟨aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
    (fun s => s.aestronglyMeasurable_fun_sum
      (fun i _ => (hF i).aestronglyMeasurable)) hlim, ?_⟩
  exact lt_of_le_of_lt
    (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm))
    (lintegral_tsum_enorm_lt_top hF hs)

end Legacy.TorusEndpoint.IntegrableSeries
