import BecknerOnofri.DistributionLimit

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BecknerOnofri.DistributionLimit

/-- The concrete integral L1 metric implies convergence in measure. -/
theorem inMeasure_of_l1 {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} {f : ι → α → ℝ} {h : α → ℝ}
    (hf : ∀ n,Integrable (f n) μ) (hh : Integrable h μ)
    (hc : Tendsto (fun n => ∫ x,‖f n x-h x‖ ∂μ) l (𝓝 0)) :
    TendstoInMeasure μ f l h := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    (fun n => (hf n).aestronglyMeasurable) hh.aestronglyMeasurable
  have he (n : ι) : eLpNorm (f n-h) 1 μ = ENNReal.ofReal (∫ x,‖f n x-h x‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,← ofReal_integral_norm_eq_lintegral_enorm ((hf n).sub hh)]
    rfl
  simp_rw [he]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc

theorem identDistrib_of_l1 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : ℕ → α → ℝ} {g : β → ℝ} {h : α → ℝ}
    (hd : ∀ n,IdentDistrib (f n) g μ ν) (hg : Integrable g ν) (hh : Integrable h μ)
    (hc : Tendsto (fun n => ∫ x,‖f n x-h x‖ ∂μ) atTop (𝓝 0)) :
    IdentDistrib h g μ ν :=
  identDistrib_of_tendstoInMeasure hd (inMeasure_of_l1 (fun n => (hd n).integrable_iff.mpr hg) hh hc)

#print axioms inMeasure_of_l1
#print axioms identDistrib_of_l1
end BecknerOnofri.DistributionLimit
