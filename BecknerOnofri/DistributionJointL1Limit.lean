import BecknerOnofri.DistributionL1Limit
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! Both sides of an equidistribution identity may vary along L1-convergent
sequences. This is needed when rearranging approximations of an L1 function. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BecknerOnofri.DistributionLimit

theorem identDistrib_of_joint_l1 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℕ → α → ℝ} {g : ℕ → β → ℝ} {f₀ : α → ℝ} {g₀ : β → ℝ}
    (hf : ∀ n,Integrable (f n) μ) (hg : ∀ n,Integrable (g n) ν)
    (hf₀ : Integrable f₀ μ) (hg₀ : Integrable g₀ ν)
    (hD : ∀ n,IdentDistrib (f n) (g n) μ ν)
    (hfL : Tendsto (fun n => ∫ x,‖f n x-f₀ x‖ ∂μ) atTop (𝓝 0))
    (hgL : Tendsto (fun n => ∫ x,‖g n x-g₀ x‖ ∂ν) atTop (𝓝 0)) :
    IdentDistrib f₀ g₀ μ ν := by
  have hfT := (inMeasure_of_l1 hf hf₀ hfL).tendstoInDistribution_of_aemeasurable
    (fun n => (hf n).aemeasurable) hf₀.aemeasurable
  have hgT := (inMeasure_of_l1 hg hg₀ hgL).tendstoInDistribution_of_aemeasurable
    (fun n => (hg n).aemeasurable) hg₀.aemeasurable
  have hfT' : TendstoInDistribution g atTop f₀ (fun _ => ν) μ :=
    { forall_aemeasurable := fun n => (hg n).aemeasurable
      aemeasurable_limit := hf₀.aemeasurable
      tendsto := by
        convert! hfT.tendsto using 2 with n
        exact Subtype.ext (hD n).map_eq.symm }
  exact ⟨hf₀.aemeasurable,hg₀.aemeasurable,tendstoInDistribution_unique g hfT' hgT⟩

#print axioms identDistrib_of_joint_l1
end BecknerOnofri.DistributionLimit
