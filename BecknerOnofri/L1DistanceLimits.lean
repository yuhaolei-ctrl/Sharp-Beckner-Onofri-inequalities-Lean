module

public import BecknerOnofri.L1ContractiveLimit

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.RearrangementApproximation

theorem integral_distance_tendsto {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} {f g : ι → α → ℝ} {f₀ g₀ : α → ℝ}
    (hf : ∀ n,Integrable (f n) μ) (hg : ∀ n,Integrable (g n) μ)
    (hf₀ : Integrable f₀ μ) (hg₀ : Integrable g₀ μ)
    (hfL : Tendsto (fun n => ∫ x,‖f n x-f₀ x‖ ∂μ) l (𝓝 0))
    (hgL : Tendsto (fun n => ∫ x,‖g n x-g₀ x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ x,‖f n x-g n x‖ ∂μ) l (𝓝 (∫ x,‖f₀ x-g₀ x‖ ∂μ)) := by
  have h := ((tendsto_toL1_iff hf hf₀).mpr hfL).dist ((tendsto_toL1_iff hg hg₀).mpr hgL)
  simpa only [dist_toL1_eq] using h

theorem ae_eq_of_l1_distance_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hzero : (∫ x,‖f x-g x‖ ∂μ)=0) : f=ᵐ[μ] g := by
  apply (Integrable.toL1_eq_toL1_iff f g hf hg).mp
  apply dist_eq_zero.mp
  rwa [dist_toL1_eq]

#print axioms integral_distance_tendsto
#print axioms ae_eq_of_l1_distance_zero
end BecknerOnofri.RearrangementApproximation
