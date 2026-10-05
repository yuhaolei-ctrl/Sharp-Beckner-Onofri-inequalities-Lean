module

public import BecknerOnofri.Friedrichs.MixedAngularVectors

@[expose] public section

/-! Sine-weighted tensor profiles belong to the actual mixed spatial form
closure. The single product cutoff handles all active boundary faces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma angularLift_function_tendsto {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) :
    Tendsto (fun δ : ℝ => (cutoffLift α f hf δ).1) (𝓝[>] 0) (𝓝 (angularLift α f hf).1) := by
  apply SpatialForm.tendsto_of_norm_sq
  have ht := cutoffProfile_L2_error_tendsto_zero α _ (angularProfiles_smooth α f hf)
  have he (δ : ℝ) : (∫ x,(cutoffProfile α (angularProfiles α f) δ x-productProfile (angularProfiles α f) x)^2 ∂spatialMeasure α)=
    ‖(cutoffLift α f hf δ).1-(angularLift α f hf).1‖^2 :=
    integral_sq_sub (cutoff_memLp α f hf δ) (angular_memLp α f hf)
  simpa only [he] using ht

lemma angularLift_gradient_tendsto {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (i : Fin d) :
    Tendsto (fun δ : ℝ => (cutoffLift α f hf δ).2.1 i) (𝓝[>] 0) (𝓝 ((angularLift α f hf).2.1 i)) := by
  apply SpatialForm.tendsto_of_norm_sq
  have hend : ∀ j,α j≠0 → angularProfiles α f j 0=0 ∧ angularProfiles α f j Real.pi=0 := by
    intro j hj
    simp [angularProfiles,Legacy.BecknerOnofri.JacobiAngular.angular,hj]
  have ht := gradient_error_tendsto_zero α _ (angularProfiles_smooth α f hf) hend i
  have he (δ : ℝ) : (∫ x,(partialDerivative i (cutoffProfile α (angularProfiles α f) δ) x-
    partialDerivative i (productProfile (angularProfiles α f)) x)^2 ∂spatialMeasure α)=
    ‖(cutoffLift α f hf δ).2.1 i-(angularLift α f hf).2.1 i‖^2 :=
    integral_sq_sub (cutoff_partial_memLp α f hf δ i) (angular_partial_memLp α f hf i)
  simpa only [he] using ht

lemma angularLift_potential_tendsto {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (i : Fin d) :
    Tendsto (fun δ : ℝ => (cutoffLift α f hf δ).2.2 i) (𝓝[>] 0) (𝓝 ((angularLift α f hf).2.2 i)) := by
  apply SpatialForm.tendsto_of_norm_sq
  have ht := angular_product_potential_error_tendsto_zero α f hf i
  have he (δ : ℝ) : (∫ x,(SpatialForm.potentialFactor (α i) (x i)*cutoffProfile α (angularProfiles α f) δ x-
    SpatialForm.potentialFactor (α i) (x i)*productProfile (angularProfiles α f) x)^2 ∂spatialMeasure α)=
    ‖(cutoffLift α f hf δ).2.2 i-(angularLift α f hf).2.2 i‖^2 :=
    integral_sq_sub (cutoff_potential_memLp α f hf δ i) (angular_potential_memLp α f hf i)
  simpa only [mul_sub,he] using ht

theorem angularLift_tendsto {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) :
    Tendsto (cutoffLift α f hf) (𝓝[>] 0) (𝓝 (angularLift α f hf)) :=
  (angularLift_function_tendsto α f hf).prodMk_nhds
    ((tendsto_pi_nhds.mpr (angularLift_gradient_tendsto α f hf)).prodMk_nhds
      (tendsto_pi_nhds.mpr (angularLift_potential_tendsto α f hf)))

theorem angular_mem_formClosure {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) : angularLift α f hf∈formClosure α := by
  apply mem_closure_of_tendsto (angularLift_tendsto α f hf)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact cutoffLift_mem_core α f hf hδ

#print axioms angular_mem_formClosure
end BecknerOnofri.Friedrichs.MixedSpatial
