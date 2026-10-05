import BecknerOnofri.Friedrichs.MixedFormLift

/-! Product form-domain approximation allowing arbitrary smooth periodic
inactive factors, including the odd sine sector of the full periodic space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def ProfilePotentialIntegrable {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) : Prop :=
  ∀ i,Integrable (fun x => (SpatialForm.potentialFactor (α i) (x i)*productProfile f x)^2) (spatialMeasure α)

lemma profile_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) : MemLp (productProfile f) 2 (spatialMeasure α) :=
  continuous_memLp α (productProfile_continuous f (fun j => (hf j).continuous))

lemma profile_partial_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (i : Fin d) :
    MemLp (partialDerivative i (productProfile f)) 2 (spatialMeasure α) :=
  continuous_memLp α (partialDerivative_productProfile_continuous f hf i)

lemma profile_potential_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hV : ProfilePotentialIntegrable α f) (i : Fin d) :
    MemLp (fun x => SpatialForm.potentialFactor (α i) (x i)*productProfile f x) 2 (spatialMeasure α) :=
  weighted_product_memLp α f (fun j => (hf j).continuous) _ (potential_measurable α i) (hV i)

def profileLift {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hV : ProfilePotentialIntegrable α f) : EnergySpace α :=
  lift α (productProfile f) (profile_memLp α f hf) (profile_partial_memLp α f hf)
    (profile_potential_memLp α f hf hV)

lemma profile_cutoff_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (δ : ℝ) : MemLp (cutoffProfile α f δ) 2 (spatialMeasure α) :=
  continuous_memLp α (cutoffProfile_contDiff α f hf δ).continuous

lemma profile_cutoff_partial_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (δ : ℝ) (i : Fin d) :
    MemLp (partialDerivative i (cutoffProfile α f δ)) 2 (spatialMeasure α) :=
  continuous_memLp α (cutoff_partial_continuous α f hf δ i)

lemma profile_cutoff_potential_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hV : ProfilePotentialIntegrable α f) (δ : ℝ) (i : Fin d) :
    MemLp (fun x => SpatialForm.potentialFactor (α i) (x i)*cutoffProfile α f δ x) 2 (spatialMeasure α) :=
  weighted_cutoff_memLp α f hf _ (potential_measurable α i) (hV i) δ

def profileCutoffLift {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hV : ProfilePotentialIntegrable α f) (δ : ℝ) : EnergySpace α :=
  lift α (cutoffProfile α f δ) (profile_cutoff_memLp α f hf δ) (profile_cutoff_partial_memLp α f hf δ)
    (profile_cutoff_potential_memLp α f hf hV δ)

lemma profileLift_tendsto {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hV : ProfilePotentialIntegrable α f)
    (hend : ∀ j,α j≠0 → f j 0=0 ∧ f j Real.pi=0) :
    Tendsto (profileCutoffLift α f hf hV) (𝓝[>] 0) (𝓝 (profileLift α f hf hV)) := by
  have h0 : Tendsto (fun δ => (profileCutoffLift α f hf hV δ).1) (𝓝[>] 0) (𝓝 (profileLift α f hf hV).1) := by
    apply SpatialForm.tendsto_of_norm_sq
    have he (δ : ℝ) : (∫ x,(cutoffProfile α f δ x-productProfile f x)^2 ∂spatialMeasure α)=
        ‖(profileCutoffLift α f hf hV δ).1-(profileLift α f hf hV).1‖^2 :=
      integral_sq_sub (profile_cutoff_memLp α f hf δ) (profile_memLp α f hf)
    simpa only [he] using cutoffProfile_L2_error_tendsto_zero α f hf
  have h1 (i : Fin d) : Tendsto (fun δ => (profileCutoffLift α f hf hV δ).2.1 i)
      (𝓝[>] 0) (𝓝 ((profileLift α f hf hV).2.1 i)) := by
    apply SpatialForm.tendsto_of_norm_sq
    have he (δ : ℝ) : (∫ x,(partialDerivative i (cutoffProfile α f δ) x-
        partialDerivative i (productProfile f) x)^2 ∂spatialMeasure α)=
        ‖(profileCutoffLift α f hf hV δ).2.1 i-(profileLift α f hf hV).2.1 i‖^2 :=
      integral_sq_sub (profile_cutoff_partial_memLp α f hf δ i) (profile_partial_memLp α f hf i)
    simpa only [he] using gradient_error_tendsto_zero α f hf hend i
  have hP (i : Fin d) : Tendsto (fun δ => (profileCutoffLift α f hf hV δ).2.2 i)
      (𝓝[>] 0) (𝓝 ((profileLift α f hf hV).2.2 i)) := by
    apply SpatialForm.tendsto_of_norm_sq
    have he (δ : ℝ) : (∫ x,(SpatialForm.potentialFactor (α i) (x i)*cutoffProfile α f δ x-
        SpatialForm.potentialFactor (α i) (x i)*productProfile f x)^2 ∂spatialMeasure α)=
        ‖(profileCutoffLift α f hf hV δ).2.2 i-(profileLift α f hf hV).2.2 i‖^2 :=
      integral_sq_sub (profile_cutoff_potential_memLp α f hf hV δ i) (profile_potential_memLp α f hf hV i)
    simpa only [mul_sub,he] using weighted_profile_error_tendsto_zero α f _ (hV i)
  exact h0.prodMk_nhds ((tendsto_pi_nhds.mpr h1).prodMk_nhds (tendsto_pi_nhds.mpr hP))

theorem profile_mem_formClosure {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hV : ProfilePotentialIntegrable α f)
    (hp : ∀ i,α i=0 → Function.Periodic (f i) (2*Real.pi))
    (hend : ∀ j,α j≠0 → f j 0=0 ∧ f j Real.pi=0) :
    profileLift α f hf hV∈formClosure α := by
  apply mem_closure_of_tendsto (profileLift_tendsto α f hf hV hend)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact lift_mem_core α (cutoffProfile_core α f hf hp hδ) _ _ _

#print axioms profile_mem_formClosure
end BecknerOnofri.Friedrichs.MixedSpatial
