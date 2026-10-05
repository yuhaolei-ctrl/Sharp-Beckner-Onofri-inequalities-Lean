import BecknerOnofri.Friedrichs.MixedCutoffL2

/-! Weighted cutoff convergence includes the singular potential components;
the dominating weight is required to be genuinely integrable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma productCutoff_continuous {d : ℕ} (α : MultiIndex d) (δ : ℝ) :
    Continuous (productCutoff α δ) := by
  have hc := (cutoffProfile_contDiff α (fun _ _ => 1) (fun _ => contDiff_const) δ).continuous
  have he : cutoffProfile α (fun _ _ => 1) δ=productCutoff α δ := by
    funext x
    simp only [cutoffProfile,productCutoff,mul_one]
  exact he ▸ hc

theorem weighted_cutoff_integral_tendsto_zero {d : ℕ} (α : MultiIndex d) (G : Space d → ℝ)
    (hG : Integrable G (spatialMeasure α)) :
    Tendsto (fun δ : ℝ => ∫ x,(productCutoff α δ x-1)^2*G x ∂spatialMeasure α)
      (𝓝[>] 0) (𝓝 (0:ℝ)) := by
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0,AEStronglyMeasurable
      (fun x => (productCutoff α δ x-1)^2*G x) (spatialMeasure α) :=
    Eventually.of_forall (fun δ =>
      (((productCutoff_continuous α δ).sub continuous_const).pow 2).aestronglyMeasurable.mul hG.aestronglyMeasurable)
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0,∀ᵐ x ∂spatialMeasure α,
      ‖(productCutoff α δ x-1)^2*G x‖≤|G x| := by
    apply Eventually.of_forall
    intro δ
    apply ae_of_all
    intro x
    have hχ := productCutoff_mem α δ x
    have hsq : (productCutoff α δ x-1)^2≤1 := by nlinarith [hχ.1,hχ.2]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) hsq
  have hlim : ∀ᵐ x ∂spatialMeasure α,Tendsto
      (fun δ : ℝ => (productCutoff α δ x-1)^2*G x) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    filter_upwards [ae_active_interior α] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [productCutoff_eventually_one α x hx] with δ hδ
    simp only [hδ,sub_self,zero_pow (by decide : (2:ℕ)≠0),zero_mul]
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (fun x => |G x|) hmeas hbound hG.abs hlim

theorem weighted_profile_error_tendsto_zero {d : ℕ} (α : MultiIndex d)
    (f : Fin d → ℝ → ℝ) (W : Space d → ℝ)
    (hi : Integrable (fun x => (W x*productProfile f x)^2) (spatialMeasure α)) :
    Tendsto (fun δ : ℝ => ∫ x,(W x*(cutoffProfile α f δ x-productProfile f x))^2 ∂spatialMeasure α)
      (𝓝[>] 0) (𝓝 (0:ℝ)) := by
  have he : ∀ δ x,(W x*(cutoffProfile α f δ x-productProfile f x))^2=
      (productCutoff α δ x-1)^2*(W x*productProfile f x)^2 := by
    intro δ x
    rw [cutoffProfile_factor]
    ring
  simp_rw [he]
  exact weighted_cutoff_integral_tendsto_zero α _ hi

#print axioms weighted_profile_error_tendsto_zero
end BecknerOnofri.Friedrichs.MixedSpatial
