import BecknerOnofri.Friedrichs.MixedGradientBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def cutoffFactors {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (δ : ℝ) (i : Fin d) : ℝ → ℝ :=
  fun t => scalarCutoff (α i) δ t*f i t

lemma cutoffFactors_smooth {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (δ : ℝ) (i : Fin d) :
    ContDiff ℝ ∞ (cutoffFactors α f δ i) := scalarCutoff_product_smooth (α i) (hf i) δ

lemma productProfile_cutoffFactors {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (δ : ℝ) :
    productProfile (cutoffFactors α f δ)=cutoffProfile α f δ := by
  funext x
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : α i=0 <;> simp only [cutoffFactors,scalarCutoff,h,if_true,if_false]

lemma cutoffFactors_eventually {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (x : Space d)
    (hx : ∀ j,α j≠0 → x j∈Ioo 0 Real.pi) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,∀ j,cutoffFactors α f δ j (x j)=f j (x j) ∧
      deriv (cutoffFactors α f δ j) (x j)=deriv (f j) (x j) := by
  apply eventually_all.mpr
  intro j
  filter_upwards [scalarCutoff_eventually (hx j)] with δ hδ
  constructor
  · change scalarCutoff (α j) δ (x j)*f j (x j)=_
    rw [hδ.1,one_mul]
  · change deriv (fun t => scalarCutoff (α j) δ t*f j t) (x j)=_
    rw [scalarCutoff_product_deriv (α j) ((hf j).differentiable (by simp)),hδ.1,hδ.2]
    ring

theorem gradient_error_tendsto_zero {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hend : ∀ j,α j≠0 → f j 0=0 ∧ f j Real.pi=0)
    (i : Fin d) :
    Tendsto (fun δ : ℝ => ∫ x,(partialDerivative i (cutoffProfile α f δ) x-
      partialDerivative i (productProfile f) x)^2 ∂spatialMeasure α) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
  choose C hC hCb using fun j => cutoff_profile_joint_bound (α j) (hf j) (hend j)
  let M : ℝ := ∏ j,C j
  have hM : 0≤M := Finset.prod_nonneg (fun j _ => hC j)
  have hq (δ : ℝ) := cutoffFactors_smooth α f hf δ
  have hcont (δ : ℝ) : Continuous (partialDerivative i (cutoffProfile α f δ)) := by
    rw [← productProfile_cutoffFactors]
    exact partialDerivative_productProfile_continuous _ (hq δ) i
  have hbase := partialDerivative_productProfile_continuous f hf i
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0,AEStronglyMeasurable
      (fun x => (partialDerivative i (cutoffProfile α f δ) x-partialDerivative i (productProfile f) x)^2)
      (spatialMeasure α) := Eventually.of_forall (fun δ => ((hcont δ |>.sub hbase).pow 2).aestronglyMeasurable)
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0,∀ᵐ x ∂spatialMeasure α,
      ‖(partialDerivative i (cutoffProfile α f δ) x-partialDerivative i (productProfile f) x)^2‖≤(2*M)^2 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [spatial_ae_compact α,ae_active_interior α] with x hx hi
    have hb j := hCb j δ hδ (x j) ⟨hx.1 j,hx.2 j⟩ (hi j)
    have hb0 := partialDerivative_productProfile_bound f (fun j => (hf j).differentiable (by simp))
      C hC i x (fun j => (hb j).1) (hb i).2.1
    have hbq := partialDerivative_productProfile_bound (cutoffFactors α f δ)
      (fun j => (hq δ j).differentiable (by simp)) C hC i x (fun j => (hb j).2.2.1) (hb i).2.2.2
    rw [productProfile_cutoffFactors] at hbq
    have hdiff : |partialDerivative i (cutoffProfile α f δ) x-partialDerivative i (productProfile f) x|≤2*M :=
      (abs_sub _ _).trans (by linarith)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*M)).mpr hdiff
  have hlim : ∀ᵐ x ∂spatialMeasure α,Tendsto
      (fun δ : ℝ => (partialDerivative i (cutoffProfile α f δ) x-partialDerivative i (productProfile f) x)^2)
      (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    filter_upwards [ae_active_interior α] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [cutoffFactors_eventually α f hf x hx] with δ hδ
    have he : partialDerivative i (cutoffProfile α f δ) x=partialDerivative i (productProfile f) x := by
      rw [← productProfile_cutoffFactors,partialDerivative_productProfile _
        (fun j => (hq δ j).differentiable (by simp)),partialDerivative_productProfile f
        (fun j => (hf j).differentiable (by simp)),(hδ i).2]
      congr 1
      exact Finset.prod_congr rfl (fun j _ => (hδ j).1)
    simp only [he,sub_self,zero_pow (by decide : (2:ℕ)≠0)]
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (fun _ => (2*M)^2) hmeas hbound (integrable_const _) hlim

#print axioms gradient_error_tendsto_zero
end BecknerOnofri.Friedrichs.MixedSpatial
