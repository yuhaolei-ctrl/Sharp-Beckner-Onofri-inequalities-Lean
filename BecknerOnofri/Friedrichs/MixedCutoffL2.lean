module

public import BecknerOnofri.Friedrichs.MixedProductCutoff
public import BecknerOnofri.Friedrichs.CutoffLimit
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Actual L2 convergence of product cutoffs on the mixed spatial measure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def productProfile {d : ℕ} (f : Fin d → ℝ → ℝ) (x : Space d) : ℝ := ∏ i,f i (x i)

def productCutoff {d : ℕ} (α : MultiIndex d) (δ : ℝ) (x : Space d) : ℝ :=
  ∏ i,if α i=0 then 1 else boundaryCutoff δ (x i)

lemma cutoffProfile_factor {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (δ : ℝ) (x : Space d) :
    cutoffProfile α f δ x=productCutoff α δ x*productProfile f x := by
  simp only [cutoffProfile,productCutoff,productProfile,Finset.prod_mul_distrib]

lemma productCutoff_mem {d : ℕ} (α : MultiIndex d) (δ : ℝ) (x : Space d) :
    productCutoff α δ x∈Icc 0 1 := by
  have hi (i : Fin d) : (if α i=0 then 1 else boundaryCutoff δ (x i))∈Icc (0:ℝ) 1 := by
    split_ifs
    · exact ⟨zero_le_one,le_rfl⟩
    · exact boundaryCutoff_mem δ (x i)
  exact ⟨Finset.prod_nonneg (fun i _ => (hi i).1),
    Finset.prod_le_one₀ (fun i _ => (hi i).1) (fun i _ => (hi i).2)⟩

lemma ae_active_interior {d : ℕ} (α : MultiIndex d) :
    ∀ᵐ x ∂spatialMeasure α,∀ i,α i≠0 → x i∈Ioo 0 Real.pi := by
  apply eventually_all.mpr
  intro i
  change ∀ᵐ x ∂Measure.pi (fun i => coordinateMeasure (α i)),α i≠0 → x i∈Ioo 0 Real.pi
  apply (Measure.tendsto_eval_ae_ae (μ := fun j : Fin d => coordinateMeasure (α j)) (i := i)).eventually
    (p := fun t : ℝ => α i≠0 → t∈Ioo 0 Real.pi)
  by_cases hi : α i=0
  · exact ae_of_all _ (fun t h => (h hi).elim)
  · simpa only [coordinateMeasure,if_neg hi] using
      (ae_restrict_mem measurableSet_Ioo : ∀ᵐ t ∂volume.restrict (Ioo 0 Real.pi),t∈Ioo 0 Real.pi).mono
        (fun t ht _ => ht)

lemma productCutoff_eventually_one {d : ℕ} (α : MultiIndex d) (x : Space d)
    (hx : ∀ i,α i≠0 → x i∈Ioo 0 Real.pi) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,productCutoff α δ x=1 := by
  have hi (i : Fin d) : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (if α i=0 then 1 else boundaryCutoff δ (x i))=1 := by
    by_cases h : α i=0
    · simp only [h,if_true,eventually_const]
    · filter_upwards [boundaryCutoff_eventually_one (hx i h)] with δ hδ
      simp only [if_neg h,hδ.1]
  filter_upwards [eventually_all.mpr hi] with δ hδ
  exact Finset.prod_eq_one (fun i _ => hδ i)

lemma coordinate_square_integrable (m : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun t => (f t)^2) (coordinateMeasure m) := by
  unfold coordinateMeasure
  split_ifs
  · exact (hf.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact (hf.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self

lemma productProfile_square_integrable {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i,Continuous (f i)) : Integrable (fun x => (productProfile f x)^2) (spatialMeasure α) := by
  have hi := Integrable.fintype_prod (fun i => coordinate_square_integrable (α i) (hf i))
  simpa only [productProfile,spatialMeasure,Finset.prod_pow] using hi

theorem cutoffProfile_L2_error_tendsto_zero {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i,ContDiff ℝ ∞ (f i)) :
    Tendsto (fun δ : ℝ => ∫ x,(cutoffProfile α f δ x-productProfile f x)^2 ∂spatialMeasure α)
      (𝓝[>] 0) (𝓝 (0:ℝ)) := by
  have hc : Continuous (productProfile f) := continuous_finsetProd _
    (fun i _ => (hf i).continuous.comp (continuous_apply i))
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0,AEStronglyMeasurable
      (fun x => (cutoffProfile α f δ x-productProfile f x)^2) (spatialMeasure α) :=
    Eventually.of_forall (fun δ => (((cutoffProfile_contDiff α f hf δ).continuous.sub hc).pow 2).aestronglyMeasurable)
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0,∀ᵐ x ∂spatialMeasure α,
      ‖(cutoffProfile α f δ x-productProfile f x)^2‖ ≤ (productProfile f x)^2 := by
    apply Eventually.of_forall
    intro δ
    apply ae_of_all
    intro x
    have hχ := productCutoff_mem α δ x
    have hsq : (productCutoff α δ x-1)^2≤1 := by nlinarith [hχ.1,hχ.2]
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),cutoffProfile_factor]
    calc
      _ = (productCutoff α δ x-1)^2*(productProfile f x)^2 := by ring
      _ ≤ _ := mul_le_of_le_one_left (sq_nonneg _) hsq
  have hlim : ∀ᵐ x ∂spatialMeasure α,Tendsto
      (fun δ : ℝ => (cutoffProfile α f δ x-productProfile f x)^2) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    filter_upwards [ae_active_interior α] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [productCutoff_eventually_one α x hx] with δ hδ
    simp only [cutoffProfile_factor,hδ,one_mul,sub_self,zero_pow (by decide : (2:ℕ)≠0)]
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (fun x => (productProfile f x)^2) hmeas hbound
    (productProfile_square_integrable α f (fun i => (hf i).continuous)) hlim

#print axioms cutoffProfile_L2_error_tendsto_zero
end BecknerOnofri.Friedrichs.MixedSpatial
