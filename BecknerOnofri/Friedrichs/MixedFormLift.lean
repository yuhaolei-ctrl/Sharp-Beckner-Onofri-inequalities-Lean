import BecknerOnofri.Friedrichs.MixedAngularPotential
import BecknerOnofri.Friedrichs.MixedGradientLimit
import BecknerOnofri.Friedrichs.FormLift

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma productProfile_continuous {d : ℕ} (f : Fin d → ℝ → ℝ) (hf : ∀ i,Continuous (f i)) :
    Continuous (productProfile f) := continuous_finsetProd _ (fun i _ => (hf i).comp (continuous_apply i))

lemma cutoff_partial_continuous {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (δ : ℝ) (i : Fin d) :
    Continuous (partialDerivative i (cutoffProfile α f δ)) := by
  rw [← productProfile_cutoffFactors]
  exact partialDerivative_productProfile_continuous _ (cutoffFactors_smooth α f hf δ) i

lemma potential_measurable {d : ℕ} (α : MultiIndex d) (i : Fin d) :
    Measurable (fun x : Space d => SpatialForm.potentialFactor (α i) (x i)) :=
  measurable_const.div (Real.measurable_sin.comp (measurable_pi_apply i))

lemma weighted_product_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,Continuous (f j)) (W : Space d → ℝ) (hW : Measurable W)
    (hi : Integrable (fun x => (W x*productProfile f x)^2) (spatialMeasure α)) :
    MemLp (fun x => W x*productProfile f x) 2 (spatialMeasure α) :=
  (memLp_two_iff_integrable_sq (hW.mul (productProfile_continuous f hf).measurable).aestronglyMeasurable).mpr hi

lemma weighted_cutoff_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (W : Space d → ℝ) (hW : Measurable W)
    (hi : Integrable (fun x => (W x*productProfile f x)^2) (spatialMeasure α)) (δ : ℝ) :
    MemLp (fun x => W x*cutoffProfile α f δ x) 2 (spatialMeasure α) := by
  have hm : AEStronglyMeasurable (fun x => W x*cutoffProfile α f δ x) (spatialMeasure α) :=
    (hW.mul (cutoffProfile_contDiff α f hf δ).continuous.measurable).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply hi.mono' (hm.pow 2)
  apply ae_of_all
  intro x
  change ‖(W x*cutoffProfile α f δ x)^2‖≤(W x*productProfile f x)^2
  have hχ := productCutoff_mem α δ x
  have hs : (productCutoff α δ x)^2≤1 := by nlinarith [hχ.1,hχ.2]
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),cutoffProfile_factor]
  calc
    _ = (productCutoff α δ x)^2*(W x*productProfile f x)^2 := by ring
    _ ≤ _ := mul_le_of_le_one_left (sq_nonneg _) hs

def lift {d : ℕ} (α : MultiIndex d) (F : Space d → ℝ)
    (h0 : MemLp F 2 (spatialMeasure α))
    (h1 : ∀ i,MemLp (partialDerivative i F) 2 (spatialMeasure α))
    (hV : ∀ i,MemLp (fun x => SpatialForm.potentialFactor (α i) (x i)*F x) 2 (spatialMeasure α)) :
    EnergySpace α := (h0.toLp F,((fun i => (h1 i).toLp (partialDerivative i F)),
      (fun i => (hV i).toLp (fun x => SpatialForm.potentialFactor (α i) (x i)*F x))))

lemma lift_mem_core {d : ℕ} (α : MultiIndex d) {F : Space d → ℝ} (hF : smoothCoreProfile α F)
    (h0 : MemLp F 2 (spatialMeasure α))
    (h1 : ∀ i,MemLp (partialDerivative i F) 2 (spatialMeasure α))
    (hV : ∀ i,MemLp (fun x => SpatialForm.potentialFactor (α i) (x i)*F x) 2 (spatialMeasure α)) :
    lift α F h0 h1 hV∈core α :=
  ⟨F,hF,h0.coeFn_toLp,fun i => (h1 i).coeFn_toLp,fun i => (hV i).coeFn_toLp⟩

lemma integral_sq_sub {d : ℕ} {α : MultiIndex d} {F G : Space d → ℝ}
    (hF : MemLp F 2 (spatialMeasure α)) (hG : MemLp G 2 (spatialMeasure α)) :
    (∫ x,(F x-G x)^2 ∂spatialMeasure α)=‖hF.toLp F-hG.toLp G‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hF.toLp F) (hG.toLp G),hF.coeFn_toLp,hG.coeFn_toLp] with x hx hfx hgx
  simp only [hx,Pi.sub_apply,hfx,hgx,RCLike.inner_apply,conj_trivial,pow_two]

#print axioms integral_sq_sub
end BecknerOnofri.Friedrichs.MixedSpatial
