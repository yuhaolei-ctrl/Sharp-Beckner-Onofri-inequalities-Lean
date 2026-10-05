module

public import BecknerOnofri.Friedrichs.MixedFormLift

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def angularFunction {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) : Space d → ℝ :=
  productProfile (angularProfiles α f)

def cutoffFunction {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (δ : ℝ) : Space d → ℝ :=
  cutoffProfile α (angularProfiles α f) δ

lemma angular_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) : MemLp (angularFunction α f) 2 (spatialMeasure α) :=
  continuous_memLp α (productProfile_continuous _ (fun j => (angularProfiles_smooth α f hf j).continuous))

lemma angular_partial_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (i : Fin d) :
    MemLp (partialDerivative i (angularFunction α f)) 2 (spatialMeasure α) :=
  continuous_memLp α (partialDerivative_productProfile_continuous _ (angularProfiles_smooth α f hf) i)

lemma angular_potential_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (i : Fin d) :
    MemLp (fun x => SpatialForm.potentialFactor (α i) (x i)*angularFunction α f x) 2 (spatialMeasure α) :=
  weighted_product_memLp α _ (fun j => (angularProfiles_smooth α f hf j).continuous) _
    (potential_measurable α i) (angular_product_potential_integrable α f hf i)

lemma cutoff_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (δ : ℝ) : MemLp (cutoffFunction α f δ) 2 (spatialMeasure α) :=
  continuous_memLp α (cutoffProfile_contDiff α _ (angularProfiles_smooth α f hf) δ).continuous

lemma cutoff_partial_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (δ : ℝ) (i : Fin d) :
    MemLp (partialDerivative i (cutoffFunction α f δ)) 2 (spatialMeasure α) :=
  continuous_memLp α (cutoff_partial_continuous α _ (angularProfiles_smooth α f hf) δ i)

lemma cutoff_potential_memLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (δ : ℝ) (i : Fin d) :
    MemLp (fun x => SpatialForm.potentialFactor (α i) (x i)*cutoffFunction α f δ x) 2 (spatialMeasure α) :=
  weighted_cutoff_memLp α _ (angularProfiles_smooth α f hf) _ (potential_measurable α i)
    (angular_product_potential_integrable α f hf i) δ

def angularLift {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (hf : ∀ j,ContDiff ℝ ∞ (f j)) : EnergySpace α :=
  lift α (angularFunction α f) (angular_memLp α f hf) (angular_partial_memLp α f hf) (angular_potential_memLp α f hf)

def cutoffLift {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (hf : ∀ j,ContDiff ℝ ∞ (f j)) (δ : ℝ) : EnergySpace α :=
  lift α (cutoffFunction α f δ) (cutoff_memLp α f hf δ) (cutoff_partial_memLp α f hf δ) (cutoff_potential_memLp α f hf δ)

lemma cutoffLift_mem_core {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) {δ : ℝ} (hδ : 0<δ) : cutoffLift α f hf δ∈core α :=
  lift_mem_core α (cutoffProfile_core α _ (angularProfiles_smooth α f hf)
    (fun i _ => angularProfiles_periodic α f i) hδ) _ _ _

#print axioms cutoffLift_mem_core
end BecknerOnofri.Friedrichs.MixedSpatial
