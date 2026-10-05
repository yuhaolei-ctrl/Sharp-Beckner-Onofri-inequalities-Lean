module

public import BecknerOnofri.Friedrichs.MixedSpatialDefinitions
public import BecknerOnofri.Friedrichs.BoundaryCutoff
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def cutoffProfile {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (δ : ℝ)
    (x : Space d) : ℝ := ∏ i,(if α i=0 then 1 else boundaryCutoff δ (x i))*f i (x i)

lemma cutoffProfile_contDiff {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i,ContDiff ℝ ∞ (f i)) (δ : ℝ) : ContDiff ℝ ∞ (cutoffProfile α f δ) := by
  unfold cutoffProfile
  apply contDiff_prod
  intro i hi
  apply ContDiff.mul
  · split_ifs with h
    · exact contDiff_const
    · exact (boundaryCutoff_smooth δ).comp (contDiff_apply ℝ ℝ i)
  · exact (hf i).comp (contDiff_apply ℝ ℝ i)

lemma cutoffProfile_periodic {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i,α i=0 → Function.Periodic (f i) (2*Real.pi)) (δ : ℝ) :
    inactivePeriodic α (cutoffProfile α f δ) := by
  intro i hi x
  unfold cutoffProfile
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hji : j=i
  · subst j
    simp only [Function.update_self,hi,if_true,one_mul]
    exact hf i hi (x i)
  · simp only [Function.update_of_ne hji]

lemma cutoffProfile_support {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    {δ : ℝ} (hδ : 0<δ) : interiorSupport α (cutoffProfile α f δ) := by
  refine ⟨δ,hδ,?_⟩
  intro x hx
  obtain ⟨i,hi,hx⟩ := hx
  unfold cutoffProfile
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [if_neg (Nat.ne_of_gt hi)]
  rcases hx with hl|hr
  · rw [boundaryCutoff_zero_left hδ hl,zero_mul]
  · rw [boundaryCutoff_zero_right hδ hr,zero_mul]

theorem cutoffProfile_core {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i,ContDiff ℝ ∞ (f i))
    (hp : ∀ i,α i=0 → Function.Periodic (f i) (2*Real.pi)) {δ : ℝ} (hδ : 0<δ) :
    smoothCoreProfile α (cutoffProfile α f δ) :=
  ⟨cutoffProfile_contDiff α f hf δ,cutoffProfile_periodic α f hp δ,cutoffProfile_support α f hδ⟩

#print axioms cutoffProfile_core
end BecknerOnofri.Friedrichs.MixedSpatial
