import BecknerOnofri.MixtureFrequencyEmbedding
import BecknerOnofri.SubsetEnergyIteration

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
open Finset MeasureTheory
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

def coordinateEnergy {d : ℕ} (I : Finset (Fin d)) (p : ℝ) (f : Torus d → ℝ) : ℝ≥0∞ :=
  weightedEnergyENN (fun k => if ∀ i ∉ I, k i = 0 then weight p k else 0) f

def coordinateEmbedding {d : ℕ} (I : Finset (Fin d)) : Fin I.card ↪ Fin d :=
  (I.orderEmbOfFin rfl).toEmbedding

lemma coordinateEmbedding_range {d : ℕ} (I : Finset (Fin d)) :
    Set.range (coordinateEmbedding I) = (I : Set (Fin d)) := I.range_orderEmbOfFin rfl

lemma coordinateEmbedding_mem {d : ℕ} (I : Finset (Fin d)) (j : Fin I.card) :
    coordinateEmbedding I j ∈ I := I.orderEmbOfFin_mem rfl j

lemma weightedEnergyENN_embedding_general {m d : ℕ} (e : Fin m ↪ Fin d)
    (g : Frequency d → ℝ) (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    weightedEnergyENN (fun k => if ∀ i ∉ Set.range e, k i = 0 then g k else 0)
      (CosineMixtureApproximation.rho w N) =
    weightedEnergyENN (fun k => g (extendFrequency e k))
      (CosineMixtureApproximation.rho w (fun n j => N n (e j))) := by
  classical
  let f : Frequency d → ℝ≥0∞ := fun k => ENNReal.ofReal
    ((if ∀ i ∉ Set.range e, k i = 0 then g k else 0) *
      ‖densityFourier (CosineMixtureApproximation.rho w N) k‖^2)
  have hf : Function.support f ⊆ Set.range (extendFrequency e) := by
    intro k hk
    apply (extendFrequency_range e k).mpr
    by_contra h
    exact hk (by dsimp only [f]; rw [if_neg h, zero_mul, ENNReal.ofReal_zero])
  have he : Function.Injective (extendFrequency e) := Function.extend_injective e.injective _
  change (∑' k, f k) = _
  rw [← he.tsum_eq hf]
  apply tsum_congr
  intro k
  have hk : ∀ i ∉ Set.range e, extendFrequency e k i = 0 := extendFrequency_outside e k
  dsimp only [f]
  rw [if_pos hk, rho_fourier_extendFrequency e w N hw hs]

lemma coordinateEnergy_embedding {d : ℕ} (I : Finset (Fin d)) (p : ℝ)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    coordinateEnergy I p (CosineMixtureApproximation.rho w N) =
      weightedEnergyENN (weight p)
        (CosineMixtureApproximation.rho w (fun n j => N n (coordinateEmbedding I j))) := by
  have h := weightedEnergyENN_embedding (coordinateEmbedding I) p w N hw hs
  simpa only [coordinateEmbedding_range, SetLike.mem_coe, coordinateEnergy] using h

lemma coordinateEnergy_erase_embedding {d : ℕ} (I : Finset (Fin d)) (p : ℝ)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (j : Fin I.card) :
    coordinateEnergy (I.erase (coordinateEmbedding I j)) p (CosineMixtureApproximation.rho w N) =
      weightedEnergyENN (fun k => if k j = 0 then weight p k else 0)
        (CosineMixtureApproximation.rho w (fun n l => N n (coordinateEmbedding I l))) := by
  classical
  let i := coordinateEmbedding I j
  have hcondition (k : Frequency d) :
      (∀ l ∉ I.erase i, k l = 0) ↔ ((∀ l ∉ I, k l = 0) ∧ k i = 0) := by
    constructor
    · intro h
      exact ⟨fun l hl => h l (fun he => hl (mem_erase.mp he).2), h i (notMem_erase _ _)⟩
    · rintro ⟨h, hi⟩ l hl
      by_cases he : l = i
      · simpa only [he] using hi
      · exact h l (fun hI => hl (mem_erase.mpr ⟨he, hI⟩))
  have hg : (fun k : Frequency d => if ∀ l ∉ I.erase i, k l = 0 then weight p k else 0) =
      (fun k => if ∀ l ∉ I, k l = 0 then (if k i = 0 then weight p k else 0) else 0) := by
    funext k
    simp only [hcondition]
    split_ifs <;> simp_all
  unfold coordinateEnergy
  rw [hg]
  have h := weightedEnergyENN_embedding_general (coordinateEmbedding I)
    (fun k => if k i = 0 then weight p k else 0) w N hw hs
  simpa only [coordinateEmbedding_range, SetLike.mem_coe, i,
    extendFrequency_apply, weight_extendFrequency] using h

#print axioms coordinateEnergy_embedding
#print axioms coordinateEnergy_erase_embedding
end BecknerOnofri.CosineMixtureTransfer
