module

public import BecknerOnofri.CountableMixtureExtendedComparison
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! Fourier reindexing for an arbitrary coordinate subset of a cosine mixture. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
open Finset MeasureTheory
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

def extendFrequency {m d : ℕ} (e : Fin m ↪ Fin d) (k : Frequency m) : Frequency d :=
  Function.extend e k (fun _ => 0)

@[simp] lemma extendFrequency_apply {m d : ℕ} (e : Fin m ↪ Fin d)
    (k : Frequency m) (j : Fin m) : extendFrequency e k (e j) = k j :=
  e.injective.extend_apply _ _ _

lemma extendFrequency_outside {m d : ℕ} (e : Fin m ↪ Fin d)
    (k : Frequency m) (i : Fin d) (hi : i ∉ Set.range e) : extendFrequency e k i = 0 :=
  Function.extend_apply' _ _ _ hi

lemma weight_extendFrequency {m d : ℕ} (e : Fin m ↪ Fin d) (p : ℝ) (k : Frequency m) :
    weight p (extendFrequency e k) = weight p k := by
  unfold weight
  congr 1
  exact (Fintype.sum_of_injective e e.injective
    (fun j => (k j:ℝ)^2) (fun i => (extendFrequency e k i:ℝ)^2)
    (fun i hi => by rw [extendFrequency_outside e k i hi]; norm_num)
    (fun j => by rw [extendFrequency_apply])).symm

lemma componentCoeff_extendFrequency {m d : ℕ} (e : Fin m ↪ Fin d)
    (N : Fin d → ℕ) (k : Frequency m) :
    componentCoeff N (extendFrequency e k) = componentCoeff (fun j => N (e j)) k := by
  unfold componentCoeff binomialProduct
  exact (Fintype.prod_of_injective e e.injective
    (fun j => binomialCoeffReal (N (e j)) (k j).natAbs)
    (fun i => binomialCoeffReal (N i) (extendFrequency e k i).natAbs)
    (fun i hi => by rw [extendFrequency_outside e k i hi]; simp)
    (fun j => by rw [extendFrequency_apply])).symm

lemma rho_fourier_extendFrequency {m d : ℕ} (e : Fin m ↪ Fin d)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (k : Frequency m) :
    densityFourier (CosineMixtureApproximation.rho w N) (extendFrequency e k) =
      densityFourier (CosineMixtureApproximation.rho w (fun n j => N n (e j))) k := by
  simp only [rho_fourier w N hw hs, componentCoeff_extendFrequency,
    rho_fourier w (fun n j => N n (e j)) hw hs]

lemma extendFrequency_range {m d : ℕ} (e : Fin m ↪ Fin d) (k : Frequency d) :
    k ∈ Set.range (extendFrequency e) ↔ ∀ i ∉ Set.range e, k i = 0 := by
  constructor
  · rintro ⟨l, rfl⟩ i hi
    exact extendFrequency_outside e l i hi
  · intro h
    refine ⟨fun j => k (e j), ?_⟩
    funext i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      exact extendFrequency_apply e _ j
    · rw [extendFrequency_outside e _ i hi, h i hi]

/-- A masked Fourier sum is precisely the energy in the retained coordinates,
also when either sum diverges. -/
theorem weightedEnergyENN_embedding {m d : ℕ} (e : Fin m ↪ Fin d) (p : ℝ)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    weightedEnergyENN (fun k => if ∀ i ∉ Set.range e, k i = 0 then weight p k else 0)
      (CosineMixtureApproximation.rho w N) =
    weightedEnergyENN (weight p) (CosineMixtureApproximation.rho w (fun n j => N n (e j))) := by
  classical
  let f : Frequency d → ℝ≥0∞ := fun k => ENNReal.ofReal
    ((if ∀ i ∉ Set.range e, k i = 0 then weight p k else 0) *
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
  rw [if_pos hk, weight_extendFrequency, rho_fourier_extendFrequency e w N hw hs]

#print axioms weightedEnergyENN_embedding
end BecknerOnofri.CosineMixtureTransfer
