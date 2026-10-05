import BecknerOnofri.EntropyTailCouplingComparison
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Equiv.Basic

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail.DiscreteLayers

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem permutation_coordinate_sum (f : α → ℝ) (i j : α) :
    (∑ σ : Equiv.Perm α, f (σ i)) = ∑ σ : Equiv.Perm α, f (σ j) := by
  have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap i j)) (fun σ : Equiv.Perm α => f (σ j))
  simpa using h

theorem permutation_average (f : α → ℝ) (i : α) :
    (Fintype.card (Equiv.Perm α) : ℝ)⁻¹*(∑ σ : Equiv.Perm α, f (σ i)) =
      (Fintype.card α : ℝ)⁻¹*(∑ j, f j) := by
  haveI : Nonempty α := ⟨i⟩
  have hp : (Fintype.card (Equiv.Perm α) : ℝ) ≠ 0 := by positivity
  have ha : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have h : (Fintype.card α : ℝ)*(∑ σ : Equiv.Perm α, f (σ i)) =
      (Fintype.card (Equiv.Perm α) : ℝ)*(∑ j, f j) := by
    calc
      _ = ∑ j : α, ∑ σ : Equiv.Perm α, f (σ j) := by
        simp_rw [← permutation_coordinate_sum f i]
        simp
      _ = ∑ σ : Equiv.Perm α, ∑ j : α, f (σ j) := Finset.sum_comm
      _ = _ := by
        simp only [Equiv.sum_comp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply (mul_left_cancel₀ (mul_ne_zero hp ha))
  field_simp
  nlinarith [h]

/-- The exact finite permutation inequality used in the manuscript's layer-cake step. -/
theorem permutation_product_comparison {d : ℕ} (hd : 0 < d)
    (f : Fin d → ℕ → ℝ) (hf : ∀ i n, 0 ≤ f i n) (hmono : ∀ i, Monotone (f i))
    (L : Fin d → ℕ) :
    (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹*
      (∑ σ : Equiv.Perm (Fin d), ∏ i, f i (L (σ i))) ≤
        (d : ℝ)⁻¹*(∑ j : Fin d, ∏ i, f i (L j)) := by
  classical
  let M := Finset.univ.sup L
  have hL (j : Fin d) : L j ≤ M := Finset.le_sup (Finset.mem_univ j)
  have hm (i : Fin d) (n : ℕ) :
      (∑ σ : Equiv.Perm (Fin d), (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹*
        (if n ≤ L (σ i) then 1 else 0)) =
      ∑ j : Fin d, (d : ℝ)⁻¹*(if n ≤ L j then 1 else 0) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simpa only [Fintype.card_fin] using permutation_average (fun j => if n ≤ L j then (1 : ℝ) else 0) i
  have h := product_comparison hd f hf hmono
    (fun _σ : Equiv.Perm (Fin d) => (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹)
    (fun _ => by positivity) (fun _j : Fin d => (d : ℝ)⁻¹)
    (fun i σ => L (σ i)) (fun i σ => hL (σ i)) L hL hm
  simpa only [← Finset.mul_sum] using h

#print axioms permutation_product_comparison
end BecknerOnofri.HighDim.EntropyTail.DiscreteLayers
