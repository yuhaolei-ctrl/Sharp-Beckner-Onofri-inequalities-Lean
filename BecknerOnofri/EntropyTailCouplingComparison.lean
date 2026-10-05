module

public import BecknerOnofri.EntropyTailDiscreteLayers
public import Mathlib.Data.Finset.Max

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail.DiscreteLayers

variable {Ω J : Type*} [Fintype Ω] [Fintype J]

/-- The nested-level-set comparison underlying the source's layer-cake argument. -/
theorem intersection_comparison {d : ℕ} (hd : 0 < d)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (v : J → ℝ)
    (X : Fin d → Ω → ℕ) (L : J → ℕ)
    (hmarginal : ∀ i n, (∑ ω, w ω*(if n ≤ X i ω then 1 else 0)) =
      ∑ j, v j*(if n ≤ L j then 1 else 0)) (r : Fin d → ℕ) :
    (∑ ω, w ω*(if ∀ i, r i ≤ X i ω then 1 else 0)) ≤
      ∑ j, v j*(if ∀ i, r i ≤ L j then 1 else 0) := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  calc
    _ ≤ ∑ ω, w ω*(if r i ≤ X i ω then 1 else 0) := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases h : ∀ i, r i ≤ X i ω
      · simp only [if_pos h, if_pos (h i), le_refl]
      · rw [if_neg h, mul_zero]
        split_ifs <;> simp only [mul_one, mul_zero]
        · exact hw ω
        · exact le_rfl
    _ = ∑ j, v j*(if r i ≤ L j then 1 else 0) := hmarginal i (r i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have he : (∀ k, r k ≤ L j) ↔ r i ≤ L j :=
        ⟨fun h => h i, fun h k => (hmax k (Finset.mem_univ k)).trans h⟩
      by_cases hh : r i ≤ L j
      · rw [if_pos hh, if_pos (he.mpr hh)]
      · rw [if_neg hh, if_neg (fun h => hh (he.mp h))]

theorem weighted_expansion {d M : ℕ} (f : Fin d → ℕ → ℝ)
    (X : Fin d → Ω → ℕ) (hX : ∀ i ω, X i ω ≤ M) (w : Ω → ℝ) :
    (∑ ω, w ω*∏ i, f i (X i ω)) =
      ∑ r : Fin d → Fin (M+1), (∏ i, increment (f i) (r i))*
        (∑ ω, w ω*(if ∀ i, (r i : ℕ) ≤ X i ω then 1 else 0)) := by
  classical
  have he (ω : Ω) := product_expansion f (fun i => X i ω) (fun i => hX i ω)
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Finite comonotone coupling maximizes every product of nonnegative increasing factors.
This is the finite layer-cake statement used before integrating the heat kernel. -/
theorem product_comparison {d M : ℕ} (hd : 0 < d)
    (f : Fin d → ℕ → ℝ) (hf : ∀ i n, 0 ≤ f i n) (hmono : ∀ i, Monotone (f i))
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (v : J → ℝ)
    (X : Fin d → Ω → ℕ) (hX : ∀ i ω, X i ω ≤ M)
    (L : J → ℕ) (hL : ∀ j, L j ≤ M)
    (hmarginal : ∀ i n, (∑ ω, w ω*(if n ≤ X i ω then 1 else 0)) =
      ∑ j, v j*(if n ≤ L j then 1 else 0)) :
    (∑ ω, w ω*∏ i, f i (X i ω)) ≤ ∑ j, v j*∏ i, f i (L j) := by
  classical
  rw [weighted_expansion f X hX w,
    weighted_expansion f (fun _ j => L j) (fun _ j => hL j) v]
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left
    (intersection_comparison hd w hw v X L hmarginal (fun i => (r i : ℕ)))
  exact Finset.prod_nonneg (fun i _ => increment_nonneg (hf i) (hmono i) _)

#print axioms product_comparison
end BecknerOnofri.HighDim.EntropyTail.DiscreteLayers
