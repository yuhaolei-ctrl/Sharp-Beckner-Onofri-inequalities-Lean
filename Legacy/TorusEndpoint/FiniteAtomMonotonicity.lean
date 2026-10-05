module

public import Legacy.TorusEndpoint.FiniteAtomCoefficients

@[expose] public section

/-! Monotonicity of actual finite-atom coefficients, with no infinite-cone summability premise. -/

open Legacy.TorusEndpoint.FiniteCone
open scoped BigOperators

namespace Legacy.TorusEndpoint.FiniteAtomCoefficients

theorem decompositions_subset {d : ℕ} (atoms larger : List (Vec d)) (w v k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hv : ∀ x ∈ larger, 0 < eval v x)
    (hsub : ∀ x ∈ atoms, x ∈ larger) :
    decompositions atoms w k ⊆ decompositions larger v k := by
  intro xs hx
  obtain ⟨hm, hs⟩ := (mem_decompositions_iff atoms w k hw xs).mp hx
  exact (mem_decompositions_iff larger v k hv xs).mpr
    ⟨fun x hx => hsub x (hm x hx), hs⟩

theorem coefficient_mono_atoms {d : ℕ} (atoms larger : List (Vec d)) (w v k : Vec d)
    (a : Vec d → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hv : ∀ x ∈ larger, 0 < eval v x)
    (hsub : ∀ x ∈ atoms, x ∈ larger) (ha : ∀ x ∈ larger, 0 ≤ a x) :
    coefficient atoms w a q k ≤ coefficient larger v a q k := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg (decompositions_subset atoms larger w v k hw hv hsub)
  intro xs hx _
  have hm := ((mem_decompositions_iff larger v k hv xs).mp hx).1
  exact wordWeight_nonneg a hq xs (fun x hx => ha x (hm x hx))

theorem wordWeight_mono_weights {d : ℕ} (a b : Vec d → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (xs : List (Vec d)) (ha : ∀ x ∈ xs, 0 ≤ a x) (hab : ∀ x ∈ xs, a x ≤ b x) :
    wordWeight a q xs ≤ wordWeight b q xs := by
  exact mul_le_mul_of_nonneg_left (List.prod_map_le_prod_map₀ a b ha hab)
    (scalarExpTerm_nonneg hq _)

theorem coefficient_mono_weights {d : ℕ} (atoms : List (Vec d)) (w k : Vec d)
    (a b : Vec d → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hw : ∀ x ∈ atoms, 0 < eval w x)
    (ha : ∀ x ∈ atoms, 0 ≤ a x) (hab : ∀ x ∈ atoms, a x ≤ b x) :
    coefficient atoms w a q k ≤ coefficient atoms w b q k := by
  apply Finset.sum_le_sum
  intro xs hx
  have hm := ((mem_decompositions_iff atoms w k hw xs).mp hx).1
  exact wordWeight_mono_weights a b hq xs
    (fun x hx => ha x (hm x hx)) (fun x hx => hab x (hm x hx))

theorem wordWeight_mono_parameter {d : ℕ} (a : Vec d → ℝ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (xs : List (Vec d)) (ha : ∀ x ∈ xs, 0 ≤ a x) :
    wordWeight a p xs ≤ wordWeight a q xs := by
  apply mul_le_mul_of_nonneg_right (scalarExpTerm_mono hp hpq _)
  apply List.prod_nonneg
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  exact ha x hx

theorem coefficient_mono_parameter {d : ℕ} (atoms : List (Vec d)) (w k : Vec d)
    (a : Vec d → ℝ) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (ha : ∀ x ∈ atoms, 0 ≤ a x) :
    coefficient atoms w a p k ≤ coefficient atoms w a q k := by
  apply Finset.sum_le_sum
  intro xs hx
  have hm := ((mem_decompositions_iff atoms w k hw xs).mp hx).1
  exact wordWeight_mono_parameter a hp hpq xs (fun x hx => ha x (hm x hx))

theorem coefficient_zero_outside_positive_cone {d : ℕ}
    (atoms : List (Vec d)) (w k : Vec d) (a : Vec d → ℝ) (q : ℝ)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hpos : ∀ x ∈ atoms, LexPositive x)
    (hk : k ≠ zero) (hn : ¬ LexPositive k) : coefficient atoms w a q k = 0 := by
  classical
  have he : decompositions atoms w k = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro xs hx
    obtain ⟨hm, hs⟩ := (mem_decompositions_iff atoms w k hw xs).mp hx
    have hne : xs ≠ [] := by
      intro hnil
      subst xs
      exact hk hs.symm
    exact hn (hs ▸ positive_sum xs hne (fun x hx => hpos x (hm x hx)))
  simp [coefficient, he]

end Legacy.TorusEndpoint.FiniteAtomCoefficients
