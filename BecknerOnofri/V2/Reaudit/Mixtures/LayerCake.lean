module

public import BecknerOnofri.EntropyTailMixedMellin
public import BecknerOnofri.V2.Mixture.Scalar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! # The continuous layer-cake comparison `eq:section5-global-layer-cake-comparison` (S043)

The manuscript proves, for nonnegative nondecreasing `f_i` and a uniformly random permutation `σ`,
```
E[∏_i f_i(L_{σ(i)})]
   = ∫_{[0,∞)^{12}} P(⋂_i {f_i(L_{σ(i)}) > y_i}) dy
   ≤ ∫_{[0,∞)^{12}} min_i (1/12) ∑_j 1_{f_i(L_j) > y_i} dy
   = (1/12) ∑_j ∏_i f_i(L_j),
```
by the layer-cake formula for the Lebesgue measure on `[0,∞)^{12}`, the bound of an intersection
probability by its smallest member, and nestedness of the sets `{j : f_i(L_j) > y_i}`.

The repository's route (`DiscreteLayers.permutation_product_comparison`) replaces the Lebesgue
integral by a finite sum over integer layers.  This module proves the comparison with the
**continuous layer-cake**: the product `∏_i a_i` is the Lebesgue volume of the box
`∏_i [0, a_i)` (`Real.volume_pi_Ico`), the average over `σ` and the diagonal average are compared
pointwise in `y ∈ ℝ^d`, and the comparison is integrated.  Thereafter the printed
subset expansion (`DiscreteLayers.choice_sum_deficit`, `permutation_deficit_identity`,
`diagonal_deficit_identity`: purely algebraic, no layers) and the Gaussian-gamma representation
(`mixedTail_eq_heatIntegral`) are reused, so that `tail_arbitrary_indices_direct` has the type of
`Mixture.tail_arbitrary_indices` but contains no discrete layer declaration
(`DiscreteLayers.permutation_product_comparison`/`product_comparison`/`product_deficit_comparison`
are not used). -/

noncomputable section
open Finset MeasureTheory
open scoped BigOperators

namespace BecknerOnofri.V2.Reaudit.Mixtures

/-- The box `∏_i [0, a_i)`. -/
def rbox {d : ℕ} (a : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico 0 (a i)

theorem measurableSet_rbox {d : ℕ} (a : Fin d → ℝ) : MeasurableSet (rbox a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_rbox {d : ℕ} (a : Fin d → ℝ) :
    volume (rbox a) = ∏ i, ENNReal.ofReal (a i) := by
  unfold rbox
  rw [Real.volume_pi_Ico]
  simp

theorem volume_rbox_ne_top {d : ℕ} (a : Fin d → ℝ) : volume (rbox a) ≠ ⊤ := by
  rw [volume_rbox]
  exact (ENNReal.prod_lt_top (fun i _ => ENNReal.ofReal_lt_top)).ne

theorem integrable_rbox_indicator {d : ℕ} (a : Fin d → ℝ) :
    Integrable ((rbox a).indicator (1 : (Fin d → ℝ) → ℝ)) volume := by
  rw [integrable_indicator_iff (measurableSet_rbox a)]
  exact integrableOn_const (volume_rbox_ne_top a)

/-- The layer-cake formula for a product: `∏_i a_i = ∫_{ℝ^d} 1_{⋂_i {y_i < a_i}, y ≥ 0} dy`. -/
theorem integral_rbox_indicator {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∫ y, (rbox a).indicator (1 : (Fin d → ℝ) → ℝ) y = ∏ i, a i := by
  rw [integral_indicator_one (measurableSet_rbox a)]
  simp only [Measure.real, volume_rbox, ENNReal.toReal_prod, ENNReal.toReal_ofReal (ha _)]

/-! ## Nested sets and the minimum bound -/

theorem exists_min_nested {d : ℕ} (hd : 0 < d) (A : Fin d → Finset (Fin d))
    (hn : ∀ i i', A i ⊆ A i' ∨ A i' ⊆ A i) : ∃ i0, ∀ i, A i0 ⊆ A i := by
  obtain ⟨i0, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => (A i).card)
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  refine ⟨i0, fun i => ?_⟩
  rcases hn i0 i with h | h
  · exact h
  · have := Finset.eq_of_subset_of_card_le h (hmin i (Finset.mem_univ _))
    rw [this]

/-- For nested sets `A_i ⊆ Fin d`, the probability under a uniform random permutation of
`⋂_i {σ(i) ∈ A_i}` is at most the smallest of the probabilities, which equals the density of
`⋂_i A_i`:  `P_σ(∀ i, σ i ∈ A_i) ≤ min_i |A_i|/d = |⋂_i A_i|/d`. -/
theorem perm_indicator_le {d : ℕ} (hd : 0 < d) (A : Fin d → Finset (Fin d))
    (hn : ∀ i i', A i ⊆ A i' ∨ A i' ⊆ A i) :
    (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin d), (if ∀ i, σ i ∈ A i then (1 : ℝ) else 0) ≤
      (d : ℝ)⁻¹ * ∑ j : Fin d, (if ∀ i, j ∈ A i then (1 : ℝ) else 0) := by
  classical
  obtain ⟨i0, hi0⟩ := exists_min_nested hd A hn
  have h1 : (∑ σ : Equiv.Perm (Fin d), (if ∀ i, σ i ∈ A i then (1 : ℝ) else 0)) ≤
      ∑ σ : Equiv.Perm (Fin d), (if σ i0 ∈ A i0 then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro σ _
    by_cases h : ∀ i, σ i ∈ A i
    · simp [h, h i0]
    · simp only [h, ite_false]
      split_ifs <;> norm_num
  have h2 : (∑ j : Fin d, (if ∀ i, j ∈ A i then (1 : ℝ) else 0)) =
      ∑ j : Fin d, (if j ∈ A i0 then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j ∈ A i0
    · have : ∀ i, j ∈ A i := fun i => hi0 i h
      simp [h, this]
    · have : ¬ ∀ i, j ∈ A i := fun hh => h (hh i0)
      simp [h, this]
  have hpos : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    positivity
  have hav := BecknerOnofri.HighDim.EntropyTail.DiscreteLayers.permutation_average
    (fun j : Fin d => if j ∈ A i0 then (1 : ℝ) else 0) i0
  rw [h2]
  calc (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin d), (if ∀ i, σ i ∈ A i then (1 : ℝ) else 0)
      ≤ (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin d), (if σ i0 ∈ A i0 then (1 : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left h1 hpos.le
    _ = (d : ℝ)⁻¹ * ∑ j : Fin d, (if j ∈ A i0 then (1 : ℝ) else 0) := by
        simpa only [Fintype.card_fin] using hav

/-- The sets `{j : y_i < f_i(L_j)}` (with `y_i ≥ 0`) are nested because the `f_i` are
nondecreasing. -/
theorem layer_sets_nested {d : ℕ} (f : Fin d → ℕ → ℝ) (hmono : ∀ i, Monotone (f i))
    (L : Fin d → ℕ) (y : Fin d → ℝ) (i i' : Fin d) :
    (Finset.univ.filter fun j => 0 ≤ y i ∧ y i < f i (L j)) ⊆
        (Finset.univ.filter fun j => 0 ≤ y i' ∧ y i' < f i' (L j)) ∨
      (Finset.univ.filter fun j => 0 ≤ y i' ∧ y i' < f i' (L j)) ⊆
        (Finset.univ.filter fun j => 0 ≤ y i ∧ y i < f i (L j)) := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Finset.not_subset] at h1 h2
  obtain ⟨j, hj, hj'⟩ := h1
  obtain ⟨j', hk, hk'⟩ := h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hj hj' hk hk'
  rcases le_total (L j) (L j') with hle | hle
  · -- `j ∈ A_i`, `L j ≤ L j'`, so `j' ∈ A_i`
    have := hmono i hle
    have := hk' hj.1
    linarith [hj.2]
  · have := hmono i' hle
    have := hj' hk.1
    linarith [hk.2]

/-- The continuous layer-cake permutation comparison, the statement of
`DiscreteLayers.permutation_product_comparison`:
`(1/12!) ∑_σ ∏_i f_i(L_{σ(i)}) ≤ (1/d) ∑_j ∏_i f_i(L_j)`
(`eq:section5-global-layer-cake-comparison`), proved with the Lebesgue integral over `ℝ^d`. -/
theorem layer_cake_permutation_comparison {d : ℕ} (hd : 0 < d)
    (f : Fin d → ℕ → ℝ) (hf : ∀ i n, 0 ≤ f i n) (hmono : ∀ i, Monotone (f i))
    (L : Fin d → ℕ) :
    (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ *
        (∑ σ : Equiv.Perm (Fin d), ∏ i, f i (L (σ i))) ≤
      (d : ℝ)⁻¹ * (∑ j : Fin d, ∏ i, f i (L j)) := by
  classical
  set P : ℝ := (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ with hP
  have hP0 : 0 ≤ P := by positivity
  have hd0 : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  -- the layer-cake formula: every product is the volume of a box
  have hL : ∀ σ : Equiv.Perm (Fin d), ∏ i, f i (L (σ i)) =
      ∫ y, (rbox fun i => f i (L (σ i))).indicator (1 : (Fin d → ℝ) → ℝ) y := fun σ =>
    (integral_rbox_indicator _ (fun i => hf _ _)).symm
  have hR : ∀ j : Fin d, ∏ i, f i (L j) =
      ∫ y, (rbox fun i => f i (L j)).indicator (1 : (Fin d → ℝ) → ℝ) y := fun j =>
    (integral_rbox_indicator _ (fun i => hf _ _)).symm
  simp_rw [hL, hR]
  rw [← integral_finsetSum _ (fun σ _ => integrable_rbox_indicator _),
    ← integral_finsetSum _ (fun j _ => integrable_rbox_indicator _),
    ← integral_const_mul, ← integral_const_mul]
  apply integral_mono
  · exact (integrable_finsetSum _ (fun σ _ => integrable_rbox_indicator _)).const_mul _
  · exact (integrable_finsetSum _ (fun j _ => integrable_rbox_indicator _)).const_mul _
  · intro y
    -- pointwise comparison for fixed `y`
    let A : Fin d → Finset (Fin d) := fun i =>
      Finset.univ.filter fun j => 0 ≤ y i ∧ y i < f i (L j)
    have hn := layer_sets_nested f hmono L y
    have key := perm_indicator_le hd A hn
    have e1 : ∀ σ : Equiv.Perm (Fin d),
        (rbox fun i => f i (L (σ i))).indicator (1 : (Fin d → ℝ) → ℝ) y =
          if ∀ i, σ i ∈ A i then (1 : ℝ) else 0 := by
      intro σ
      simp only [rbox, A, Set.indicator_apply, Set.mem_pi, Set.mem_univ, Set.mem_Ico,
        true_implies, Finset.mem_filter, Finset.mem_univ, true_and, Pi.one_apply]
    have e2 : ∀ j : Fin d,
        (rbox fun i => f i (L j)).indicator (1 : (Fin d → ℝ) → ℝ) y =
          if ∀ i, j ∈ A i then (1 : ℝ) else 0 := by
      intro j
      simp only [rbox, A, Set.indicator_apply, Set.mem_pi, Set.mem_univ, Set.mem_Ico,
        true_implies, Finset.mem_filter, Finset.mem_univ, true_and, Pi.one_apply]
    simp only [e1, e2]
    exact key

#print axioms layer_cake_permutation_comparison

/-! ## The product-deficit comparison and the tail comparison with the continuous layer cake -/

open BecknerOnofri.HighDim.EntropyTail
open BecknerOnofri.HighDim.EntropyTail.DiscreteLayers (nonemptyChoices choiceTerm
  permutation_deficit_identity diagonal_deficit_identity)

/-- The printed subset expansion `eq:section5-global-subset-expansion` and permutation averaging,
with the continuous layer-cake comparison in place of the discrete one (statement of
`DiscreteLayers.product_deficit_comparison`). -/
theorem product_deficit_comparison_cont {d : ℕ} (hd : 0 < d) (g h : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (hh : ∀ n, 0 ≤ h n) (hgm : Monotone g) (hhm : Monotone h)
    (L : Fin d → ℕ) :
    (∏ i, (g (L i) + h (L i))) - (∏ i, g (L i)) ≤
      (d : ℝ)⁻¹ * (∑ j : Fin d, ((g (L j) + h (L j)) ^ d - (g (L j)) ^ d)) := by
  classical
  rw [← permutation_deficit_identity, ← diagonal_deficit_identity]
  apply Finset.sum_le_sum
  intro b _
  apply layer_cake_permutation_comparison hd (fun i n => if b i then h n else g n) _ _ L
  · intro i n
    split_ifs
    · exact hh n
    · exact hg n
  · intro i
    cases hb : b i <;> simpa only [hb, Bool.false_eq_true, ite_false, ite_true] using
      (show Monotone (if b i then h else g) from by cases hc : b i <;> simp [hc, hgm, hhm])

theorem mixedHeat_le_diagonal_cont {s : ℝ} (hs : 0 < s) (L : Fin 12 → ℕ) :
    mixedHeat s L ≤ (1 / 12 : ℝ) * ∑ i : Fin 12, mixedHeat s (fun _ => L i) := by
  rw [mixedHeat_product hs]
  simp_rw [mixedHeat_diagonal hs]
  simpa only [Nat.cast_ofNat, one_div] using
    product_deficit_comparison_cont (by norm_num : 0 < 12)
      (axisLow s) (axisHigh s) (axisLow_nonneg s) (axisHigh_nonneg s)
      (axisLow_monotone s) (axisHigh_monotone s) L

/-- The Gaussian-gamma integration against `s^5 ds / 120` of the pointwise comparison
(`eq:section5-global-tail-arbitrary-indices`), as in `mixedTail_le_diagonal` but with the
continuous layer cake. -/
theorem mixedTail_le_diagonal_cont (L : Fin 12 → ℕ) :
    mixedTail L ≤ (1 / 12 : ℝ) * ∑ i : Fin 12, scalarTail (L i) := by
  simp_rw [← mixedTail_diagonal, mixedTail_eq_heatIntegral]
  rw [← integral_finsetSum _ (fun i _ => normalized_mixedHeat_integrable (fun _ => L i)),
    ← integral_const_mul]
  apply integral_mono_ae (normalized_mixedHeat_integrable L)
    ((integrable_finsetSum _
      (fun i _ => normalized_mixedHeat_integrable (fun _ => L i))).const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have h := mul_le_mul_of_nonneg_left (mixedHeat_le_diagonal_cont hs0 L)
    (show 0 ≤ s ^ 5 / 120 by positivity)
  convert! h using 1
  · ring
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

open BecknerOnofri.V2.ThetaTail (aCoef Tn cube12 latticeNorm) in
/-- `eq:section5-global-tail-arbitrary-indices`, with the type of `Mixture.tail_arbitrary_indices`
and the continuous layer cake. -/
theorem tail_arbitrary_indices_direct (L : Fin 12 → ℕ) :
    ∑' k : Fin 12 → ℤ,
        (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef (L i) (k i)) k ≤
      (1 / 12 : ℝ) * ∑ i : Fin 12, Tn (L i) := by
  rw [← BecknerOnofri.V2.Mixture.mixedTail_eq_sum]
  simpa only [BecknerOnofri.V2.Mixture.scalarTail_eq_Tn] using mixedTail_le_diagonal_cont L

#print axioms tail_arbitrary_indices_direct

end BecknerOnofri.V2.Reaudit.Mixtures
