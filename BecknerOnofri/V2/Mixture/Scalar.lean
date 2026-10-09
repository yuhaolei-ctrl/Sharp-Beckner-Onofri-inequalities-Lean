module

public import BecknerOnofri.V2.ThetaTail.RouteM.Unconditional
public import BecknerOnofri.EntropyTailMixture

@[expose] public section

/-! # From the scalar bound to the mixture estimate: scalar side (Subsubsection `subsec:section5-global-tail`)

This file connects the G07 definitions (`aCoef`, `Hn`, `Tn`, `Rn`, `cube12`, `latticeNorm`) to the
generic v1 scalar objects (`scalarCoefficient`, `harmonic`, `scalarTail`, `mixedTail`) and proves
the three scalar statements of the subsection:

* `harmonic_identity` (`eq:harmonic-identity`): `H_n = 2 ∑_{j≥1} a_n(j)/j`;
* `Rn_eq_positive` (`eq:section5-scalar-positive-budget`):
  `R_n = 3/5 a_n(2) + 16/5 a_n(3) + 81/5 ∑_{j≥4} a_n(j)/j`;
* `tail_arbitrary_indices` (`eq:section5-global-tail-arbitrary-indices`):
  `∑_{k∉cube} |k|^{-12} ∏ a_{L_i}(k_i) ≤ (1/12) ∑ T_{L_i}`.

Route notes.  `harmonic_identity` is obtained from the v1 theorem `scalarHarmonic_tsum` (which uses
`Legacy.D10.binomialCoeffReal_harmonic`), not from the written telescoping recurrence
(`eq:harmonic-coefficient-recurrence`, `eq:harmonic-binomial-telescope`).  `tail_arbitrary_indices`
is obtained from the v1 theorem `mixedTail_le_diagonal` (discrete layer-cake / permutation
comparison `DiscreteLayers`, `permutation_product_comparison`, `product_deficit_comparison`
together with the Mellin/heat representation), which is a discrete-layer version of the written
continuous layer-cake argument `eq:section5-global-layer-cake-comparison`. -/
noncomputable section
open Finset
namespace BecknerOnofri.V2.Mixture

open BecknerOnofri.V2.ThetaTail (aCoef Hn Tn Rn cube12 latticeNorm latticeNormSq)
open BecknerOnofri.HighDim.EntropyTail (scalarCoefficient scalarTail scalarTailWeight mixedTail
  mixedCoefficient outsideCube scalarHarmonic_tsum scalarHarmonic_summable mixedTail_le_diagonal)

/-! ## Bridge between the G07 notation and the v1 scalar notation -/

theorem scalarCoefficient_eq_aCoef (n j : ℕ) : scalarCoefficient n j = aCoef n (j : ℤ) := by
  simp [scalarCoefficient, aCoef]

theorem aCoef_eq_scalarCoefficient (n : ℕ) (j : ℤ) : aCoef n j = scalarCoefficient n j.natAbs := by
  simp [scalarCoefficient, aCoef]

theorem harmonic_cast_eq_Hn (n : ℕ) : ((harmonic n : ℚ) : ℝ) = Hn n := by
  induction n with
  | zero => simp [Hn]
  | succ n ih =>
    rw [harmonic_succ]
    push_cast
    rw [ih]
    simp [Hn, Finset.sum_Icc_succ_top]

theorem scalarTailWeight_eq_indicator (k : Fin 12 → ℤ) :
    scalarTailWeight k = (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹) k := by
  have hlen : HighDim.frequencyLength k = latticeNorm k := rfl
  have hiff : outsideCube k ↔ k ∈ cube12ᶜ := by
    simp only [outsideCube, cube12, Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_insert_iff, Set.mem_singleton_iff, not_forall]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by omega⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by omega⟩
  unfold scalarTailWeight
  by_cases h : outsideCube k
  · simp only [h, ↓reduceIte]
    rw [Set.indicator_of_mem (hiff.mp h), hlen]
  · simp only [h, ↓reduceIte]
    rw [Set.indicator_of_notMem (fun hh => h (hiff.mpr hh))]

theorem scalarTail_eq_Tn (n : ℕ) : scalarTail n = Tn n := by
  unfold scalarTail Tn
  apply tsum_congr
  intro k
  rw [scalarTailWeight_eq_indicator]
  by_cases hk : k ∈ cube12ᶜ
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
    simp only [aCoef_eq_scalarCoefficient]
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, zero_mul]

/-! ## The harmonic identity `eq:harmonic-identity` -/

/-- `eq:harmonic-identity`, indexed over `j ≥ 1`: `H_n = 2 ∑_{j≥1} a_n(j)/j`. -/
theorem harmonic_identity (n : ℕ) :
    Hn n = 2 * ∑' j : ℕ, aCoef n ((j : ℤ) + 1) / ((j : ℝ) + 1) := by
  have h1 := (scalarHarmonic_summable n).sum_add_tsum_nat_add 1
  have h2 := scalarHarmonic_tsum n
  rw [← harmonic_cast_eq_Hn, ← h2, ← h1]
  simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, zero_add]
  congr 2
  funext j
  rw [scalarCoefficient_eq_aCoef]
  push_cast
  rfl

/-- Summability of the harmonic series of coefficients (a finite sum, since `a_n(j) = 0` for
`j > n`). -/
theorem summable_harmonic_aCoef (n : ℕ) (c : ℕ) :
    Summable (fun j : ℕ => aCoef n (((j + c : ℕ) : ℤ)) / ((j + c : ℕ) : ℝ)) := by
  have := (scalarHarmonic_summable n).comp_injective
    (show Function.Injective (fun j : ℕ => j + c) from fun a b h => by dsimp at h; omega)
  simpa only [Function.comp_def, scalarCoefficient_eq_aCoef] using this

theorem aCoef_nonneg (n : ℕ) (j : ℤ) : 0 ≤ aCoef n j := by
  unfold aCoef
  positivity

/-! ## The nonnegative representation `eq:section5-scalar-positive-budget` -/

/-- `eq:section5-scalar-positive-budget`:
`R_n = 3/5 a_n(2) + 16/5 a_n(3) + 81/5 ∑_{j≥4} a_n(j)/j`.  Equality with the `Rn` of
`ThetaTail.Defs` (`R_n = 81/10 H_n − 81/5 a_n(1) − 15/2 a_n(2) − 11/5 a_n(3)`). -/
theorem Rn_eq_positive_nat (n : ℕ) :
    Rn n = 3 / 5 * aCoef n 2 + 16 / 5 * aCoef n 3 +
      81 / 5 * ∑' j : ℕ, aCoef n (((j + 4 : ℕ) : ℤ)) / ((j + 4 : ℕ) : ℝ) := by
  have hs := (scalarHarmonic_summable n).sum_add_tsum_nat_add 4
  have h2 := scalarHarmonic_tsum n
  have e1 : (∑' j : ℕ, scalarCoefficient n j / (j : ℝ)) =
      aCoef n 1 + aCoef n 2 / 2 + aCoef n 3 / 3 +
        ∑' j : ℕ, aCoef n (((j + 4 : ℕ) : ℤ)) / ((j + 4 : ℕ) : ℝ) := by
    rw [← hs]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, scalarCoefficient_eq_aCoef,
      Nat.cast_zero, div_zero, zero_add, Nat.cast_one, Nat.cast_ofNat, div_one]
  have hH : Hn n = 2 * (aCoef n 1 + aCoef n 2 / 2 + aCoef n 3 / 3 +
        ∑' j : ℕ, aCoef n (((j + 4 : ℕ) : ℤ)) / ((j + 4 : ℕ) : ℝ)) := by
    rw [← e1, ← harmonic_cast_eq_Hn, ← h2]
  unfold Rn
  rw [hH]
  ring

/-- `eq:section5-scalar-positive-budget` with the summation index written as `j + 4`. -/
theorem Rn_eq_positive (n : ℕ) :
    Rn n = 3 / 5 * aCoef n 2 + 16 / 5 * aCoef n 3 +
      81 / 5 * ∑' j : ℕ, aCoef n ((j : ℤ) + 4) / ((j : ℝ) + 4) := by
  rw [Rn_eq_positive_nat]
  push_cast
  rfl

theorem Rn_nonneg (n : ℕ) : 0 ≤ Rn n := by
  rw [Rn_eq_positive_nat]
  have : 0 ≤ ∑' j : ℕ, aCoef n (((j + 4 : ℕ) : ℤ)) / ((j + 4 : ℕ) : ℝ) :=
    tsum_nonneg fun j => div_nonneg (aCoef_nonneg _ _) (by positivity)
  have h2 := aCoef_nonneg n 2
  have h3 := aCoef_nonneg n 3
  positivity

/-! ## The arbitrary-indices statement `eq:section5-global-tail-arbitrary-indices` -/

theorem mixedTail_eq_sum (L : Fin 12 → ℕ) :
    mixedTail L =
      ∑' k : Fin 12 → ℤ,
        (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef (L i) (k i)) k := by
  unfold HighDim.EntropyTail.mixedTail
  apply tsum_congr
  intro k
  rw [scalarTailWeight_eq_indicator]
  by_cases hk : k ∈ cube12ᶜ
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
    simp only [mixedCoefficient, aCoef_eq_scalarCoefficient]
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, zero_mul]

/-- `eq:section5-global-tail-arbitrary-indices`: for every `L ∈ ℕ₀^{12}`,
`∑_{k∉{-1,0,1}^{12}} |k|^{-12} ∏_i a_{L_i}(k_i) ≤ (1/12) ∑_i T_{L_i}`. -/
theorem tail_arbitrary_indices (L : Fin 12 → ℕ) :
    ∑' k : Fin 12 → ℤ,
        (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef (L i) (k i)) k ≤
      (1 / 12 : ℝ) * ∑ i : Fin 12, Tn (L i) := by
  rw [← mixedTail_eq_sum]
  simpa only [scalarTail_eq_Tn] using mixedTail_le_diagonal L

end BecknerOnofri.V2.Mixture
