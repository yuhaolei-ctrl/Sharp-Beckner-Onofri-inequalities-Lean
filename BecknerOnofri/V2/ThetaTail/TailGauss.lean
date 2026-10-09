module

public import BecknerOnofri.V2.ThetaTail.Binomial
public import BecknerOnofri.V2.ThetaTail.LatticeProd

@[expose] public section

/-! # `T_n ≤ G(x)` and `T_n ≤ a_n(2) e^{4x} G(x)` (`d12-tail-eq:binomgauss`)

`x = (n+1/2)^{-1}`.  Unconditional. -/
noncomputable section
open Finset
namespace BecknerOnofri.V2.ThetaTail

lemma prod_aCoef_le (n : ℕ) (k : Fin 12 → ℤ) :
    ∏ i, aCoef n (k i) ≤ Real.exp (-xn n * latticeNormSq k) := by
  rw [exp_latticeNormSq]
  refine Finset.prod_le_prod₀ (fun i _ => aCoef_nonneg n _) (fun i _ => ?_)
  have := aCoef_le_exp n (k i)
  rwa [neg_mul]

lemma prod_aCoef_le_two (n : ℕ) (k : Fin 12 → ℤ) (hk : k ∉ cube12) :
    ∏ i, aCoef n (k i) ≤ aCoef n 2 * Real.exp (4 * xn n) * Real.exp (-xn n * latticeNormSq k) := by
  rw [mem_cube12_iff] at hk
  simp only [not_forall, not_or] at hk
  obtain ⟨i, h1, h0, h2⟩ := hk
  have hi : 2 ≤ (k i).natAbs := by omega
  rw [exp_latticeNormSq, ← Finset.mul_prod_erase Finset.univ (fun j => aCoef n (k j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => Real.exp (-xn n * ((k j : ℤ) : ℝ) ^ 2))
      (Finset.mem_univ i)]
  have hA := aCoef_le_two n (k i) hi
  have hB : ∏ j ∈ Finset.univ.erase i, aCoef n (k j)
      ≤ ∏ j ∈ Finset.univ.erase i, Real.exp (-xn n * ((k j : ℤ) : ℝ) ^ 2) := by
    refine Finset.prod_le_prod₀ (fun j _ => aCoef_nonneg n _) (fun j _ => ?_)
    have := aCoef_le_exp n (k j)
    rwa [neg_mul]
  have hBnn : 0 ≤ ∏ j ∈ Finset.univ.erase i, aCoef n (k j) :=
    Finset.prod_nonneg fun j _ => aCoef_nonneg n _
  have e : aCoef n 2 * Real.exp (4 * xn n) * (Real.exp (-xn n * ((k i : ℤ) : ℝ) ^ 2) *
      ∏ j ∈ Finset.univ.erase i, Real.exp (-xn n * ((k j : ℤ) : ℝ) ^ 2))
      = (aCoef n 2 * Real.exp (4 * xn n) * Real.exp (-xn n * ((k i : ℤ) : ℝ) ^ 2)) *
        ∏ j ∈ Finset.univ.erase i, Real.exp (-xn n * ((k j : ℤ) : ℝ) ^ 2) := by ring
  rw [e]
  have hA' : aCoef n (k i) ≤ aCoef n 2 * Real.exp (4 * xn n) * Real.exp (-xn n * ((k i : ℤ) : ℝ) ^ 2) := by
    rwa [neg_mul]
  exact mul_le_mul hA' hB hBnn (by
    have := aCoef_nonneg n 2
    positivity)

lemma Tn_summand_nonneg (n : ℕ) (k : Fin 12 → ℤ) :
    0 ≤ (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef n (k i)) k :=
  Set.indicator_nonneg (fun k _ => mul_nonneg (inv_nonneg.2 (pow_nonneg (Real.sqrt_nonneg _) _))
    (Finset.prod_nonneg fun i _ => aCoef_nonneg n _)) k

lemma Tn_summand_le (n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ k : Fin 12 → ℤ, k ∉ cube12 →
      ∏ i, aCoef n (k i) ≤ c * Real.exp (-xn n * latticeNormSq k)) (k : Fin 12 → ℤ) :
    (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef n (k i)) k
      ≤ c * gaussSummand (xn n) k := by
  unfold gaussSummand
  by_cases hk : k ∈ cube12ᶜ
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
    have h := hbound k hk
    have hpos : 0 ≤ (latticeNorm k ^ 12)⁻¹ := inv_nonneg.2 (pow_nonneg (Real.sqrt_nonneg _) _)
    calc (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef n (k i)
        ≤ (latticeNorm k ^ 12)⁻¹ * (c * Real.exp (-xn n * latticeNormSq k)) :=
          mul_le_mul_of_nonneg_left h hpos
      _ = c * (Real.exp (-xn n * latticeNormSq k) / latticeNorm k ^ 12) := by
          rw [div_eq_mul_inv]; ring
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk]; simp

lemma summable_Tn_summand (n : ℕ) :
    Summable (fun k : Fin 12 → ℤ =>
      (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef n (k i)) k) := by
  refine Summable.of_nonneg_of_le (Tn_summand_nonneg n) (fun k => ?_)
    ((summable_gaussSummand (xn_pos n)).mul_left 1)
  have := Tn_summand_le n 1 zero_le_one (fun k _ => by
    simpa using prod_aCoef_le n k) k
  simpa using this

/-- `T_n ≤ G(x)`, `x = (n+1/2)^{-1}` -/
theorem Tn_le_G (n : ℕ) : Tn n ≤ G (xn n) := by
  unfold Tn G
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_Tn_summand n) (summable_gaussSummand (xn_pos n))
  have := Tn_summand_le n 1 zero_le_one (fun k _ => by simpa using prod_aCoef_le n k) k
  simpa using this

/-- `T_n ≤ a_n(2) e^{4x} G(x)` -/
theorem Tn_le_two_G (n : ℕ) : Tn n ≤ aCoef n 2 * Real.exp (4 * xn n) * G (xn n) := by
  unfold Tn G
  have hc : 0 ≤ aCoef n 2 * Real.exp (4 * xn n) :=
    mul_nonneg (aCoef_nonneg n 2) (Real.exp_pos _).le
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_Tn_summand n)
    ((summable_gaussSummand (xn_pos n)).mul_left _)
  exact Tn_summand_le n _ hc (fun k hk => prod_aCoef_le_two n k hk) k

end BecknerOnofri.V2.ThetaTail
