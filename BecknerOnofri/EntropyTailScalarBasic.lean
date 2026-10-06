module

public import BecknerOnofri.EntropyTailDefinitions
public import BecknerOnofri.EntropyTailBudget

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.D10

theorem scalarCoefficient_eq (n j : ℕ) : scalarCoefficient n j = binomialCoeffReal n j := by
  simp [scalarCoefficient, binomialCoeffReal, binomialCoeff]

theorem scalarBudget_eq (n : ℕ) : scalarBudget n = tailBudget n := by
  simp only [scalarBudget, tailBudget, scalarCoefficient_eq]

theorem scalarTail_summable (n : ℕ) : Summable (fun k : Frequency 12 =>
    scalarTailWeight k * ∏ i : Fin 12, scalarCoefficient n (k i).natAbs) := by
  simpa only [RandomRectangles.componentCoeff, binomialProduct, scalarCoefficient_eq] using
    RandomRectangles.summable_weighted_component (fun _ : Fin 12 => n) scalarTailWeight

theorem scalarTail_eq_finite_sum (n : ℕ) : scalarTail n =
    ∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => n),
      scalarTailWeight k * ∏ i : Fin 12, scalarCoefficient n (k i).natAbs := by
  apply tsum_eq_sum
  intro k hk
  have h := RandomRectangles.componentCoeff_eq_zero hk
  simp only [RandomRectangles.componentCoeff, binomialProduct, ← scalarCoefficient_eq] at h
  rw [h, mul_zero]

theorem scalarTail_nonneg (n : ℕ) : 0 ≤ scalarTail n := by
  apply tsum_nonneg
  intro k
  apply mul_nonneg
  · unfold scalarTailWeight
    split_ifs <;> positivity
  · exact Finset.prod_nonneg (fun i _ => by unfold scalarCoefficient; positivity)

theorem scalarTail_zero_of_le_one {n : ℕ} (hn : n ≤ 1) : scalarTail n = 0 := by
  unfold scalarTail
  trans ∑' _ : Frequency 12, (0 : ℝ)
  · apply tsum_congr
    intro k
    unfold scalarTailWeight
    split_ifs with hk
    · obtain ⟨i,hi⟩ := hk
      have hc : scalarCoefficient n (k i).natAbs = 0 := by
        rw [scalarCoefficient_eq]
        exact RandomRectangles.coeff_eq_zero (by omega)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hc, mul_zero]
    · exact zero_mul _
  · simp

theorem scalarBudget_zero : scalarBudget 0 = 0 := by
  norm_num [scalarBudget, scalarCoefficient, harmonic, Finset.sum_range_succ, Nat.choose]

theorem scalarBudget_one : scalarBudget 1 = 0 := by
  norm_num [scalarBudget, scalarCoefficient, harmonic, Finset.sum_range_succ, Nat.choose]

theorem scalarBudget_two : scalarBudget 2 = 21/250 := by
  norm_num [scalarBudget, scalarCoefficient, harmonic, Finset.sum_range_succ, Nat.choose]

theorem scalarTail_le_budget_small {n : ℕ} (hn : n ≤ 1) : scalarTail n ≤ scalarBudget n := by
  rw [scalarTail_zero_of_le_one hn]
  have h : n = 0 ∨ n = 1 := by omega
  rcases h with rfl | rfl
  · rw [scalarBudget_zero]
  · rw [scalarBudget_one]

theorem tailBudget_step (n : ℕ) :
    tailBudget (n+1)-tailBudget n =
      12*(n:ℝ)*((67/100)*((n:ℝ)-1)+4*(21/500)) /
        (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)) := by
  rw [tailBudget, tailBudget, first_coefficient, first_coefficient,
    second_coefficient, second_coefficient, harmonic_succ]
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  have h3 : (n:ℝ)+3 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem tailBudget_strict_step (n : ℕ) (hn : 1 ≤ n) : tailBudget n < tailBudget (n+1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 12*(n:ℝ)*((67/100)*((n:ℝ)-1)+4*(21/500)) /
        (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)) := by
    apply div_pos
    · apply mul_pos
      · positivity
      · nlinarith
    · positivity
  rw [← tailBudget_step] at hpos
  linarith

/-- Exact arithmetic for the coefficients of
(1+4z/3+z^4/3)^12-(1+4z/3)^12 weighted by j^(-6).
The Fourier-lattice identification is proved in EntropyTailTwo. -/
def indexTwoShellSum : ℚ :=
  ∑ b ∈ Finset.range 13, ∑ a ∈ Finset.range (13-b),
    if b = 0 then 0 else
      (Nat.choose 12 b : ℚ) * (Nat.choose (12-b) a : ℚ) * (1/3)^b * (4/3)^a /
        ((4*b+a : ℕ) : ℚ)^6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem indexTwoShellSum_upper : indexTwoShellSum < 41963/500000 := by
  decide +kernel

#print axioms tailBudget_step
#print axioms tailBudget_strict_step
#print axioms indexTwoShellSum_upper
end BecknerOnofri.HighDim.EntropyTail

#print axioms BecknerOnofri.HighDim.EntropyTail.scalarTail_le_budget_small
#print axioms BecknerOnofri.HighDim.EntropyTail.scalarTail_eq_finite_sum
