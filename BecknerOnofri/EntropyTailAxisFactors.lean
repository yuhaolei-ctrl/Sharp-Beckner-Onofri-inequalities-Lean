import BecknerOnofri.EntropyTailScalarBasic

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

theorem scalarCoefficient_nonneg (n j : ℕ) : 0 ≤ scalarCoefficient n j := by
  unfold scalarCoefficient
  positivity

theorem scalarCoefficient_monotone (j : ℕ) : Monotone (fun n => scalarCoefficient n j) := by
  apply monotone_nat_of_le_succ
  intro n
  have hr := Legacy.D10.binomialCoeff_row_step n j
  have hn : 0 ≤ ((n : ℚ)+1)^2*
      (Legacy.D10.binomialCoeff (n+1) j-Legacy.D10.binomialCoeff n j) := by
    rw [hr]
    exact mul_nonneg (sq_nonneg _) (Legacy.D10.binomialCoeff_nonneg _ _)
  have h : Legacy.D10.binomialCoeff n j ≤ Legacy.D10.binomialCoeff (n+1) j :=
    sub_nonneg.mp (nonneg_of_mul_nonneg_right hn (by positivity))
  simp only [scalarCoefficient_eq, Legacy.D10.binomialCoeffReal]
  exact_mod_cast h

/-- The two nonnegative factors g and h in the source's unequal-index step. -/
def axisLow (s : ℝ) (n : ℕ) : ℝ := 1+2*scalarCoefficient n 1*Real.exp (-s)

def axisHigh (s : ℝ) (n : ℕ) : ℝ :=
  2*∑' j : ℕ, scalarCoefficient n (j+2)*Real.exp (-s*(j+2 : ℝ)^2)

theorem axisHigh_summable (s : ℝ) (n : ℕ) :
    Summable (fun j : ℕ => scalarCoefficient n (j+2)*Real.exp (-s*(j+2 : ℝ)^2)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (n+1))
  intro j hj
  have hj' : n < j+2 := by simp only [Finset.mem_range, not_lt] at hj; omega
  rw [scalarCoefficient_eq]
  have hz : Legacy.D10.binomialCoeffReal n (j+2) = 0 := by
    unfold Legacy.D10.binomialCoeffReal
    rw [Legacy.D10.binomialCoeff_eq_zero hj']
    norm_num
  rw [hz, zero_mul]

theorem axisLow_nonneg (s : ℝ) (n : ℕ) : 0 ≤ axisLow s n := by
  dsimp only [axisLow]
  have h := scalarCoefficient_nonneg n 1
  positivity

theorem axisHigh_nonneg (s : ℝ) (n : ℕ) : 0 ≤ axisHigh s n :=
  mul_nonneg (by norm_num) (tsum_nonneg (fun j =>
    mul_nonneg (scalarCoefficient_nonneg n (j+2)) (Real.exp_pos _).le))

theorem axisLow_monotone (s : ℝ) : Monotone (axisLow s) := by
  intro n m hnm
  dsimp only [axisLow]
  have h := mul_le_mul_of_nonneg_right (scalarCoefficient_monotone 1 hnm) (Real.exp_pos (-s)).le
  nlinarith

theorem axisHigh_monotone (s : ℝ) : Monotone (axisHigh s) := by
  intro n m hnm
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply (axisHigh_summable s n).tsum_le_tsum _ (axisHigh_summable s m)
  intro j
  exact mul_le_mul_of_nonneg_right (scalarCoefficient_monotone (j+2) hnm) (Real.exp_pos _).le

#print axioms scalarCoefficient_monotone
#print axioms axisHigh_monotone
end BecknerOnofri.HighDim.EntropyTail
