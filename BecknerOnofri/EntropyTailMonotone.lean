module

public import BecknerOnofri.EntropyTailScalarBasic

@[expose] public section

noncomputable section
namespace BecknerOnofri.HighDim.EntropyTail

theorem scalarBudget_step (n : ℕ) :
    scalarBudget (n+1)-scalarBudget n =
      12*(n:ℝ)*((27/40)*((n:ℝ)-1)+4*(21/500)) /
        (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)) := by
  simp only [scalarBudget_eq, tailBudget_step]

theorem scalarBudget_strict_step (n : ℕ) (hn : 1 ≤ n) : scalarBudget n < scalarBudget (n+1) := by
  simp only [scalarBudget_eq]
  exact tailBudget_strict_step n hn

theorem scalarBudget_monotone : Monotone scalarBudget := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n = 0
  · subst n
    norm_num only [zero_add, scalarBudget_zero, scalarBudget_one]
  · exact (scalarBudget_strict_step n (by omega)).le

#print axioms scalarBudget_monotone
end BecknerOnofri.HighDim.EntropyTail
