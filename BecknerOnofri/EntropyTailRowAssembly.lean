module

public import BecknerOnofri.EntropyTailLargeIndex

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.EntropyTail

def rationalScalarBudget (n : ℕ) : ℚ :=
  12*((21/500)*((n : ℚ)*(n-1)/((n+1)*(n+2)))+
    (67/100)*(harmonic n-2*(n : ℚ)/(n+1)-((n : ℚ)*(n-1)/((n+1)*(n+2)))))

theorem scalarBudget_eq_rational (n : ℕ) : scalarBudget n = (rationalScalarBudget n : ℝ) := by
  rw [scalarBudget_eq, tailBudget, first_coefficient, second_coefficient]
  simp only [rationalScalarBudget, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_one]
  ring

theorem scalarTail_lt_budget_of_interval {a b n : ℕ} (hn : 0 < n)
    (han : a ≤ n) (hnb : n ≤ b)
    (hrow : heatIntegral (2/(2*(b : ℝ)+1)) < scalarBudget a) :
    scalarTail n < scalarBudget n := by
  have hηn : (0 : ℝ) < 1/((n : ℝ)+1/2) := by positivity
  have hηb : (0 : ℝ) < 2/(2*(b : ℝ)+1) := by positivity
  have he : (2 : ℝ)/(2*(b : ℝ)+1) = 1/((b : ℝ)+1/2) := by field_simp <;> ring
  have hnb' : (n : ℝ) ≤ b := by exact_mod_cast hnb
  have hm : (2 : ℝ)/(2*(b : ℝ)+1) ≤ 1/((n : ℝ)+1/2) := by
    rw [he]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  exact ((scalarTail_le_heatIntegral hn).trans
    (heatIntegral_antitone hηb hηn hm)).trans_lt
      (hrow.trans_le (scalarBudget_monotone han))

#print axioms scalarTail_lt_budget_of_interval

theorem scalarTail_lt_budget_of_rational_row {a b n : ℕ} {U : ℚ}
    (hn : 0 < n) (han : a ≤ n) (hnb : n ≤ b)
    (hrow : heatIntegral (2/(2*(b : ℝ)+1)) < (U : ℝ))
    (hbudget : U < rationalScalarBudget a) : scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_interval hn han hnb
  apply hrow.trans
  rw [scalarBudget_eq_rational]
  exact_mod_cast hbudget

#print axioms scalarTail_lt_budget_of_rational_row
end BecknerOnofri.HighDim.EntropyTail
