module

public import BecknerOnofri.EntropyHeatWeighted

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

def sixthMomentBound (j : ℕ) : ℝ :=
  if j = 0 then (3/2)^6*(10/27)^6
  else if j = 1 then (6/5)^6*(10/27)^6
  else (10/27)^(4+j)

theorem exp_neg_nat_rational (m : ℕ) : Real.exp (-(m : ℝ)) ≤ (10/27 : ℝ)^m := by
  have h := exp_neg_integer_upper m (s := 1) le_rfl
  rw [mul_one] at h
  exact h.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) m)

theorem sixth_moment_bound (j : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    s^6*Real.exp (-(4+(j : ℝ))*s) ≤ sixthMomentBound j := by
  by_cases hj0 : j = 0
  · subst j
    have h := sixth_exp_global (c := 4) (s := s) (by norm_num) (by linarith)
    have he := exp_neg_nat_rational 6
    norm_num [sixthMomentBound] at h he ⊢
    nlinarith
  · by_cases hj1 : j = 1
    · subst j
      have h := sixth_exp_global (c := 5) (s := s) (by norm_num) (by linarith)
      have he := exp_neg_nat_rational 6
      norm_num [sixthMomentBound] at h he ⊢
      nlinarith
    · have hj : (2 : ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
      apply (sixth_exp_after_one (show 6 ≤ 4+(j : ℝ) by linarith) hs).trans
      simpa only [sixthMomentBound, if_neg hj0, if_neg hj1, Nat.cast_add, Nat.cast_ofNat]
        using exp_neg_nat_rational (4+j)

theorem heat_majorant_expansion (s : ℝ) :
    s^6*(12*(1007/500)*Real.exp (-4*s)*(1+(2101/1000)*Real.exp (-s))^11) =
    12*(1007/500)* ∑ j ∈ Finset.range 12,
      (Nat.choose 11 j : ℝ)*(2101/1000)^j*(s^6*Real.exp (-(4+(j : ℝ))*s)) := by
  rw [add_comm (1 : ℝ) ((2101/1000)*Real.exp (-s)), add_pow]
  simp only [one_pow, one_mul, mul_one, mul_pow, ← Real.exp_nat_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = 12*(1007/500)*(Nat.choose 11 j : ℝ)*(2101/1000)^j*s^6*
        (Real.exp (-4*s)*Real.exp ((j : ℝ)*(-s))) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      have he : -4*s+(j : ℝ)*(-s) = -(4+(j : ℝ))*s := by ring
      rw [he]
      ring

theorem heatComplement_weighted_large {s : ℝ} (hs : 1 ≤ s) :
    s^6*heatComplement s < 300 := by
  have h := mul_le_mul_of_nonneg_left (heatComplement_large_upper hs) (pow_nonneg (by linarith : 0 ≤ s) 6)
  rw [heat_majorant_expansion] at h
  have hsum : (∑ j ∈ Finset.range 12,
      (Nat.choose 11 j : ℝ)*(2101/1000)^j*(s^6*Real.exp (-(4+(j : ℝ))*s))) ≤
      ∑ j ∈ Finset.range 12, (Nat.choose 11 j : ℝ)*(2101/1000)^j*sixthMomentBound j := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (sixth_moment_bound j hs) (by positivity)
  have hnum : (12 : ℝ)*(1007/500)*(∑ j ∈ Finset.range 12,
      (Nat.choose 11 j : ℝ)*(2101/1000)^j*sixthMomentBound j) < 300 := by
    norm_num [Finset.sum_range_succ, sixthMomentBound, Nat.choose]
  exact (h.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))).trans_lt hnum

#print axioms heatComplement_weighted_large
end BecknerOnofri.HighDim.EntropyTail
