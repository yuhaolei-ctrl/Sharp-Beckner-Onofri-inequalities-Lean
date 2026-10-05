import Legacy.BecknerOnofri.ThetaConstants
import Legacy.BecknerOnofri.LaplaceReciprocal
import Mathlib.Data.Rat.Cast.Order

/-! The 24 retained shell terms now contain actual Laplace integrals.
The remaining obligation is to bound the full theta integral by this
finite expression, including the interpretation of its tail. -/
open MeasureTheory Set
namespace Legacy.BecknerOnofri.ThetaCertificate
attribute [local irreducible] counts

noncomputable def realTerm (q : ℕ) : ℝ :=
  let A := (a : ℝ) * q
  ((counts 10)[q]! : ℝ) * (r : ℝ)^q *
    (1/A+4/A^2+12/A^3+24/A^4+24/A^5+
      ∫ v : ℝ in Ioi 0, Real.exp (-v)/(A+v))

 theorem realTerm_le_term {q : ℕ} (hq : 0 < q) : realTerm q ≤ (term q : ℝ) := by
  have hA : 0 < (a : ℝ) * (q : ℝ) := mul_pos a_pos (by exact_mod_cast hq)
  have h := LaplaceReciprocal.integral_upper hA
  dsimp only [realTerm, term, laplaceUpper]
  push_cast
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl h)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg r_pos.le _))

noncomputable def realFiniteUpper : ℝ :=
  (∑ i : Fin 24, realTerm (i.val+1)) + (tail : ℝ)

 theorem realFiniteUpper_le_certificate : realFiniteUpper ≤ (upper : ℝ) := by
  unfold realFiniteUpper upper
  push_cast
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro i hi
  exact realTerm_le_term (Nat.zero_lt_succ i.val)

 theorem realFiniteUpper_lt : realFiniteUpper < (41/25 : ℝ) := by
  have h := (Rat.cast_lt (K := ℝ)).mpr rational_upper_lt
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact realFiniteUpper_le_certificate.trans_lt h

#print axioms realFiniteUpper_lt
end Legacy.BecknerOnofri.ThetaCertificate
