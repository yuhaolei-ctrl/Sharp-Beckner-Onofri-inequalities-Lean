module

public import BecknerOnofri.EntropyTailPolynomial

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Polynomial BigOperators
open Finset Polynomial
namespace BecknerOnofri.HighDim.EntropyTail

theorem binomialPolynomial_expansion (A : ℚ) (d : ℕ) :
    (1 + Polynomial.monomial 1 A)^d =
      ∑ a ∈ range (d+1), Polynomial.monomial a ((d.choose a : ℚ)*A^a) := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro a _
  rw [one_pow, mul_one, Polynomial.monomial_pow, one_mul, ← Polynomial.C_eq_natCast,
    Polynomial.monomial_mul_C]
  congr 1
  ring

theorem trinomialPolynomial_expansion (A B : ℚ) (d : ℕ) :
    (1 + Polynomial.monomial 1 A + Polynomial.monomial 4 B)^d =
      ∑ b ∈ range (d+1), ∑ a ∈ range (d-b+1),
        Polynomial.monomial (4*b+a) ((d.choose b : ℚ)*((d-b).choose a : ℚ)*B^b*A^a) := by
  rw [add_comm (1 + Polynomial.monomial 1 A), add_pow]
  apply Finset.sum_congr rfl
  intro b _
  rw [binomialPolynomial_expansion, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Polynomial.monomial_pow, Polynomial.monomial_mul_monomial,
    ← Polynomial.C_eq_natCast, Polynomial.monomial_mul_C]
  congr 1
  ring

theorem inverseSixth_difference_eq_shell :
    inverseSixth (radialPolynomial 2 12) - inverseSixth (radialPolynomial 1 12) = indexTwoShellSum := by
  let F : ℕ → ℚ := fun b => ∑ a ∈ range (13-b),
    (Nat.choose 12 b : ℚ) * (Nat.choose (12-b) a : ℚ) * (1/3)^b * (4/3)^a /
      ((4*b+a : ℕ) : ℚ)^6
  have hP : inverseSixth (radialPolynomial 2 12) = ∑ b ∈ range 13, F b := by
    rw [radialPolynomial_two, trinomialPolynomial_expansion]
    simp only [map_sum, inverseSixth_monomial]
    apply Finset.sum_congr rfl
    intro b hb
    have hr : 12-b+1=13-b := by have h := Finset.mem_range.mp hb; omega
    rw [hr]
  have hQ : inverseSixth (radialPolynomial 1 12) = F 0 := by
    rw [radialPolynomial_one, binomialPolynomial_expansion]
    simp only [map_sum, inverseSixth_monomial]
    simp [F]
  rw [hP,hQ]
  symm
  unfold indexTwoShellSum
  calc
    _ = ∑ b ∈ range 13, (F b - if b = 0 then F 0 else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b = 0
      · subst b; simp
      · simp only [hb, ↓reduceIte, sub_zero, F]
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

#print axioms inverseSixth_difference_eq_shell
end BecknerOnofri.HighDim.EntropyTail
