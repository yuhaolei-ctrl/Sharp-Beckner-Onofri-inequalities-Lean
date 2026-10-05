module

public import BecknerOnofri.EntropyTailPolynomialExpansion

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Polynomial
namespace BecknerOnofri.HighDim.CubeShell
open Finset Polynomial

def evaluateShell (F : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun j => F j • LinearMap.id)

theorem evaluateShell_monomial (F : ℕ → ℝ) (j : ℕ) (a : ℝ) :
    evaluateShell F (Polynomial.monomial j a) = a*F j := by
  simp [evaluateShell, Polynomial.lsum, mul_comm]

theorem prod_monomial {ι : Type*} (s : Finset ι) (m : ι → ℕ) :
    (∏ i ∈ s, Polynomial.monomial (m i) (1 : ℝ)) =
      Polynomial.monomial (∑ i ∈ s, m i) (1 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Polynomial.monomial_mul_monomial]

theorem cube_generating_polynomial (d : ℕ) :
    (1+Polynomial.monomial 1 (2 : ℝ))^d =
      ∑ k ∈ RectangleLattice.box (fun _ : Fin d => 1), Polynomial.monomial (latticeSquare k) (1 : ℝ) := by
  have hbase : (∑ j ∈ Icc (-1 : ℤ) 1, Polynomial.monomial (j.natAbs^2) (1 : ℝ)) =
      1+Polynomial.monomial 1 (2 : ℝ) := by
    have he : Icc (-1 : ℤ) 1 = {-1,0,1} := by decide +kernel
    rw [he]
    norm_num [Finset.sum_insert, ← map_add]
    ext j
    by_cases h0 : j=0 <;> by_cases h1 : j=1 <;>
      simp [Polynomial.coeff_monomial, h0, h1, eq_comm] <;> norm_num <;> ring
  rw [← hbase, Finset.sum_pow']
  unfold RectangleLattice.box
  apply sum_congr rfl
  intro k _
  exact prod_monomial univ _

theorem binomial_polynomial (d : ℕ) :
    (1+Polynomial.monomial 1 (2 : ℝ))^d =
      ∑ r ∈ range (d+1), Polynomial.monomial r ((d.choose r : ℝ)*2^r) := by
  rw [add_comm, add_pow]
  apply sum_congr rfl
  intro r _
  rw [one_pow, mul_one, Polynomial.monomial_pow, one_mul, ← Polynomial.C_eq_natCast,
    Polynomial.monomial_mul_C]
  congr 1
  ring

/-- Every radial function on the frequency cube has exactly the binomial
shell multiplicities used in the manuscript's spin energy. -/
theorem cube_sum (d : ℕ) (F : ℕ → ℝ) :
    (∑ k ∈ RectangleLattice.box (fun _ : Fin d => 1), F (latticeSquare k)) =
      ∑ r ∈ range (d+1), (d.choose r : ℝ)*2^r*F r := by
  have h := congrArg (evaluateShell F) ((cube_generating_polynomial d).symm.trans (binomial_polynomial d))
  simpa only [map_sum, evaluateShell_monomial, one_mul] using h

#print axioms cube_sum
end BecknerOnofri.HighDim.CubeShell
