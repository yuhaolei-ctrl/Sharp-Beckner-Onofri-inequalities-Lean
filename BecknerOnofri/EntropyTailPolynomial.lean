import BecknerOnofri.EntropyTailScalarBasic
import BecknerOnofri.ComplementGap
import Mathlib.Algebra.Polynomial.Coeff

/-! A polynomial encoding of the actual finite lattice sum for n=2. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Polynomial
open Finset
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.D10

def radialPolynomial (r d : ℕ) : ℚ[X] :=
  (∑ j ∈ Finset.Icc (-(r : ℤ)) (r : ℤ),
    Polynomial.monomial (j.natAbs^2) (binomialCoeff 2 j.natAbs))^d

def inverseSixth : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun j => ((j : ℚ)^6)⁻¹ • LinearMap.id)

theorem inverseSixth_monomial (j : ℕ) (a : ℚ) :
    inverseSixth (Polynomial.monomial j a) = a / (j : ℚ)^6 := by
  simp [inverseSixth, Polynomial.lsum, div_eq_mul_inv, mul_comm]

theorem prod_monomial {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → ℚ) :
    (∏ i ∈ s, Polynomial.monomial (m i) (a i)) =
      Polynomial.monomial (∑ i ∈ s, m i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Polynomial.monomial_mul_monomial]

theorem radialPolynomial_eq_sum (r d : ℕ) : radialPolynomial r d =
    ∑ k ∈ RectangleLattice.box (fun _ : Fin d => r),
      Polynomial.monomial (latticeSquare k) (∏ i : Fin d, binomialCoeff 2 (k i).natAbs) := by
  unfold radialPolynomial RectangleLattice.box
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro k _
  exact prod_monomial Finset.univ _ _

theorem inverseSixth_radialPolynomial (r d : ℕ) : inverseSixth (radialPolynomial r d) =
    ∑ k ∈ RectangleLattice.box (fun _ : Fin d => r),
      (∏ i : Fin d, binomialCoeff 2 (k i).natAbs) / (latticeSquare k : ℚ)^6 := by
  rw [radialPolynomial_eq_sum, map_sum]
  simp only [inverseSixth_monomial]

theorem radialPolynomial_one (d : ℕ) : radialPolynomial 1 d =
    (1 + Polynomial.monomial 1 (4/3 : ℚ))^d := by
  unfold radialPolynomial
  have hs : Finset.Icc (-1 : ℤ) 1 = {-1,0,1} := by decide +kernel
  norm_num only [Nat.cast_ofNat]
  rw [hs]
  norm_num [Finset.sum_insert, binomialCoeff, Nat.choose, ← map_add]
  congr 1
  ext j
  by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;>
    simp [Polynomial.coeff_monomial, h0, h1, eq_comm] <;> norm_num <;> ring

theorem radialPolynomial_two (d : ℕ) : radialPolynomial 2 d =
    (1 + Polynomial.monomial 1 (4/3 : ℚ) + Polynomial.monomial 4 (1/3 : ℚ))^d := by
  unfold radialPolynomial
  have hs : Finset.Icc (-2 : ℤ) 2 = {-2,-1,0,1,2} := by decide +kernel
  norm_num only [Nat.cast_ofNat]
  rw [hs]
  norm_num [Finset.sum_insert, binomialCoeff, Nat.choose, ← map_add]
  congr 1
  ext j
  by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> by_cases h4 : j = 4 <;>
    simp [Polynomial.coeff_monomial, h0, h1, h4, eq_comm] <;> norm_num <;> ring

theorem coefficient_weight_cast (k : Frequency 12) :
    (frequencyLength k^12)⁻¹ * (∏ i : Fin 12, scalarCoefficient 2 (k i).natAbs) =
      (((∏ i : Fin 12, binomialCoeff 2 (k i).natAbs) / (latticeSquare k : ℚ)^6 : ℚ) : ℝ) := by
  have hp : frequencyLength k^12 = (latticeSquare k : ℝ)^6 := by
    have h := frequencyLength_pow_eq k
    norm_num only [Nat.cast_ofNat, show (12 : ℝ)/2 = 6 by norm_num, Real.rpow_ofNat] at h
    exact h
  rw [hp]
  simp only [scalarCoefficient_eq, binomialCoeffReal, Rat.cast_div, Rat.cast_mul, Rat.cast_inv, Rat.cast_prod,
    Rat.cast_pow, Rat.cast_natCast, div_eq_mul_inv, mul_comm]

#print axioms inverseSixth_radialPolynomial
end BecknerOnofri.HighDim.EntropyTail
