import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic

/-! The formal polynomial part of the Jacobi intertwining argument.
These are differential identities; Friedrichs domains and fractional powers
of the corresponding unbounded operators are separate analytic obligations. -/

noncomputable section
open Polynomial

namespace Legacy.BecknerOnofri.JacobiPolynomial

def jacobi (m : ℕ) (p : ℝ[X]) : ℝ[X] :=
  -(1 - X^2) * derivative (derivative p) + (2 * (m : ℝ[X]) + 1) * X * derivative p

def shifted (m : ℕ) (p : ℝ[X]) : ℝ[X] := jacobi m p + (m : ℝ[X])^2 * p

theorem derivative_shifted (m : ℕ) (p : ℝ[X]) :
    derivative (shifted m p) = shifted (m+1) (derivative p) := by
  simp [shifted, jacobi, derivative_mul, derivative_pow]
  rw [show C (2 : ℝ) = (2 : ℝ[X]) from map_ofNat C 2]
  ring


theorem iterate_derivative_jacobi (m : ℕ) (p : ℝ[X]) :
    derivative^[m] (jacobi 0 p) = shifted m (derivative^[m] p) := by
  induction m with
  | zero => simp [shifted]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, derivative_shifted, Function.iterate_succ_apply']

theorem jacobi_chebyshev (n : ℤ) :
    jacobi 0 (Polynomial.Chebyshev.T ℝ n) =
      (n : ℝ[X])^2 * Polynomial.Chebyshev.T ℝ n := by
  have h := Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℝ) n
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at h
  simp only [jacobi, Nat.cast_zero, mul_zero, zero_add, one_mul]
  linear_combination -h

theorem shifted_chebyshev_derivative (n : ℤ) (m : ℕ) :
    shifted m (derivative^[m] (Polynomial.Chebyshev.T ℝ n)) =
      (n : ℝ[X])^2 * derivative^[m] (Polynomial.Chebyshev.T ℝ n) := by
  rw [← iterate_derivative_jacobi, jacobi_chebyshev]
  have hcast : (n : ℝ[X])^2 = C ((n : ℝ)^2) := by simp
  rw [hcast, iterate_derivative_C_mul]

#print axioms iterate_derivative_jacobi
#print axioms shifted_chebyshev_derivative
end Legacy.BecknerOnofri.JacobiPolynomial
