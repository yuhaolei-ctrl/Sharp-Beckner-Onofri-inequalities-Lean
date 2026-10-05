module

public import Legacy.BecknerOnofri.JacobiAngular
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

@[expose] public section

/-! Uniform bounds for the genuine derivatives of Chebyshev polynomials on the closed interval. -/
noncomputable section
open Polynomial
namespace Legacy.BecknerOnofri.ChebyshevDerivativeBound
open Polynomial.Chebyshev

theorem endpoint_nonneg (n m : ℕ) :
    0 ≤ (derivative^[m] (T ℝ (n:ℤ))).eval 1 :=
  (abs_nonneg _).trans (abs_iterate_derivative_T_real_le (n:ℤ) m (by norm_num : |(1:ℝ)| ≤ 1))

theorem endpoint_bound (n m : ℕ) :
    (derivative^[m] (T ℝ (n:ℤ))).eval 1 ≤ (n:ℝ)^(2*m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hr := iterate_derivative_T_eval_one_recurrence (R := ℝ) (n:ℤ) m
    simp only [Int.cast_natCast] at hr
    have hnext := endpoint_nonneg n (m+1)
    have hprev := endpoint_nonneg n m
    have hk := mul_nonneg (sq_nonneg (m:ℝ)) hprev
    have hm := mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) hnext
    have hstep : (derivative^[m+1] (T ℝ (n:ℤ))).eval 1 ≤
        (n:ℝ)^2 * (derivative^[m] (T ℝ (n:ℤ))).eval 1 := by
      nlinarith only [hr, hk, hm]
    calc
      _ ≤ (n:ℝ)^2 * (derivative^[m] (T ℝ (n:ℤ))).eval 1 := hstep
      _ ≤ (n:ℝ)^2 * (n:ℝ)^(2*m) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = _ := by rw [← pow_add]; congr 1; omega

/-- The closed-interval bound includes both endpoints and all derivative orders. -/
theorem polynomial_derivative_bound (n m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    |(derivative^[m] (T ℝ (n:ℤ))).eval x| ≤ (n:ℝ)^(2*m) :=
  (abs_iterate_derivative_T_real_le (n:ℤ) m (abs_le.mpr hx)).trans (endpoint_bound n m)

/-- Formal polynomial differentiation agrees at every order with actual real differentiation. -/
theorem iterate_deriv_eval (p : Polynomial ℝ) (m : ℕ) (x : ℝ) :
    (deriv^[m] (fun y => p.eval y)) x = (derivative^[m] p).eval x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have he : deriv^[m] (fun y => p.eval y) = fun y => (derivative^[m] p).eval y := by
      funext y
      exact ih y
    rw [he]
    exact (derivative^[m] p).deriv (x := x)

/-- A bound on the actual m-fold real derivative, not only on a formal polynomial. -/
theorem actual_derivative_bound (n m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    |(deriv^[m] (fun y => (T ℝ (n:ℤ)).eval y)) x| ≤ (n:ℝ)^(2*m) := by
  rw [iterate_deriv_eval]
  exact polynomial_derivative_bound n m hx

#print axioms endpoint_bound
#print axioms actual_derivative_bound
end Legacy.BecknerOnofri.ChebyshevDerivativeBound
