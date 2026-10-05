module

public import Legacy.BecknerOnofri.JacobiCompleteness
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

@[expose] public section

/-! The zero Jacobi index is the Neumann cosine basis on the same Lebesgue interval. -/
noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped ContDiff Topology
namespace Legacy.BecknerOnofri.JacobiEigenfunctions

theorem eigenfunction_neumann (n : ℕ) (t : ℝ) :
    eigenfunction 0 n t = Real.cos ((n : ℝ) * t) := by
  simp only [eigenfunction, JacobiAngular.angular, polynomial, Function.iterate_zero,
    id_eq, Nat.add_zero, pow_zero, one_mul, Chebyshev.T_real_cos, Int.cast_natCast]

theorem eigenfunction_neumann_deriv (n : ℕ) (t : ℝ) :
    deriv (eigenfunction 0 n) t = -(n : ℝ) * Real.sin ((n : ℝ)*t) := by
  have h := (Real.hasDerivAt_cos ((n : ℝ)*t)).comp t
    ((hasDerivAt_id t).const_mul (n : ℝ))
  convert h.deriv using 1
  · congr 1
    funext x
    exact eigenfunction_neumann n x
  · ring

@[simp] theorem eigenfunction_neumann_deriv_zero (n : ℕ) :
    deriv (eigenfunction 0 n) 0 = 0 := by simp [eigenfunction_neumann_deriv]

@[simp] theorem eigenfunction_neumann_deriv_pi (n : ℕ) :
    deriv (eigenfunction 0 n) Real.pi = 0 := by
  simp [eigenfunction_neumann_deriv, Real.sin_nat_mul_pi]

theorem integration_by_parts_all (m n l : ℕ) :
    (∫ t in 0..Real.pi, eigenfunction m n t * deriv (deriv (eigenfunction m l)) t) =
      -(∫ t in 0..Real.pi, deriv (eigenfunction m n) t * deriv (eigenfunction m l) t) := by
  by_cases hm : m = 0
  · subst m
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := Real.pi)
      (fun t _ => ((eigenfunction_contDiff 0 n).differentiable (by simp) t).hasDerivAt)
      (fun t _ => ((eigenfunction_deriv_contDiff 0 l).differentiable (by simp) t).hasDerivAt)
      ((eigenfunction_deriv_contDiff 0 n).continuous.intervalIntegrable _ _)
      ((eigenfunction_second_continuous 0 l).intervalIntegrable _ _)
    simpa only [eigenfunction_neumann_deriv_zero, eigenfunction_neumann_deriv_pi,
      mul_zero, sub_self, zero_sub] using h
  · exact integration_by_parts (Nat.pos_of_ne_zero hm) n l

theorem integral_orthogonal_all (m : ℕ) {n l : ℕ} (hne : n ≠ l) :
    (∫ t in Ioo 0 Real.pi, eigenfunction m n t * eigenfunction m l t) = 0 := by
  have hw : ∀ t ∈ Ioo 0 Real.pi,
      (eigenvalue m n - eigenvalue m l) * (eigenfunction m n t * eigenfunction m l t) =
        eigenfunction m n t * deriv (deriv (eigenfunction m l)) t -
          eigenfunction m l t * deriv (deriv (eigenfunction m n)) t := by
    intro t ht
    have hn := eigenfunction_equation m n ht
    have hl := eigenfunction_equation m l ht
    dsimp [JacobiAngular.angularOperator] at hn hl
    linear_combination (eigenfunction m n t) * hl - (eigenfunction m l t) * hn
  have hInt := setIntegral_congr_fun (μ := volume) measurableSet_Ioo hw
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le,
    ← intervalIntegral.integral_of_le Real.pi_pos.le] at hInt
  have hni := ((eigenfunction_contDiff m n).continuous.mul
    (eigenfunction_second_continuous m l)).intervalIntegrable (μ := volume) (0 : ℝ) Real.pi
  have hli := ((eigenfunction_contDiff m l).continuous.mul
    (eigenfunction_second_continuous m n)).intervalIntegrable (μ := volume) (0 : ℝ) Real.pi
  have hsub := intervalIntegral.integral_sub hni hli
  simp only [Pi.mul_apply] at hsub
  rw [intervalIntegral.integral_const_mul, hsub,
    integration_by_parts_all m n l, integration_by_parts_all m l n] at hInt
  have hs : (∫ t in 0..Real.pi, deriv (eigenfunction m l) t * deriv (eigenfunction m n) t) =
      ∫ t in 0..Real.pi, deriv (eigenfunction m n) t * deriv (eigenfunction m l) t := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hs, sub_self] at hInt
  have hv : eigenvalue m n - eigenvalue m l ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne (eigenvalue_injective m h))
  have hz := (mul_eq_zero.mp hInt).resolve_left hv
  simpa only [intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo] using hz

theorem normalizedVector_orthonormal_all (m : ℕ) : Orthonormal ℝ (normalizedVector m) := by
  rw [orthonormal_iff_ite]
  intro n l
  split_ifs with h
  · subst l
    exact normalizedVector_inner_self m n
  · rw [normalizedVector, normalizedVector, inner_smul_left, inner_smul_right,
      eigenvector_inner, integral_orthogonal_all m h, mul_zero, mul_zero]

/-- Dirichlet Jacobi for positive indices and Neumann cosines at index zero,
on one and the same Lebesgue Hilbert space. -/
def fullHilbertBasis (m : ℕ) : HilbertBasis ℕ ℝ JacobiL2 :=
  HilbertBasis.mkOfOrthogonalEqBot (normalizedVector_orthonormal_all m)
    (normalizedVector_orthogonalComplement m)

@[simp] theorem fullHilbertBasis_apply (m n : ℕ) :
    fullHilbertBasis m n = normalizedVector m n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

@[simp] theorem normalizedFunction_neumann_deriv_zero (n : ℕ) :
    deriv (normalizedFunction 0 n) 0 = 0 := by
  change deriv (fun x => (Real.sqrt (normSquared 0 n))⁻¹ * eigenfunction 0 n x) _ = 0
  rw [deriv_const_mul _
    ((eigenfunction_contDiff 0 n).differentiable (by simp) 0),
    eigenfunction_neumann_deriv_zero, mul_zero]

@[simp] theorem normalizedFunction_neumann_deriv_pi (n : ℕ) :
    deriv (normalizedFunction 0 n) Real.pi = 0 := by
  change deriv (fun x => (Real.sqrt (normSquared 0 n))⁻¹ * eigenfunction 0 n x) _ = 0
  rw [deriv_const_mul _
    ((eigenfunction_contDiff 0 n).differentiable (by simp) Real.pi),
    eigenfunction_neumann_deriv_pi, mul_zero]

theorem eigenfunction_dirichlet (n : ℕ) (t : ℝ) :
    eigenfunction 1 n t = ((n+1 : ℕ) : ℝ) * Real.sin (((n+1 : ℕ) : ℝ)*t) := by
  simp only [eigenfunction, JacobiAngular.angular, polynomial, Function.iterate_one,
    pow_one, Chebyshev.T_derivative_eq_U, eval_mul, eval_natCast, Int.cast_natCast]
  have h := Chebyshev.U_real_cos (θ := t) (n := (n : ℤ))
  simp only [Int.cast_natCast] at h
  convert congrArg (fun x : ℝ => ((n+1 : ℕ) : ℝ) * x) h using 1 <;>
    push_cast <;> ring_nf

#print axioms fullHilbertBasis
end Legacy.BecknerOnofri.JacobiEigenfunctions
