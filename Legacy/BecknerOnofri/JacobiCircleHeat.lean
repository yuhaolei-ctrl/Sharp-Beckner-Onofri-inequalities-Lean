module

public import Legacy.BecknerOnofri.JacobiHeatEquation
public import Legacy.BecknerOnofri.CircleBoundaryHeat
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Exact identification of the normalized Jacobi heat kernels at indices zero
and one with the actual reflected Neumann and Dirichlet circle heat kernels. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Legacy.BecknerOnofri.JacobiHeatBounds
open JacobiEigenfunctions

theorem integral_sine_square_frequency {N : ℕ} (hN : 0 < N) :
    (∫ x in (0:ℝ)..Real.pi, Real.sin ((N:ℝ)*x)^2) = Real.pi/2 := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x^2) hn,integral_sin_sq]
  simp only [mul_zero,Real.sin_zero,zero_mul,Real.sin_nat_mul_pi,mul_zero,sub_zero,zero_add,smul_eq_mul]
  field_simp

theorem integral_cosine_square_frequency {N : ℕ} (hN : 0 < N) :
    (∫ x in (0:ℝ)..Real.pi, Real.cos ((N:ℝ)*x)^2) = Real.pi/2 := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x^2) hn,integral_cos_sq]
  simp only [mul_zero,Real.sin_zero,Real.sin_nat_mul_pi,mul_zero,sub_zero,zero_add,smul_eq_mul]
  field_simp

theorem normSquared_dirichlet (n : ℕ) :
    normSquared 1 n = ((n+1:ℕ):ℝ)^2 * (Real.pi/2) := by
  unfold normSquared
  simp_rw [eigenfunction_dirichlet,mul_pow]
  rw [integral_const_mul,← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le,integral_sine_square_frequency (Nat.succ_pos n)]

theorem normSquared_neumann_zero : normSquared 0 0 = Real.pi := by
  unfold normSquared
  simp_rw [eigenfunction_neumann]
  simp [Real.pi_pos.le]

theorem normSquared_neumann_succ (n : ℕ) : normSquared 0 (n+1) = Real.pi/2 := by
  unfold normSquared
  simp_rw [eigenfunction_neumann]
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_cosine_square_frequency (Nat.succ_pos n)]

theorem normalizedFunction_product (m n : ℕ) (x y : ℝ) :
    normalizedFunction m n x * normalizedFunction m n y =
      (normSquared m n)⁻¹ * (eigenfunction m n x * eigenfunction m n y) := by
  unfold normalizedFunction
  rw [show (Real.sqrt (normSquared m n))⁻¹ * eigenfunction m n x *
      ((Real.sqrt (normSquared m n))⁻¹ * eigenfunction m n y) =
      ((Real.sqrt (normSquared m n))^2)⁻¹ * (eigenfunction m n x*eigenfunction m n y) by
    rw [← inv_pow]; ring,Real.sq_sqrt (normSquared_pos m n).le]

theorem normalizedFunction_dirichlet_product (n : ℕ) (x y : ℝ) :
    normalizedFunction 1 n x * normalizedFunction 1 n y =
      (2/Real.pi)*Real.sin (((n+1:ℕ):ℝ)*x)*Real.sin (((n+1:ℕ):ℝ)*y) := by
  rw [normalizedFunction_product,normSquared_dirichlet,eigenfunction_dirichlet,eigenfunction_dirichlet]
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  field_simp

theorem normalizedFunction_neumann_zero_product (x y : ℝ) :
    normalizedFunction 0 0 x * normalizedFunction 0 0 y = 1/Real.pi := by
  rw [normalizedFunction_product,normSquared_neumann_zero]
  simp [eigenfunction_neumann]

theorem normalizedFunction_neumann_succ_product (n : ℕ) (x y : ℝ) :
    normalizedFunction 0 (n+1) x * normalizedFunction 0 (n+1) y =
      (2/Real.pi)*Real.cos (((n+1:ℕ):ℝ)*x)*Real.cos (((n+1:ℕ):ℝ)*y) := by
  rw [normalizedFunction_product,normSquared_neumann_succ]
  simp only [eigenfunction_neumann]
  field_simp

theorem heatKernel_one_eq_dirichlet {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    heatKernel 1 t x y = CircleHeat.dirichletPiHeat t x y := by
  rw [heatKernel,CircleHeat.dirichletPiHeat_eq_sine_series ht,← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [mul_assoc,normalizedFunction_dirichlet_product]
  simp only [eigenvalue,Nat.cast_add,Nat.cast_one]
  ring

theorem heatKernel_zero_eq_neumann {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    heatKernel 0 t x y = CircleHeat.neumannPiHeat t x y := by
  rw [heatKernel,(heatKernel_summable 0 ht x y).tsum_eq_zero_add,
    CircleHeat.neumannPiHeat_eq_cosine_series ht,← tsum_mul_left]
  have hz : Real.exp (-t*eigenvalue 0 0)*normalizedFunction 0 0 x*normalizedFunction 0 0 y = 1/Real.pi := by
    rw [mul_assoc,normalizedFunction_neumann_zero_product]
    simp [eigenvalue]
  rw [hz]
  congr 1
  apply tsum_congr
  intro n
  rw [mul_assoc,normalizedFunction_neumann_succ_product]
  simp only [eigenvalue,Nat.add_zero,Nat.cast_add,Nat.cast_one]
  ring

theorem heatKernel_one_pos {t x y : ℝ} (ht : 0 < t) (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    0 < heatKernel 1 t x y := by
  rw [heatKernel_one_eq_dirichlet ht]
  exact CircleHeat.dirichletPiHeat_pos ht hx hy

theorem heatKernel_zero_pos {t : ℝ} (ht : 0 < t) (x y : ℝ) : 0 < heatKernel 0 t x y := by
  rw [heatKernel_zero_eq_neumann ht]
  exact CircleHeat.neumannPiHeat_pos ht x y

theorem heatKernel_one_lt_zero {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    heatKernel 1 t x y < heatKernel 0 t x y := by
  rw [heatKernel_one_eq_dirichlet ht,heatKernel_zero_eq_neumann ht]
  exact CircleHeat.dirichletPiHeat_lt_neumann ht x y

#print axioms heatKernel_one_eq_dirichlet
#print axioms heatKernel_zero_eq_neumann
#print axioms heatKernel_one_lt_zero
end Legacy.BecknerOnofri.JacobiHeatBounds
