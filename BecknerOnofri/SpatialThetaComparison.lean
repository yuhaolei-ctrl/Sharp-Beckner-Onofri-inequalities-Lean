module

public import BecknerOnofri.SpatialThetaJacobiNormalization

@[expose] public section

/-! The actual spatial-theta diagonal comparison used by the dimension-twelve
radial certificate. All infinite products and Fourier identities are proved. -/
noncomputable section
open Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.SpatialThetaDiagonal
open RadialThetaTail

/-- The normalized spatial theta is exactly the convergent normalized Jacobi
product in the squared-sine coordinate. -/
theorem theta_normalized_product {t : ℝ} (ht : 0<t) (y : ℝ) :
    theta t y/theta t 0=SpatialThetaProduct.jacobiProduct t (Real.sin (Real.pi*y)^2) := by
  rw [SpatialThetaJacobi.theta_eq_zero_mul_product ht y]
  exact mul_div_cancel_left₀ _ (theta_pos ht 0).ne'

/-- Exact source diagonal comparison, for every positive time and every real
torus representative. The diagonal point preserves the sum of squared sines. -/
theorem theta_product_le_diagonal {d : ℕ} (hd : 0<d) {t : ℝ} (ht : 0<t)
    (x : Fin d → ℝ) :
    (∏ i,theta t (x i))≤radialTheta d t (sineSquareSum x) := by
  have hr (i : Fin d) : Real.sin (Real.pi*x i)^2∈Icc (0:ℝ) 1 := by
    refine ⟨sq_nonneg _,?_⟩
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*x i),sq_nonneg (Real.cos (Real.pi*x i))]
  have hprod := SpatialThetaProduct.product_diagonal hd ht
    (fun i => Real.sin (Real.pi*x i)^2) hr
  calc
    (∏ i,theta t (x i))=
        theta t 0^d*(∏ i,SpatialThetaProduct.jacobiProduct t (Real.sin (Real.pi*x i)^2)) := by
      rw [Finset.prod_congr rfl (fun i (_hi : i∈Finset.univ) =>
        SpatialThetaJacobi.theta_eq_zero_mul_product ht (x i)),Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ ≤ theta t 0^d*SpatialThetaProduct.jacobiProduct t (sineSquareSum x/(d:ℝ))^d :=
      mul_le_mul_of_nonneg_left hprod (pow_nonneg (theta_pos ht 0).le _)
    _ = radialTheta d t (sineSquareSum x) := by
      rw [radialTheta,SpatialThetaJacobi.theta_eq_zero_mul_product ht (radialAngle d (sineSquareSum x)),
        sineSquare_radialAngle hd (sineSquareSum_mem x),mul_pow]

#print axioms theta_normalized_product
#print axioms theta_product_le_diagonal
end BecknerOnofri.HighDim.SpatialThetaDiagonal
