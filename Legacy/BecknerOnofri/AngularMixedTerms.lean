import Legacy.BecknerOnofri.ChebyshevMixedSeries
import Legacy.BecknerOnofri.JacobiTensorBasis

/-! The genuine angular conjugates of differentiated Fourier-Chebyshev
terms are scalar multiples of the concrete normalized tensor eigenfunctions.
Frequencies killed by differentiation are proved to contribute zero. -/
noncomputable section
namespace Legacy.BecknerOnofri.AngularMixedTerms
open Set Polynomial Legacy.TorusEndpoint TorusSobolev RadialWiener ChebyshevMixedSeries
open TensorPolynomialDerivatives JacobiEigenfunctions
open scoped BigOperators ContDiff

def countIndex {d : ℕ} (is : List (Fin d)) : Fin d → ℕ := fun i => is.count i

def angularCube {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ := fun i => (1+Real.cos (x i))/2

def weight {d : ℕ} (is : List (Fin d)) (x : Fin d → ℝ) : ℝ :=
  ∏ i, Real.sin (x i)^(is.count i)

def angularTerm {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) (x : Fin d → ℝ) : ℝ := weight is x * term a is k (angularCube x)

def shiftedIndex {d : ℕ} (is : List (Fin d)) (k : Frequency d) : Fin d → ℕ :=
  fun i => (k i).natAbs-is.count i

def normalization {d : ℕ} (is : List (Fin d)) (n : Fin d → ℕ) : ℝ :=
  2^is.length * ∏ i, Real.sqrt (normSquared (is.count i) (n i))

theorem angularCube_mem {d : ℕ} (x : Fin d → ℝ) :
    angularCube x ∈ FiniteDifferences.closedCube d := by
  constructor <;> intro i <;> dsimp [angularCube]
  · linarith [Real.neg_one_le_cos (x i)]
  · linarith [Real.cos_le_one (x i)]

theorem angularCube_coordinate {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    2*angularCube x i-1 = Real.cos (x i) := by dsimp [angularCube]; ring

theorem weight_norm_le {d : ℕ} (is : List (Fin d)) (x : Fin d → ℝ) : ‖weight is x‖ ≤ 1 := by
  rw [weight, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (x i))

theorem angularTerm_bound {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) (x : Fin d → ℝ) : ‖angularTerm a is k x‖ ≤ majorant a is k := by
  rw [angularTerm, norm_mul]
  exact (mul_le_mul_of_nonneg_right (weight_norm_le is x) (norm_nonneg _)).trans
    (by simpa using term_bound a is k (angularCube_mem x))

theorem angularTerm_contDiff {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) : ContDiff ℝ ∞ (angularTerm a is k) := by
  apply ContDiff.mul
  · apply contDiff_prod
    intro i _
    exact (Real.contDiff_sin.comp (contDiff_apply ℝ ℝ i)).pow _
  · apply (term_contDiff a is k).comp
    apply contDiff_pi.mpr
    intro i
    exact (contDiff_const.add (Real.contDiff_cos.comp (contDiff_apply ℝ ℝ i))).div_const 2

theorem derivative_polynomial_zero {d : ℕ} (is : List (Fin d)) (k : Frequency d)
    (i : Fin d) (hi : (k i).natAbs < is.count i) :
    iteratePolynomials (polynomials k) is i = 0 := by
  apply Polynomial.iterate_derivative_eq_zero
  simpa only [polynomials, Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast] using hi

theorem term_eq_zero_of_frequency_lt {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) (i : Fin d) (hi : (k i).natAbs < is.count i) (y : FiniteDifferences.Space d) :
    term a is k y = 0 := by
  have hp : unitTensor (iteratePolynomials (polynomials k) is) y = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [derivative_polynomial_zero is k i hi]
    simp
  simp [term, hp]

theorem angularTerm_eq_zero_of_frequency_lt {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) (i : Fin d) (hi : (k i).natAbs < is.count i) (x : Fin d → ℝ) :
    angularTerm a is k x = 0 := by
  rw [angularTerm, term_eq_zero_of_frequency_lt a is k i hi, mul_zero]

theorem eigenfunction_eq_normalized (m n : ℕ) (t : ℝ) :
    eigenfunction m n t = Real.sqrt (normSquared m n) * normalizedFunction m n t := by
  rw [normalizedFunction, ← mul_assoc, mul_inv_cancel₀
    (Real.sqrt_pos.mpr (normSquared_pos m n)).ne', one_mul]

theorem angularTerm_eq_tensor {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) (hk : ∀ i, is.count i ≤ (k i).natAbs) (x : Fin d → ℝ) :
    angularTerm a is k x = (a k).re * normalization is (shiftedIndex is k) *
      JacobiTensor.tensorFunction (countIndex is) (shiftedIndex is k) x := by
  have hi (i : Fin d) : Real.sin (x i)^(is.count i) *
      (iteratePolynomials (polynomials k) is i).eval (2*angularCube x i-1) =
        eigenfunction (is.count i) (shiftedIndex is k i) (x i) := by
    rw [angularCube_coordinate]
    dsimp [eigenfunction, JacobiAngular.angular, polynomial, shiftedIndex, iteratePolynomials, polynomials]
    rw [← Nat.cast_add, Nat.sub_add_cancel (hk i)]
  calc
    _ = (a k).re * 2^is.length * ∏ i, Real.sin (x i)^(is.count i) *
        (iteratePolynomials (polynomials k) is i).eval (2*angularCube x i-1) := by
      rw [Finset.prod_mul_distrib]
      dsimp [angularTerm, weight, term, unitTensor]
      ring
    _ = (a k).re * 2^is.length * ∏ i, eigenfunction (is.count i) (shiftedIndex is k i) (x i) := by
      simp only [hi]
    _ = _ := by
      simp only [eigenfunction_eq_normalized, Finset.prod_mul_distrib]
      dsimp [normalization, JacobiTensor.tensorFunction, countIndex]
      ring

theorem angular_mixedPartial_series {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d)) (x : Fin d → ℝ) :
    weight is x * FiniteDifferences.mixedPartial is
      (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) (angularCube x) =
        ∑' k, angularTerm a is k x := by
  rw [mixedPartial_profile a ha is (angularCube_mem x)]
  exact (tsum_mul_left : (∑' k, weight is x * term a is k (angularCube x)) =
    weight is x * ∑' k, term a is k (angularCube x)).symm

#print axioms angularTerm_eq_tensor
#print axioms angular_mixedPartial_series
end Legacy.BecknerOnofri.AngularMixedTerms
