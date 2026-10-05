import Legacy.BecknerOnofri.TensorPolynomialDerivatives
import Legacy.BecknerOnofri.ClosedIntervalDerivativeSeries

/-! Every genuine mixed derivative of the actual cosine profile equals its
full differentiated Fourier-Chebyshev series, also at the boundary. -/
noncomputable section
namespace Legacy.BecknerOnofri.ChebyshevMixedSeries
open Set Legacy.TorusEndpoint TorusSobolev RadialWiener FiniteDifferences TensorPolynomialDerivatives
open scoped ContDiff BigOperators

def polynomials {d : ℕ} (k : Frequency d) (i : Fin d) : Polynomial ℝ :=
  Polynomial.Chebyshev.T ℝ ((k i).natAbs : ℤ)

def term {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) (y : Space d) : ℝ :=
  (a k).re * (2^is.length * unitTensor (iteratePolynomials (polynomials k) is) y)

def series {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (y : Space d) : ℝ :=
  ∑' k, term a is k y

def majorant {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) : ℝ :=
  2^is.length * (radialWeight (2*is.length*d) k * ‖a k‖)

theorem tensor_bound {d : ℕ} (is : List (Fin d)) (k : Frequency d)
    {y : Space d} (hy : y ∈ closedCube d) :
    ‖unitTensor (iteratePolynomials (polynomials k) is) y‖ ≤ radialWeight (2*is.length*d) k := by
  rw [unitTensor, norm_prod]
  have hfactor (i : Fin d) :
      ‖(iteratePolynomials (polynomials k) is i).eval (2*y i-1)‖ ≤ radialWeight (2*is.length) k := by
    have hcoord := ChebyshevProfile.mem_closedCube.mp (CubeProfileMonotone.fromUnitCube_mapsTo d hy) i
    have hp := ChebyshevDerivativeBound.polynomial_derivative_bound (k i).natAbs (is.count i) hcoord
    change |(iteratePolynomials (polynomials k) is i).eval (2*y i-1)| ≤ _ at hp
    apply hp.trans
    apply le_trans (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k i).natAbs) ?_ (2*is.count i))
    · exact pow_le_pow_right₀ (by linarith [frequencyRadius_nonneg k])
        (Nat.mul_le_mul_left 2 List.count_le_length)
    · have hr := coordinate_abs_le_radius k i
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
  calc
    _ ≤ ∏ _ : Fin d, radialWeight (2*is.length) k :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hfactor i)
    _ = _ := by simp [radialWeight, ← pow_mul]

theorem term_bound {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d)
    {y : Space d} (hy : y ∈ closedCube d) : ‖term a is k y‖ ≤ majorant a is k := by
  rw [term, norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ ‖a k‖ * (2^is.length * radialWeight (2*is.length*d) k) :=
      mul_le_mul (by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (a k))
        (mul_le_mul_of_nonneg_left (tensor_bound is k hy) (by positivity))
        (by positivity) (norm_nonneg _)
    _ = _ := by dsimp [majorant]; ring

theorem majorant_summable {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d)) : Summable (majorant a is) :=
  (ha (2*is.length*d)).mul_left _

theorem term_contDiff {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) :
    ContDiff ℝ ∞ (term a is k) :=
  contDiff_const.mul (contDiff_const.mul (unitTensor_contDiff _))

theorem term_summable {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d))
    {y : Space d} (hy : y ∈ closedCube d) : Summable (fun k => term a is k y) :=
  (majorant_summable a ha is).of_norm_bounded (fun k => term_bound a is k hy)

theorem series_continuousOn {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d)) :
    ContinuousOn (series a is) (closedCube d) :=
  continuousOn_tsum (fun k => (term_contDiff a is k).continuous.continuousOn)
    (majorant_summable a ha is) (fun k _ hy => term_bound a is k hy)

theorem update_mem_closedCube {d : ℕ} {y : Space d} (hy : y ∈ closedCube d)
    (i : Fin d) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Function.update y i s ∈ closedCube d := by
  constructor <;> intro j <;> by_cases he : j = i
  · subst j; simpa using hs.1
  · simpa [Function.update_of_ne he] using hy.1 j
  · subst j; simpa using hs.2
  · simpa [Function.update_of_ne he] using hy.2 j

theorem term_slice_hasDerivAt {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) (y : Space d) (i : Fin d) (s : ℝ) :
    HasDerivAt (fun t => term a is k (Function.update y i t))
      (term a (is ++ [i]) k (Function.update y i s)) s := by
  have h := ((unitTensor_slice_hasDerivAt (iteratePolynomials (polynomials k) is) y i s).const_mul
    (2^is.length)).const_mul (a k).re
  convert! h using 1
  rw [term, iteratePolynomials_snoc]
  simp only [List.length_append, List.length_singleton, pow_succ]
  ring

theorem series_slice_hasDerivWithinAt {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d))
    {y : Space d} (hy : y ∈ closedCube d) (i : Fin d) :
    HasDerivWithinAt (fun t => series a is (Function.update y i t))
      (series a (is ++ [i]) y) (Icc (0 : ℝ) 1) (y i) := by
  have h := ClosedIntervalDerivativeSeries.hasDerivWithinAt_tsum
    (majorant_summable a ha is) (majorant_summable a ha (is ++ [i]))
    (fun k t => term_slice_hasDerivAt a is k y i t)
    (fun k => ((term_contDiff a (is ++ [i]) k).continuous.comp (by fun_prop)).continuousOn)
    (fun k t ht => term_bound a is k (update_mem_closedCube hy i ht))
    (fun k t ht => term_bound a (is ++ [i]) k (update_mem_closedCube hy i ht))
    (show y i ∈ Icc (0 : ℝ) 1 from ⟨hy.1 i, hy.2 i⟩)
  simpa only [series, Function.update_eq_self] using h

theorem series_nil {d : ℕ} (a : Frequency d → ℂ) :
    series a [] = fun y => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube y) := by
  funext y
  apply tsum_congr
  intro k
  simp only [term, List.length_nil, pow_zero, one_mul, iteratePolynomials_nil]
  rfl

theorem mixedPartial_profile {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d))
    {y : Space d} (hy : y ∈ closedCube d) :
    mixedPartial is (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y =
      series a is y := by
  have hF := CubeProfileMonotone.unit_profile_contDiffOn (ChebyshevProfile.profile_contDiffOn a ha)
  induction is using List.reverseRecOn generalizing y with
  | nil => rw [mixedPartial_nil, series_nil]
  | append_singleton is i ih =>
    rw [mixedPartial_append_single]
    have hd := hasDerivWithinAt_coordinate_of_contDiffOn (contDiffOn_mixedPartial hF is) i hy
    have hs := (series_slice_hasDerivWithinAt a ha is hy i).congr_of_mem
      (fun t ht => ih (update_mem_closedCube hy i ht))
      (show y i ∈ Icc (0 : ℝ) 1 from ⟨hy.1 i, hy.2 i⟩)
    have huniq := uniqueDiffOn_Icc_zero_one (y i) ⟨hy.1 i, hy.2 i⟩
    exact (hd.derivWithin huniq).symm.trans (hs.derivWithin huniq)

#print axioms mixedPartial_profile
#print axioms series_slice_hasDerivWithinAt
end Legacy.BecknerOnofri.ChebyshevMixedSeries
