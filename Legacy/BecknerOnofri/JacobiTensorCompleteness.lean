import Legacy.BecknerOnofri.JacobiTensorBasis
import Legacy.BecknerOnofri.TensorBernstein
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Completeness for actual finite tensor products of Jacobi eigenfunctions. -/
noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
namespace Legacy.BecknerOnofri.JacobiTensor
open JacobiEigenfunctions

def angularEvalLinear (m : ℕ) (t : ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := angularPolynomial m p t
  map_add' p q := by simp [angularPolynomial, mul_add]
  map_smul' c p := by simp [angularPolynomial]; ring

def tensorPolynomialMap {d : ℕ} (a : Index d) (x : Space d) :
    MultilinearMap ℝ (fun _ : Fin d => Polynomial ℝ) ℝ :=
  (MultilinearMap.mkPiRing ℝ (Fin d) 1).compLinearMap (fun i => angularEvalLinear (a i) (x i))

def tensorPolynomial {d : ℕ} (a : Index d) (p : Fin d → Polynomial ℝ) (x : Space d) : ℝ :=
  tensorPolynomialMap a x p

theorem tensorPolynomial_apply {d : ℕ} (a : Index d) (p : Fin d → Polynomial ℝ) (x : Space d) :
    tensorPolynomial a p x = ∏ i, angularPolynomial (a i) (p i) (x i) := by
  simp [tensorPolynomial, tensorPolynomialMap, MultilinearMap.mkPiRing_apply, angularEvalLinear]

theorem tensorPolynomial_continuous {d : ℕ} (a : Index d) (p : Fin d → Polynomial ℝ) :
    Continuous (tensorPolynomial a p) := by
  simp only [funext (tensorPolynomial_apply a p)]
  exact continuous_finsetProd _ (fun i _ =>
    (angularPolynomial_continuous (a i) (p i)).comp (continuous_apply i))

theorem tensorPolynomial_bounded {d : ℕ} (a : Index d) (p : Fin d → Polynomial ℝ) :
    ∃ C : ℝ, ∀ x, ‖tensorPolynomial a p x‖ ≤ C := by
  choose C hC using fun i => angularPolynomial_bounded (a i) (p i)
  refine ⟨∏ i, C i, fun x => ?_⟩
  rw [tensorPolynomial_apply, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hC i (x i))

theorem tensorPolynomial_memLp {d : ℕ} (a : Index d) (p : Fin d → Polynomial ℝ) :
    MemLp (tensorPolynomial a p) 2 (measure d) := by
  obtain ⟨C, hC⟩ := tensorPolynomial_bounded a p
  exact MemLp.of_bound (tensorPolynomial_continuous a p).aestronglyMeasurable C (ae_of_all _ hC)

theorem tensorPolynomial_pair_integrable {d : ℕ} (u : TensorL2 d)
    (a : Index d) (p : Fin d → Polynomial ℝ) :
    Integrable (fun x => u x * tensorPolynomial a p x) (measure d) :=
  (Lp.memLp u).integrable_mul (tensorPolynomial_memLp a p)

def polynomialMoment {d : ℕ} (u : TensorL2 d) (a : Index d) :
    MultilinearMap ℝ (fun _ : Fin d => Polynomial ℝ) ℝ where
  toFun p := ∫ x, u x * tensorPolynomial a p x ∂measure d
  map_update_add' p i q r := by
    simp only [tensorPolynomial, MultilinearMap.map_update_add, mul_add]
    exact integral_add (tensorPolynomial_pair_integrable u a (Function.update p i q))
      (tensorPolynomial_pair_integrable u a (Function.update p i r))
  map_update_smul' p i c q := by
    simp only [tensorPolynomial, MultilinearMap.map_update_smul, smul_eq_mul]
    simp_rw [mul_left_comm _ c]
    exact integral_const_mul c _

def normalizationFactor {d : ℕ} (a n : Index d) : ℝ :=
  ∏ i, (Real.sqrt (normSquared (a i) (n i)))⁻¹

theorem normalizationFactor_ne_zero {d : ℕ} (a n : Index d) : normalizationFactor a n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (normSquared_pos (a i) (n i))))

theorem tensorFunction_eq_raw {d : ℕ} (a n : Index d) (x : Space d) :
    tensorFunction a n x = normalizationFactor a n *
      tensorPolynomial a (fun i => polynomial (a i) (n i)) x := by
  simp only [tensorFunction, normalizedFunction, tensorPolynomial_apply,
    normalizationFactor, Finset.prod_mul_distrib]
  rfl

theorem polynomialMoment_eq_zero {d : ℕ} (u : TensorL2 d) (a : Index d)
    (hu : ∀ n, @inner ℝ (TensorL2 d) _ u (tensorVector a n) = 0)
    (p : Fin d → Polynomial ℝ) : polynomialMoment u a p = 0 := by
  have hz : polynomialMoment u a = 0 := by
    apply Module.Basis.ext_multilinear (fun i => polynomialBasis (a i))
    intro n
    simp only [polynomialBasis_apply, zero_apply]
    have h := hu n
    rw [L2.inner_def] at h
    have hi : (∫ x, u x * tensorFunction a n x ∂measure d) = 0 := by
      rw [← h]
      apply integral_congr_ae
      filter_upwards [tensorVector_ae_eq a n] with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial]
      ring
    simp_rw [tensorFunction_eq_raw, mul_left_comm _ (normalizationFactor a n)] at hi
    rw [integral_const_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left (normalizationFactor_ne_zero a n)
  rw [hz]
  rfl


def sineWeight {d : ℕ} (a : Index d) (x : Space d) : ℝ := ∏ i, Real.sin (x i)^(a i)

theorem sineWeight_continuous {d : ℕ} (a : Index d) : Continuous (sineWeight a) := by
  unfold sineWeight
  fun_prop

theorem sineWeight_norm_le {d : ℕ} (a : Index d) (x : Space d) : ‖sineWeight a x‖ ≤ 1 := by
  rw [sineWeight, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  rw [Real.norm_eq_abs, abs_pow]
  simpa using pow_le_pow_left₀ (abs_nonneg (Real.sin (x i))) (Real.abs_sin_le_one (x i)) (a i)

def weightedFunction {d : ℕ} (u : TensorL2 d) (a : Index d) (x : Space d) : ℝ :=
  u x * sineWeight a x

theorem weightedFunction_memLp {d : ℕ} (u : TensorL2 d) (a : Index d) :
    MemLp (weightedFunction u a) 2 (measure d) := by
  apply (Lp.memLp u).mono
    ((Lp.aestronglyMeasurable u).mul (sineWeight_continuous a).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖u x * sineWeight a x‖ ≤ ‖u x‖
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (sineWeight_norm_le a x)

theorem ae_mem_box (d : ℕ) : ∀ᵐ x ∂measure d, ∀ i, x i ∈ Ioo 0 Real.pi := by
  apply ae_all_iff.mpr
  intro i
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin d => intervalMeasure) i).ae
    (ae_restrict_mem measurableSet_Ioo)

def cubePoint {d : ℕ} (x : Space d) : TensorBernstein.Cube d := fun i =>
  ⟨(Real.cos (x i) + 1)/2, by constructor <;> linarith [Real.neg_one_le_cos (x i), Real.cos_le_one (x i)]⟩

def inversePoint {d : ℕ} (y : TensorBernstein.Cube d) : Space d :=
  fun i => Real.arccos (2*(y i:ℝ)-1)

theorem cubePoint_continuous (d : ℕ) : Continuous (@cubePoint d) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  fun_prop

theorem inversePoint_continuous (d : ℕ) : Continuous (@inversePoint d) := by
  unfold inversePoint
  fun_prop

theorem inversePoint_cubePoint {d : ℕ} {x : Space d} (hx : ∀ i, x i ∈ Ioo 0 Real.pi) :
    inversePoint (cubePoint x) = x := by
  funext i
  change Real.arccos (2*((Real.cos (x i)+1)/2)-1) = x i
  rw [show 2*((Real.cos (x i)+1)/2)-1 = Real.cos (x i) by ring]
  exact Real.arccos_cos (hx i).1.le (hx i).2.le

def shiftedBernstein (m j : ℕ) : Polynomial ℝ :=
  (bernsteinPolynomial ℝ m j).comp (C (1/2) * (X + 1))

theorem shiftedBernstein_eval {d : ℕ} (m j : ℕ) (x : Space d) (i : Fin d) :
    (shiftedBernstein m j).eval (Real.cos (x i)) = bernstein m j (cubePoint x i) := by
  have h : (C (1/2) * (X+1) : Polynomial ℝ).eval (Real.cos (x i)) = (cubePoint x i : ℝ) := by
    simp only [eval_mul, eval_C, eval_add, eval_X, eval_one, cubePoint]
    ring
  rw [shiftedBernstein, eval_comp, h]
  rfl

theorem weighted_bernstein_integrable {d : ℕ} (u : TensorL2 d) (a : Index d)
    (m : ℕ) (f : TensorBernstein.Cube d → ℝ) :
    Integrable (fun x => weightedFunction u a x * TensorBernstein.approx m f (cubePoint x))
      (measure d) := by
  have he : (fun x => weightedFunction u a x * TensorBernstein.approx m f (cubePoint x)) =
      fun x => ∑ j : TensorBernstein.Grid d m, f (TensorBernstein.point j) *
        (u x * tensorPolynomial a (fun i => shiftedBernstein m (j i)) x) := by
    funext x
    simp only [TensorBernstein.approx, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [tensorPolynomial_apply, angularPolynomial, shiftedBernstein_eval,
      Finset.prod_mul_distrib, TensorBernstein.weight, weightedFunction, sineWeight]
    ring
  rw [he]
  exact integrable_finsetSum _ (fun j _ =>
    (tensorPolynomial_pair_integrable u a (fun i => shiftedBernstein m (j i))).const_mul _)

theorem weighted_bernstein_integral_zero {d : ℕ} (u : TensorL2 d) (a : Index d)
    (hu : ∀ n, @inner ℝ (TensorL2 d) _ u (tensorVector a n) = 0)
    (m : ℕ) (f : TensorBernstein.Cube d → ℝ) :
    (∫ x, weightedFunction u a x * TensorBernstein.approx m f (cubePoint x) ∂measure d) = 0 := by
  have he : (fun x => weightedFunction u a x * TensorBernstein.approx m f (cubePoint x)) =
      fun x => ∑ j : TensorBernstein.Grid d m, f (TensorBernstein.point j) *
        (u x * tensorPolynomial a (fun i => shiftedBernstein m (j i)) x) := by
    funext x
    simp only [TensorBernstein.approx, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [tensorPolynomial_apply, angularPolynomial, shiftedBernstein_eval,
      Finset.prod_mul_distrib, TensorBernstein.weight, weightedFunction, sineWeight]
    ring
  rw [he, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j _
    rw [integral_const_mul]
    have hz := polynomialMoment_eq_zero u a hu (fun i => shiftedBernstein m (j i))
    change (∫ x, u x * tensorPolynomial a (fun i => shiftedBernstein m (j i)) x ∂measure d) = 0 at hz
    rw [hz, mul_zero]
  · intro j _
    exact (tensorPolynomial_pair_integrable u a (fun i => shiftedBernstein m (j i))).const_mul _

theorem bernstein_approx_bound {d : ℕ} (g : Space d →ᵇ ℝ) (m : ℕ) (y : TensorBernstein.Cube d) :
    ‖TensorBernstein.approx m (fun z => g (inversePoint z)) y‖ ≤ ‖g‖ := by
  rw [TensorBernstein.approx]
  calc
    _ ≤ ∑ j : TensorBernstein.Grid d m,
        ‖g (inversePoint (TensorBernstein.point j)) * TensorBernstein.weight m j y‖ := norm_sum_le _ _
    _ ≤ ∑ j : TensorBernstein.Grid d m, ‖g‖ * TensorBernstein.weight m j y := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs (TensorBernstein.weight m j y),
        abs_of_nonneg (TensorBernstein.weight_nonneg j y)]
      exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (TensorBernstein.weight_nonneg j y)
    _ = ‖g‖ := by rw [← Finset.mul_sum, TensorBernstein.sum_weight, mul_one]

theorem weighted_continuous_integral_zero {d : ℕ} (u : TensorL2 d) (a : Index d)
    (hu : ∀ n, @inner ℝ (TensorL2 d) _ u (tensorVector a n) = 0) (g : Space d →ᵇ ℝ) :
    (∫ x, weightedFunction u a x * g x ∂measure d) = 0 := by
  let f : TensorBernstein.Cube d → ℝ := fun y => g (inversePoint y)
  have hf : Continuous f := g.continuous.comp (inversePoint_continuous d)
  have hv : Integrable (weightedFunction u a) (measure d) :=
    (weightedFunction_memLp u a).integrable (by norm_num)
  have ht := tendsto_integral_of_dominated_convergence
    (μ := measure d) (F := fun m x => weightedFunction u a x * TensorBernstein.approx m f (cubePoint x))
    (f := fun x => weightedFunction u a x * g x)
    (fun x => ‖weightedFunction u a x‖ * ‖g‖)
    (fun m => (weighted_bernstein_integrable u a m f).aestronglyMeasurable)
    (hv.norm.mul_const ‖g‖)
    (fun m => ae_of_all _ (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (bernstein_approx_bound g m (cubePoint x)) (norm_nonneg _)))
    (by
      filter_upwards [ae_mem_box d] with x hx
      have h := (TensorBernstein.uniform f hf).tendsto_at (cubePoint x)
      have hh := (tendsto_const_nhds (x := weightedFunction u a x)).mul h
      simpa only [f, inversePoint_cubePoint hx] using hh)
  simp_rw [weighted_bernstein_integral_zero u a hu] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds


def weightedVector {d : ℕ} (u : TensorL2 d) (a : Index d) : TensorL2 d :=
  (weightedFunction_memLp u a).toLp (weightedFunction u a)

theorem weightedVector_eq_zero {d : ℕ} (u : TensorL2 d) (a : Index d)
    (hu : ∀ n, @inner ℝ (TensorL2 d) _ u (tensorVector a n) = 0) : weightedVector u a = 0 := by
  apply (BoundedContinuousFunction.toLp_denseRange ℝ (measure d) ℝ
    (p := 2) (by norm_num)).eq_zero_of_inner_left ℝ
  intro g
  rw [L2.inner_def]
  calc
    (∫ x, @inner ℝ ℝ _ (weightedVector u a x)
        (BoundedContinuousFunction.toLp 2 (measure d) ℝ g x) ∂measure d) =
        ∫ x, weightedFunction u a x * g x ∂measure d := by
      apply integral_congr_ae
      filter_upwards [(weightedFunction_memLp u a).coeFn_toLp,
        BoundedContinuousFunction.coeFn_toLp 2 (measure d) ℝ g] with x hx hg
      simp only [weightedVector, hx, hg, RCLike.inner_apply, conj_trivial]
      ring
    _ = 0 := weighted_continuous_integral_zero u a hu g

theorem eq_zero_of_orthogonal {d : ℕ} (u : TensorL2 d) (a : Index d)
    (hu : ∀ n, @inner ℝ (TensorL2 d) _ u (tensorVector a n) = 0) : u = 0 := by
  have hz := weightedVector_eq_zero u a hu
  have hae : weightedFunction u a =ᵐ[measure d] (0 : Space d → ℝ) := by
    have h := (weightedFunction_memLp u a).coeFn_toLp
    change weightedVector u a =ᵐ[measure d] weightedFunction u a at h
    rw [hz] at h
    exact h.symm.trans (Lp.coeFn_zero ℝ 2 (measure d))
  apply Lp.ext
  filter_upwards [hae, ae_mem_box d, Lp.coeFn_zero ℝ 2 (measure d)] with x hx hmem hz
  rw [hz]
  apply (mul_eq_zero.mp hx).resolve_right
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero (a i) (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (hmem i).1 (hmem i).2))

theorem orthogonalComplement {d : ℕ} (a : Index d) :
    (Submodule.span ℝ (range (tensorVector a)))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  apply eq_zero_of_orthogonal u a
  intro n
  exact Submodule.inner_left_of_mem_orthogonal
    (Submodule.subset_span (mem_range_self n)) hu

/-- The concrete product functions are a complete Hilbert basis for the product Lebesgue measure. -/
def hilbertBasis {d : ℕ} (a : Index d) : HilbertBasis (Index d) ℝ (TensorL2 d) :=
  HilbertBasis.mkOfOrthogonalEqBot (tensorVector_orthonormal a) (orthogonalComplement a)

@[simp] theorem hilbertBasis_apply {d : ℕ} (a n : Index d) :
    hilbertBasis a n = tensorVector a n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

theorem hilbertBasis_repr {d : ℕ} (a : Index d) (u : TensorL2 d) (n : Index d) :
    (hilbertBasis a).repr u n = ∫ x, tensorFunction a n x * u x ∂measure d := by
  rw [HilbertBasis.repr_apply_apply, hilbertBasis_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensorVector_ae_eq a n] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

#print axioms eq_zero_of_orthogonal
#print axioms hilbertBasis
end Legacy.BecknerOnofri.JacobiTensor
