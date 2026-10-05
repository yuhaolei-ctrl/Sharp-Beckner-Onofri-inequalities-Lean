module

public import Legacy.BecknerOnofri.JacobiEigenfunctions
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

/-! Completeness of the actual Jacobi eigenfunctions. -/
noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped ContDiff Topology BoundedContinuousFunction
namespace Legacy.BecknerOnofri.JacobiEigenfunctions

theorem iterate_derivative_natDegree (p : Polynomial ℝ) (m : ℕ) :
    (derivative^[m] p).natDegree = p.natDegree - m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', natDegree_derivative, ih]
    omega

theorem polynomial_ne_zero (m n : ℕ) : polynomial m n ≠ 0 := by
  intro h
  have hp := polynomial_endpoint_pos m n
  simp only [h, eval_zero, lt_self_iff_false] at hp

theorem polynomial_degree (m n : ℕ) : (polynomial m n).degree = n := by
  rw [degree_eq_natDegree (polynomial_ne_zero m n)]
  congr 1
  simp only [polynomial, iterate_derivative_natDegree, Chebyshev.natDegree_T,
    Int.natAbs_natCast, Nat.add_sub_cancel_right]

def polynomialSequence (m : ℕ) : Polynomial.Sequence ℝ where
  elems' := polynomial m
  degree_eq' := polynomial_degree m

def polynomialBasis (m : ℕ) : Module.Basis ℕ ℝ (Polynomial ℝ) :=
  (polynomialSequence m).basis (fun n => isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr (polynomial_ne_zero m n)))

@[simp] theorem polynomialBasis_apply (m n : ℕ) : polynomialBasis m n = polynomial m n :=
  Polynomial.Sequence.basis_eq_self _ _ _

def angularPolynomial (m : ℕ) (p : Polynomial ℝ) (t : ℝ) : ℝ :=
  Real.sin t^m * p.eval (Real.cos t)

theorem angularPolynomial_continuous (m : ℕ) (p : Polynomial ℝ) :
    Continuous (angularPolynomial m p) :=
  (Real.continuous_sin.pow m).mul
    ((JacobiAngular.polynomial_contDiff p).continuous.comp Real.continuous_cos)

theorem angularPolynomial_bounded (m : ℕ) (p : Polynomial ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, ‖angularPolynomial m p t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) (JacobiAngular.polynomial_contDiff p).continuous.continuousOn
  refine ⟨C, fun t => ?_⟩
  have hs : |Real.sin t|^m ≤ (1 : ℝ) := by
    simpa using pow_le_pow_left₀ (abs_nonneg (Real.sin t)) (Real.abs_sin_le_one t) m
  rw [angularPolynomial, norm_mul, Real.norm_eq_abs (Real.sin t ^ m), abs_pow]
  calc
    |Real.sin t|^m * ‖p.eval (Real.cos t)‖ ≤ 1 * ‖p.eval (Real.cos t)‖ :=
      mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ C := by simpa using hC (Real.cos t) ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩

theorem angularPolynomial_memLp (m : ℕ) (p : Polynomial ℝ) :
    MemLp (angularPolynomial m p) 2 intervalMeasure := by
  obtain ⟨C, hC⟩ := angularPolynomial_bounded m p
  exact MemLp.of_bound (angularPolynomial_continuous m p).aestronglyMeasurable C (ae_of_all _ hC)

theorem angularPolynomial_pair_integrable (u : JacobiL2) (m : ℕ) (p : Polynomial ℝ) :
    Integrable (fun t => u t * angularPolynomial m p t) intervalMeasure :=
  (Lp.memLp u).integrable_mul (angularPolynomial_memLp m p)

def polynomialMoment (u : JacobiL2) (m : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ t, u t * angularPolynomial m p t ∂intervalMeasure
  map_add' p q := by
    simp only [angularPolynomial, eval_add, mul_add]
    exact integral_add (angularPolynomial_pair_integrable u m p)
      (angularPolynomial_pair_integrable u m q)
  map_smul' c p := by
    simp only [angularPolynomial, eval_smul, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ t, u t * (Real.sin t^m * (c * p.eval (Real.cos t))) =
      c * (u t * (Real.sin t^m * p.eval (Real.cos t))) by intro t; ring]
    exact integral_const_mul c _

theorem polynomialMoment_eq_zero (u : JacobiL2) (m : ℕ)
    (hu : ∀ n, @inner ℝ JacobiL2 _ u (eigenvector m n) = 0) (p : Polynomial ℝ) :
    polynomialMoment u m p = 0 := by
  have h : polynomialMoment u m = 0 := by
    apply (polynomialBasis m).ext
    intro n
    rw [polynomialBasis_apply]
    change (∫ t, u t * eigenfunction m n t ∂intervalMeasure) = 0
    rw [← hu n, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [eigenvector_ae_eq m n] with t ht
    simp only [ht, RCLike.inner_apply, conj_trivial]
    ring
  rw [h]
  rfl


def weightedFunction (u : JacobiL2) (m : ℕ) (t : ℝ) : ℝ := u t * Real.sin t^m

theorem weightedFunction_memLp (u : JacobiL2) (m : ℕ) :
    MemLp (weightedFunction u m) 2 intervalMeasure := by
  apply (Lp.memLp u).mono
    ((Lp.aestronglyMeasurable u).mul (Real.continuous_sin.pow m).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖u t * Real.sin t^m‖ ≤ ‖u t‖
  rw [norm_mul, Real.norm_eq_abs (Real.sin t^m), abs_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (by
    simpa using pow_le_pow_left₀ (abs_nonneg (Real.sin t)) (Real.abs_sin_le_one t) m)

theorem weightedFunction_integrable (u : JacobiL2) (m : ℕ) :
    Integrable (weightedFunction u m) intervalMeasure :=
  (weightedFunction_memLp u m).integrable (by norm_num)

theorem weighted_polynomial_integral_zero (u : JacobiL2) (m : ℕ)
    (hu : ∀ n, @inner ℝ JacobiL2 _ u (eigenvector m n) = 0) (p : Polynomial ℝ) :
    (∫ t, weightedFunction u m t * p.eval (Real.cos t) ∂intervalMeasure) = 0 := by
  have h := polynomialMoment_eq_zero u m hu p
  simpa only [polynomialMoment, LinearMap.coe_mk, AddHom.coe_mk,
    angularPolynomial, weightedFunction, mul_assoc] using h

theorem weighted_continuous_integral_zero (u : JacobiL2) (m : ℕ)
    (hu : ∀ n, @inner ℝ JacobiL2 _ u (eigenvector m n) = 0) (g : ℝ →ᵇ ℝ) :
    (∫ t, weightedFunction u m t * g t ∂intervalMeasure) = 0 := by
  let v := weightedFunction u m
  have hv : Integrable v intervalMeasure := weightedFunction_integrable u m
  have hg : Integrable (fun t => v t * g t) intervalMeasure :=
    hv.mul_bdd g.continuous.aestronglyMeasurable (ae_of_all _ g.norm_coe_le_norm)
  have hnorm : 0 ≤ ∫ t, ‖v t‖ ∂intervalMeasure := integral_nonneg (fun _ => norm_nonneg _)
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / ((∫ t, ‖v t‖ ∂intervalMeasure) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun z => g (Real.arccos z)) (g.continuous.comp Real.continuous_arccos).continuousOn δ hδ
  have hp' : ∀ t ∈ Ioo 0 Real.pi, ‖p.eval (Real.cos t) - g t‖ ≤ δ := by
    intro t ht
    simpa only [Real.arccos_cos ht.1.le ht.2.le, Real.norm_eq_abs] using
      (hp (Real.cos t) ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩).le
  have hpi : Integrable (fun t => v t * p.eval (Real.cos t)) intervalMeasure := by
    simpa only [v, weightedFunction, angularPolynomial, mul_assoc] using
      angularPolynomial_pair_integrable u m p
  have hzero : (∫ t, v t * p.eval (Real.cos t) ∂intervalMeasure) = 0 :=
    weighted_polynomial_integral_zero u m hu p
  have hdiff : Integrable (fun t => v t * (p.eval (Real.cos t) - g t)) intervalMeasure := by
    convert hpi.sub hg using 1
    funext t
    simp only [Pi.sub_apply, mul_sub]
  have hbound : (∫ t, ‖v t * (p.eval (Real.cos t) - g t)‖ ∂intervalMeasure) ≤
      ∫ t, δ * ‖v t‖ ∂intervalMeasure := by
    apply integral_mono_ae hdiff.norm (hv.norm.const_mul δ)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [norm_mul, mul_comm δ]
    exact mul_le_mul_of_nonneg_left (hp' t ht) (norm_nonneg _)
  have herr := (norm_integral_le_integral_norm
    (μ := intervalMeasure) (fun t => v t * (p.eval (Real.cos t) - g t))).trans hbound
  simp_rw [mul_sub] at herr
  rw [integral_sub hpi hg, hzero, zero_sub, norm_neg, integral_const_mul] at herr
  have hscale : δ * (∫ t, ‖v t‖ ∂intervalMeasure) ≤ ε := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < (∫ t, ‖v t‖ ∂intervalMeasure) + 1)).mpr
    change ε * (∫ t, ‖v t‖ ∂intervalMeasure) ≤
      ε * ((∫ t, ‖v t‖ ∂intervalMeasure) + 1)
    nlinarith
  simpa only [zero_add] using herr.trans hscale

def weightedVector (u : JacobiL2) (m : ℕ) : JacobiL2 :=
  (weightedFunction_memLp u m).toLp (weightedFunction u m)

theorem weightedVector_eq_zero (u : JacobiL2) (m : ℕ)
    (hu : ∀ n, @inner ℝ JacobiL2 _ u (eigenvector m n) = 0) :
    weightedVector u m = 0 := by
  apply (BoundedContinuousFunction.toLp_denseRange ℝ intervalMeasure ℝ
    (p := 2) (by norm_num)).eq_zero_of_inner_left ℝ
  intro g
  rw [L2.inner_def]
  calc
    (∫ t, @inner ℝ ℝ _ (weightedVector u m t)
        (BoundedContinuousFunction.toLp 2 intervalMeasure ℝ g t) ∂intervalMeasure) =
        ∫ t, weightedFunction u m t * g t ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [(weightedFunction_memLp u m).coeFn_toLp,
        BoundedContinuousFunction.coeFn_toLp 2 intervalMeasure ℝ g] with t ht hg
      simp only [weightedVector, ht, hg, RCLike.inner_apply, conj_trivial]
      ring
    _ = 0 := weighted_continuous_integral_zero u m hu g

theorem eq_zero_of_orthogonal_eigenvector (u : JacobiL2) (m : ℕ)
    (hu : ∀ n, @inner ℝ JacobiL2 _ u (eigenvector m n) = 0) : u = 0 := by
  have hz := weightedVector_eq_zero u m hu
  have hae : weightedFunction u m =ᵐ[intervalMeasure] (0 : ℝ → ℝ) := by
    have h := (weightedFunction_memLp u m).coeFn_toLp
    change weightedVector u m =ᵐ[intervalMeasure] weightedFunction u m at h
    rw [hz] at h
    exact h.symm.trans (Lp.coeFn_zero ℝ 2 intervalMeasure)
  apply Lp.ext
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo, Lp.coeFn_zero ℝ 2 intervalMeasure]
    with t ht hmem hzero
  rw [hzero]
  exact (mul_eq_zero.mp ht).resolve_right
    (pow_ne_zero m (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2)))


theorem eq_zero_of_orthogonal_normalizedVector (u : JacobiL2) (m : ℕ)
    (hu : ∀ n, @inner ℝ JacobiL2 _ u (normalizedVector m n) = 0) : u = 0 := by
  apply eq_zero_of_orthogonal_eigenvector u m
  intro n
  have hn := hu n
  rw [normalizedVector, inner_smul_right] at hn
  exact (mul_eq_zero.mp hn).resolve_left (inv_ne_zero
    (ne_of_gt (Real.sqrt_pos.mpr (normSquared_pos m n))))

theorem normalizedVector_orthogonalComplement (m : ℕ) :
    (Submodule.span ℝ (range (normalizedVector m)))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  apply eq_zero_of_orthogonal_normalizedVector u m
  intro n
  exact Submodule.inner_left_of_mem_orthogonal
    (Submodule.subset_span (mem_range_self n)) hu

/-- The actual normalized Jacobi functions form a Hilbert basis of Lebesgue L² `(0,π)`. -/
def hilbertBasis {m : ℕ} (hm : 0 < m) : HilbertBasis ℕ ℝ JacobiL2 :=
  HilbertBasis.mkOfOrthogonalEqBot (normalizedVector_orthonormal hm)
    (normalizedVector_orthogonalComplement m)

@[simp] theorem hilbertBasis_apply {m : ℕ} (hm : 0 < m) (n : ℕ) :
    hilbertBasis hm n = normalizedVector m n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

#print axioms eq_zero_of_orthogonal_eigenvector
#print axioms hilbertBasis
end Legacy.BecknerOnofri.JacobiEigenfunctions
