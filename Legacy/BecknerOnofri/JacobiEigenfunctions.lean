module

public import Legacy.BecknerOnofri.JacobiAngular
public import Legacy.BecknerOnofri.ChebyshevDerivativeBound
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! The concrete Dirichlet Jacobi eigenfunctions on `(0, π)`.
The differential equation below concerns actual derivatives, and orthogonality
is obtained by integration by parts for the globally smooth eigenfunctions. -/
noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped ContDiff Topology
namespace Legacy.BecknerOnofri.JacobiEigenfunctions

def polynomial (m n : ℕ) : Polynomial ℝ :=
  derivative^[m] (Chebyshev.T ℝ ((n + m : ℕ) : ℤ))

def eigenfunction (m n : ℕ) : ℝ → ℝ :=
  JacobiAngular.angular m (fun x => (polynomial m n).eval x)

def eigenvalue (m n : ℕ) : ℝ := ((n + m : ℕ) : ℝ)^2

def intervalMeasure : Measure ℝ := volume.restrict (Ioo 0 Real.pi)
abbrev JacobiL2 := Lp ℝ 2 intervalMeasure

theorem eigenfunction_contDiff (m n : ℕ) : ContDiff ℝ ∞ (eigenfunction m n) :=
  Real.contDiff_sin.pow m |>.mul
    ((JacobiAngular.polynomial_contDiff _).comp Real.contDiff_cos)

@[simp] theorem eigenfunction_zero {m : ℕ} (hm : 0 < m) (n : ℕ) :
    eigenfunction m n 0 = 0 := by
  simp [eigenfunction, JacobiAngular.angular, ne_of_gt hm]

@[simp] theorem eigenfunction_pi {m : ℕ} (hm : 0 < m) (n : ℕ) :
    eigenfunction m n Real.pi = 0 := by
  simp [eigenfunction, JacobiAngular.angular, ne_of_gt hm]

theorem eigenfunction_hasDerivAt (m n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    HasDerivAt (eigenfunction m n)
      (JacobiAngular.first m (fun x => (polynomial m n).eval x) t) t :=
  JacobiAngular.angular_hasDerivAt m
    ((JacobiAngular.polynomial_contDiff _).differentiable (by simp))
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))

theorem eigenfunction_equation (m n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    JacobiAngular.angularOperator m (eigenfunction m n) t =
      eigenvalue m n * eigenfunction m n t := by
  rw [eigenfunction, JacobiAngular.angular_conjugation_polynomial m _
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))]
  have h := congrArg (fun p : Polynomial ℝ => p.eval (Real.cos t))
    (JacobiPolynomial.shifted_chebyshev_derivative ((n + m : ℕ) : ℤ) m)
  simp only [eval_mul, eval_pow, eval_natCast, Int.cast_natCast] at h
  rw [show (JacobiPolynomial.shifted m (polynomial m n)).eval (Real.cos t) =
    ((n+m : ℕ) : ℝ)^2 * (polynomial m n).eval (Real.cos t) from h]
  simp only [JacobiAngular.angular, eigenvalue]
  ring

theorem eigenfunction_deriv_contDiff (m n : ℕ) :
    ContDiff ℝ ∞ (deriv (eigenfunction m n)) :=
  (contDiff_infty_iff_deriv.mp (eigenfunction_contDiff m n)).2

theorem eigenfunction_second_continuous (m n : ℕ) :
    Continuous (deriv (deriv (eigenfunction m n))) :=
  (contDiff_infty_iff_deriv.mp (eigenfunction_deriv_contDiff m n)).2.continuous

theorem integration_by_parts {m : ℕ} (hm : 0 < m) (n l : ℕ) :
    (∫ t in 0..Real.pi, eigenfunction m n t * deriv (deriv (eigenfunction m l)) t) =
      -(∫ t in 0..Real.pi, deriv (eigenfunction m n) t * deriv (eigenfunction m l) t) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := Real.pi)
    (fun t _ => ((eigenfunction_contDiff m n).differentiable (by simp) t).hasDerivAt)
    (fun t _ => ((eigenfunction_deriv_contDiff m l).differentiable (by simp) t).hasDerivAt)
    ((eigenfunction_deriv_contDiff m n).continuous.intervalIntegrable _ _)
    ((eigenfunction_second_continuous m l).intervalIntegrable _ _)
  simpa only [eigenfunction_zero hm, eigenfunction_pi hm, zero_mul, sub_self, zero_sub] using h

theorem eigenvalue_injective (m : ℕ) : Function.Injective (eigenvalue m) := by
  intro n l h
  have hn : (0 : ℝ) ≤ ((n + m : ℕ) : ℝ) := by positivity
  have hl : (0 : ℝ) ≤ ((l + m : ℕ) : ℝ) := by positivity
  have he : ((n + m : ℕ) : ℝ) = ((l + m : ℕ) : ℝ) := by
    dsimp [eigenvalue] at h
    nlinarith
  exact Nat.add_right_cancel (Nat.cast_injective he)

theorem integral_orthogonal {m : ℕ} (hm : 0 < m) {n l : ℕ} (hne : n ≠ l) :
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
    integration_by_parts hm n l, integration_by_parts hm l n] at hInt
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


theorem derivative_endpoint_pos (N m : ℕ) (hm : m ≤ N) :
    0 < (derivative^[m] (Chebyshev.T ℝ (N : ℤ))).eval 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp := ih (Nat.le_of_succ_le hm)
    have hlt : (m : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_succ_le hm)
    have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hc := Chebyshev.iterate_derivative_T_eval_one_recurrence (R := ℝ) (N : ℤ) m
    simp only [Int.cast_natCast] at hc
    have hfactor : 0 < (N : ℝ)^2 - (m : ℝ)^2 := by nlinarith
    have hprod := mul_pos hfactor hp
    rw [← hc] at hprod
    exact (mul_pos_iff.mp hprod).resolve_right (by intro h; linarith [h.1]) |>.2

theorem polynomial_endpoint_pos (m n : ℕ) : 0 < (polynomial m n).eval 1 :=
  derivative_endpoint_pos (n+m) m (Nat.le_add_left m n)

theorem exists_eigenfunction_pos (m n : ℕ) :
    ∃ t ∈ Ioo 0 Real.pi, 0 < eigenfunction m n t := by
  have hc : Continuous (fun t => (polynomial m n).eval (Real.cos t)) :=
    (JacobiAngular.polynomial_contDiff _).continuous.comp Real.continuous_cos
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (polynomial m n).eval (Real.cos t) :=
    (isOpen_lt continuous_const hc).mem_nhds (by simpa using polynomial_endpoint_pos m n)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hp
  let t := min ε Real.pi / 2
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htε : t < ε := by dsimp [t]; nlinarith [min_le_left ε Real.pi]
  have htπ : t < Real.pi := by dsimp [t]; nlinarith [min_le_right ε Real.pi, Real.pi_pos]
  refine ⟨t, ⟨ht0, htπ⟩, ?_⟩
  exact mul_pos (pow_pos (Real.sin_pos_of_pos_of_lt_pi ht0 htπ) m)
    (he (by simpa [Real.dist_eq, abs_of_pos ht0] using htε))

theorem eigenfunction_norm_bound (m n : ℕ) (t : ℝ) :
    ‖eigenfunction m n t‖ ≤ ((n+m : ℕ) : ℝ)^(2*m) := by
  have hs : |Real.sin t|^m ≤ (1 : ℝ) := by
    simpa using pow_le_pow_left₀ (abs_nonneg (Real.sin t)) (Real.abs_sin_le_one t) m
  have hp := ChebyshevDerivativeBound.polynomial_derivative_bound (n+m) m
    (x := Real.cos t) ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  rw [eigenfunction, JacobiAngular.angular, Real.norm_eq_abs, abs_mul, abs_pow]
  calc
    |Real.sin t|^m * |(polynomial m n).eval (Real.cos t)| ≤
        1 * |(polynomial m n).eval (Real.cos t)| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ ≤ ((n+m : ℕ) : ℝ)^(2*m) := by simpa [polynomial] using hp

instance : IsFiniteMeasure intervalMeasure := by
  unfold intervalMeasure
  infer_instance

theorem eigenfunction_memLp (m n : ℕ) : MemLp (eigenfunction m n) 2 intervalMeasure :=
  MemLp.of_bound (eigenfunction_contDiff m n).continuous.aestronglyMeasurable
    (((n+m : ℕ) : ℝ)^(2*m)) (ae_of_all _ (eigenfunction_norm_bound m n))

def eigenvector (m n : ℕ) : JacobiL2 := (eigenfunction_memLp m n).toLp (eigenfunction m n)

theorem eigenvector_ae_eq (m n : ℕ) :
    eigenvector m n =ᵐ[intervalMeasure] eigenfunction m n :=
  (eigenfunction_memLp m n).coeFn_toLp


theorem eigenvector_inner (m n l : ℕ) :
    @inner ℝ JacobiL2 _ (eigenvector m n) (eigenvector m l) =
      ∫ t in Ioo 0 Real.pi, eigenfunction m n t * eigenfunction m l t := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [eigenvector_ae_eq m n, eigenvector_ae_eq m l] with t hn hl
  simp only [hn, hl, RCLike.inner_apply, conj_trivial]
  ring

def normSquared (m n : ℕ) : ℝ := ∫ t in Ioo 0 Real.pi, eigenfunction m n t^2

theorem normSquared_pos (m n : ℕ) : 0 < normSquared m n := by
  obtain ⟨t, ht, hp⟩ := exists_eigenfunction_pos m n
  have h := intervalIntegral.integral_pos Real.pi_pos
    ((eigenfunction_contDiff m n).continuous.pow 2).continuousOn
    (fun x _ => sq_nonneg (eigenfunction m n x))
    ⟨t, ⟨ht.1.le, ht.2.le⟩, sq_pos_of_pos hp⟩
  simpa only [normSquared, Pi.pow_apply, intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo] using h

theorem eigenvector_inner_self (m n : ℕ) :
    @inner ℝ JacobiL2 _ (eigenvector m n) (eigenvector m n) = normSquared m n := by
  rw [eigenvector_inner]
  simp only [normSquared, pow_two]

theorem eigenvector_ne_zero (m n : ℕ) : eigenvector m n ≠ 0 := by
  intro h
  have hp := normSquared_pos m n
  rw [← eigenvector_inner_self, h, inner_zero_left] at hp
  exact lt_irrefl _ hp

def normalizedFunction (m n : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt (normSquared m n))⁻¹ * eigenfunction m n t

def normalizedVector (m n : ℕ) : JacobiL2 :=
  (Real.sqrt (normSquared m n))⁻¹ • eigenvector m n

theorem normalizedVector_inner_self (m n : ℕ) :
    @inner ℝ JacobiL2 _ (normalizedVector m n) (normalizedVector m n) = 1 := by
  rw [normalizedVector, inner_smul_left, inner_smul_right, eigenvector_inner_self]
  simp only [conj_trivial]
  have hs := Real.sq_sqrt (normSquared_pos m n).le
  have hn := ne_of_gt (Real.sqrt_pos.mpr (normSquared_pos m n))
  field_simp
  nlinarith

theorem normalizedVector_orthogonal {m : ℕ} (hm : 0 < m) {n l : ℕ} (hne : n ≠ l) :
    @inner ℝ JacobiL2 _ (normalizedVector m n) (normalizedVector m l) = 0 := by
  rw [normalizedVector, normalizedVector, inner_smul_left, inner_smul_right,
    eigenvector_inner, integral_orthogonal hm hne, mul_zero, mul_zero]

theorem normalizedVector_orthonormal {m : ℕ} (hm : 0 < m) :
    Orthonormal ℝ (normalizedVector m) := by
  rw [orthonormal_iff_ite]
  intro n l
  split_ifs with h
  · subst l
    exact normalizedVector_inner_self m n
  · exact normalizedVector_orthogonal hm h

theorem normalizedFunction_contDiff (m n : ℕ) :
    ContDiff ℝ ∞ (normalizedFunction m n) :=
  contDiff_const.mul (eigenfunction_contDiff m n)

@[simp] theorem normalizedFunction_zero {m : ℕ} (hm : 0 < m) (n : ℕ) :
    normalizedFunction m n 0 = 0 := by simp [normalizedFunction, eigenfunction_zero hm]

@[simp] theorem normalizedFunction_pi {m : ℕ} (hm : 0 < m) (n : ℕ) :
    normalizedFunction m n Real.pi = 0 := by simp [normalizedFunction, eigenfunction_pi hm]

theorem normalizedVector_ae_eq (m n : ℕ) :
    normalizedVector m n =ᵐ[intervalMeasure] normalizedFunction m n := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (normSquared m n))⁻¹ (eigenvector m n),
    eigenvector_ae_eq m n] with t hs he
  simpa only [normalizedVector, normalizedFunction, Pi.smul_apply, smul_eq_mul, he] using hs

theorem normalizedFunction_equation (m n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    JacobiAngular.angularOperator m (normalizedFunction m n) t =
      eigenvalue m n * normalizedFunction m n t := by
  have hd : deriv (normalizedFunction m n) = fun x =>
      (Real.sqrt (normSquared m n))⁻¹ * deriv (eigenfunction m n) x := by
    funext x
    exact deriv_const_mul _ ((eigenfunction_contDiff m n).differentiable (by simp) x)
  have hdd : deriv (deriv (normalizedFunction m n)) t =
      (Real.sqrt (normSquared m n))⁻¹ * deriv (deriv (eigenfunction m n)) t := by
    rw [hd]
    exact deriv_const_mul _ ((eigenfunction_deriv_contDiff m n).differentiable (by simp) t)
  have he := eigenfunction_equation m n ht
  unfold JacobiAngular.angularOperator at he ⊢
  rw [hdd]
  dsimp only [normalizedFunction]
  linear_combination (Real.sqrt (normSquared m n))⁻¹ * he

#print axioms eigenfunction_equation
#print axioms integral_orthogonal
#print axioms normSquared_pos
#print axioms normalizedVector_orthonormal
end Legacy.BecknerOnofri.JacobiEigenfunctions
