module

public import Legacy.BecknerOnofri.JacobiEigenfunctions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! Polynomial control of the actual Jacobi L2 normalization, from an explicit
positive interval near the Chebyshev endpoint. -/
noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators
namespace Legacy.BecknerOnofri.JacobiHeatBounds
open JacobiEigenfunctions

def degreeBase (m n : ℕ) : ℝ := ((n+m+1:ℕ):ℝ)
def localScale (m n : ℕ) : ℝ := 1/(4*degreeBase m n^(2*m+2))
def normalizationBound (m n : ℕ) : ℝ := (16*degreeBase m n^(2*m+2))^(m+1)

theorem degreeBase_one_le (m n : ℕ) : 1 ≤ degreeBase m n := by
  dsimp [degreeBase]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n+m))

theorem degreeBase_pos (m n : ℕ) : 0 < degreeBase m n := lt_of_lt_of_le zero_lt_one (degreeBase_one_le m n)

theorem localScale_pos (m n : ℕ) : 0 < localScale m n := by
  unfold localScale
  exact one_div_pos.mpr (mul_pos (by norm_num) (pow_pos (degreeBase_pos m n) _))

theorem localScale_le_quarter (m n : ℕ) : localScale m n ≤ 1/4 := by
  unfold localScale
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [(one_le_pow₀ (n := 2*m+2) (degreeBase_one_le m n))]

theorem endpoint_one_le (N m : ℕ) (hm : m ≤ N) :
    1 ≤ (derivative^[m] (Chebyshev.T ℝ (N:ℤ))).eval 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp := ih (Nat.le_of_succ_le hm)
    have hN : (m:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast hm
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hr := Chebyshev.iterate_derivative_T_eval_one_recurrence (R := ℝ) (N:ℤ) m
    simp only [Int.cast_natCast] at hr
    have hfac : 2*(m:ℝ)+1 ≤ (N:ℝ)^2-(m:ℝ)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (N:ℝ)^2-(m:ℝ)^2 by linarith)
    nlinarith

theorem polynomial_endpoint_one_le (m n : ℕ) : 1 ≤ (polynomial m n).eval 1 :=
  endpoint_one_le (n+m) m (Nat.le_add_left m n)

theorem polynomial_derivative_degree_bound (m n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    ‖(polynomial m n).derivative.eval x‖ ≤ degreeBase m n^(2*m+2) := by
  have hp := ChebyshevDerivativeBound.polynomial_derivative_bound (n+m) (m+1) hx
  have he : (polynomial m n).derivative = derivative^[m+1] (Chebyshev.T ℝ ((n+m:ℕ):ℤ)) := by
    simp only [polynomial,Function.iterate_succ_apply']
  rw [he,Real.norm_eq_abs]
  refine hp.trans ?_
  have hn : ((n+m:ℕ):ℝ) ≤ degreeBase m n := by dsimp [degreeBase]; push_cast; linarith
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (n+m) : (0:ℝ) ≤ (n+m:ℕ)) hn (2*(m+1))
  convert! hh using 1

theorem polynomial_cos_lower (m n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (localScale m n)) :
    1/2 ≤ (polynomial m n).eval (Real.cos t) := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := Real.cos t) (b := (1:ℝ))
    (fun x _ => ((polynomial m n).hasDerivAt x).hasDerivWithinAt)
    (fun x hx => polynomial_derivative_degree_bound m n ⟨(Real.neg_one_le_cos t).trans hx.1,hx.2.le⟩)
    1 ⟨Real.cos_le_one t,le_rfl⟩
  have hc : 1-Real.cos t ≤ t := by
    have h := Real.abs_cos_sub_cos_le 0 t
    simpa only [Real.cos_zero,zero_sub,abs_neg,abs_of_nonneg ht.1,
      abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one t))] using h
  have hq : 0 ≤ degreeBase m n^(2*m+2) := (pow_pos (degreeBase_pos m n) _).le
  have hmul := mul_le_mul_of_nonneg_left hc hq
  have hscale : degreeBase m n^(2*m+2)*localScale m n = 1/4 := by
    unfold localScale
    field_simp [(pow_pos (degreeBase_pos m n) (2*m+2)).ne']
  have htime := mul_le_mul_of_nonneg_left ht.2 hq
  rw [hscale] at htime
  rw [Real.norm_eq_abs] at hh
  have hp := polynomial_endpoint_one_le m n
  have hl := le_abs_self ((polynomial m n).eval 1-(polynomial m n).eval (Real.cos t))
  linarith

theorem eigenfunction_local_lower (m n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (localScale m n/2) (localScale m n)) :
    (localScale m n/4)^m/2 ≤ eigenfunction m n t := by
  have ht0 : 0 ≤ t := by linarith [localScale_pos m n,ht.1]
  have htpi : t ≤ Real.pi/2 := by linarith [localScale_le_quarter m n,ht.2,Real.pi_gt_three]
  have hs := Real.mul_le_sin ht0 htpi
  have hpi : (1/2:ℝ) ≤ 2/Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
  have hsin : localScale m n/4 ≤ Real.sin t := by
    have hh := mul_le_mul_of_nonneg_right hpi ht0
    linarith [ht.1]
  have hpow := pow_le_pow_left₀ (by linarith [localScale_pos m n] : 0 ≤ localScale m n/4) hsin m
  have hp := polynomial_cos_lower m n ⟨ht0,ht.2⟩
  have hmul := mul_le_mul hpow hp (by norm_num : (0:ℝ) ≤ 1/2)
    (pow_nonneg (by linarith [localScale_pos m n] : 0 ≤ Real.sin t) m)
  dsimp [eigenfunction,JacobiAngular.angular]
  nlinarith only [hmul]

theorem normSquared_local_lower (m n : ℕ) :
    (localScale m n/8)*(localScale m n/4)^(2*m) ≤ normSquared m n := by
  have hd := localScale_pos m n
  have hdl := localScale_le_quarter m n
  have hi : IntervalIntegrable (fun t => eigenfunction m n t^2) volume 0 Real.pi :=
    ((eigenfunction_contDiff m n).continuous.pow 2).intervalIntegrable _ _
  have hsub := intervalIntegral.integral_mono_interval (show 0 ≤ localScale m n/2 by positivity)
    (show localScale m n/2 ≤ localScale m n by linarith)
    (show localScale m n ≤ Real.pi by linarith [Real.pi_gt_three])
    (Filter.Eventually.of_forall (fun t => sq_nonneg (eigenfunction m n t))) hi
  have hbound : ∀ t ∈ Icc (localScale m n/2) (localScale m n),
      ((localScale m n/4)^m/2)^2 ≤ eigenfunction m n t^2 := by
    intro t ht
    exact (sq_le_sq₀ (by positivity) (le_trans (by positivity) (eigenfunction_local_lower m n ht))).mpr
      (eigenfunction_local_lower m n ht)
  have hlow := intervalIntegral.integral_mono_on
    (show localScale m n/2 ≤ localScale m n by linarith)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ((localScale m n/4)^m/2)^2) volume _ _)
    (((eigenfunction_contDiff m n).continuous.pow 2).intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const] at hlow
  rw [intervalIntegral.integral_of_le Real.pi_pos.le,integral_Ioc_eq_integral_Ioo] at hsub
  change _ ≤ normSquared m n at hsub
  have hp : ((localScale m n/4)^m)^2 = (localScale m n/4)^(2*m) := by rw [← pow_mul]; congr 1; omega
  have he : (localScale m n-localScale m n/2)*((localScale m n/4)^m/2)^2 =
      (localScale m n/8)*(localScale m n/4)^(2*m) := by rw [← hp]; ring
  simpa only [smul_eq_mul,he] using hlow.trans hsub

theorem normSquared_polynomial_lower (m n : ℕ) :
    ((localScale m n/4)^(m+1))^2 ≤ normSquared m n := by
  have hh := normSquared_local_lower m n
  have hd := localScale_pos m n
  have hdl := localScale_le_quarter m n
  have ha : (localScale m n/4)^2 ≤ localScale m n/8 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ (localScale m n/4)^(2*m))
  have he : ((localScale m n/4)^(m+1))^2 = (localScale m n/4)^(2*m)*(localScale m n/4)^2 := by
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  rw [he]
  nlinarith only [hh,hmul]

theorem inverse_sqrt_normSquared_bound (m n : ℕ) :
    (Real.sqrt (normSquared m n))⁻¹ ≤ normalizationBound m n := by
  have hd := localScale_pos m n
  have hl := Real.sqrt_le_sqrt (normSquared_polynomial_lower m n)
  rw [Real.sqrt_sq (by positivity)] at hl
  have hinv := (inv_le_inv₀ (Real.sqrt_pos.mpr (normSquared_pos m n))
    (pow_pos (by positivity : 0 < localScale m n/4) (m+1))).mpr hl
  refine hinv.trans_eq ?_
  rw [← inv_pow]
  congr 1
  unfold localScale
  field_simp [(pow_pos (degreeBase_pos m n) (2*m+2)).ne']
  norm_num

theorem normalizationBound_nonneg (m n : ℕ) : 0 ≤ normalizationBound m n := by
  unfold normalizationBound
  exact (pow_pos (mul_pos (by norm_num) (pow_pos (degreeBase_pos m n) _)) _).le

theorem normalizedFunction_norm_bound (m n : ℕ) (x : ℝ) :
    ‖normalizedFunction m n x‖ ≤
      16^(m+1)*degreeBase m n^((2*m+2)*(m+1)+2*m) := by
  have hn : ((n+m:ℕ):ℝ) ≤ degreeBase m n := by dsimp [degreeBase]; push_cast; linarith
  have he := (eigenfunction_norm_bound m n x).trans
    (pow_le_pow_left₀ (Nat.cast_nonneg (n+m) : (0:ℝ) ≤ (n+m:ℕ)) hn (2*m))
  rw [normalizedFunction,norm_mul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (normSquared_pos m n)))]
  have hh := mul_le_mul (inverse_sqrt_normSquared_bound m n) he (norm_nonneg _) (normalizationBound_nonneg m n)
  refine hh.trans_eq ?_
  unfold normalizationBound
  rw [mul_pow,← pow_mul,mul_assoc,← pow_add]

#print axioms inverse_sqrt_normSquared_bound
#print axioms normalizedFunction_norm_bound
end Legacy.BecknerOnofri.JacobiHeatBounds
