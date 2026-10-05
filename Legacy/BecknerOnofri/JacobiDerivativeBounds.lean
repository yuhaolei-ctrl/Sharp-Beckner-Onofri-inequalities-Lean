import Legacy.BecknerOnofri.JacobiNormalizationBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Polynomial bounds for every actual spatial derivative of the normalized Jacobi eigenfunctions. -/
noncomputable section
open Set Polynomial
open scoped BigOperators ContDiff
namespace Legacy.BecknerOnofri.JacobiHeatBounds
open JacobiEigenfunctions

def sinPowBound : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m+1, k => ∑ i ∈ Finset.range (k+1), k.choose i*sinPowBound m (k-i)

def rawDerivativeConstant (m k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k+1), k.choose i*sinPowBound m i*(k-i).factorial

def derivativeConstant (m k : ℕ) : ℝ := (rawDerivativeConstant m k:ℝ)*16^(m+1)
def derivativeDegree (m k : ℕ) : ℕ := (2*m+2)*(m+1)+2*(m+k)

theorem sin_derivative_norm_le_one (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k Real.sin x‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
  exact Real.abs_iteratedDeriv_sin_le_one k x

theorem cos_derivative_norm_le_one (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k Real.cos x‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
  exact Real.abs_iteratedDeriv_cos_le_one k x

theorem sin_pow_derivative_bound (m k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ => Real.sin y^m) x‖ ≤ (sinPowBound m k:ℝ) := by
  induction m generalizing k with
  | zero =>
    simp only [pow_zero,sinPowBound]
    by_cases hk : k=0
    · subst k; simp
    · rw [iteratedFDeriv_const_of_ne hk]; norm_num
  | succ m ih =>
    have hh := norm_iteratedFDeriv_mul_le (N := ∞) Real.contDiff_sin (Real.contDiff_sin.pow m) x
      (n := k) (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
    have he : (fun y : ℝ => Real.sin y^(m+1)) = fun y => Real.sin y*Real.sin y^m := by
      funext y; rw [pow_succ]; ring
    rw [he]
    refine hh.trans ?_
    rw [sinPowBound,Nat.cast_sum]
    apply Finset.sum_le_sum
    intro i _
    have hmul := mul_le_mul (sin_derivative_norm_le_one i x) (ih (k-i)) (norm_nonneg _) zero_le_one
    have hc := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg (k.choose i) : (0:ℝ) ≤ k.choose i)
    simpa only [Nat.cast_mul,one_mul,mul_assoc] using hc

theorem polynomial_all_derivative_bound (m n j k : ℕ) (hjk : j ≤ k) (x : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y => (polynomial m n).eval y) (Real.cos x)‖ ≤ degreeBase m n^(2*(m+k)) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,
    ChebyshevDerivativeBound.iterate_deriv_eval,Real.norm_eq_abs]
  have he : derivative^[j] (polynomial m n) = derivative^[j+m] (Chebyshev.T ℝ ((n+m:ℕ):ℤ)) := by
    rw [polynomial,Function.iterate_add_apply]
  rw [he]
  have hh := ChebyshevDerivativeBound.polynomial_derivative_bound (n+m) (j+m)
    (x := Real.cos x) ⟨Real.neg_one_le_cos x,Real.cos_le_one x⟩
  have hn : ((n+m:ℕ):ℝ) ≤ degreeBase m n := by dsimp [degreeBase]; push_cast; linarith
  exact hh.trans ((pow_le_pow_left₀ (Nat.cast_nonneg (n+m) : (0:ℝ) ≤ (n+m:ℕ)) hn _).trans
    (pow_le_pow_right₀ (degreeBase_one_le m n) (by omega)))

theorem polynomial_cos_derivative_bound (m n k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => (polynomial m n).eval (Real.cos y)) x‖ ≤
      (k.factorial:ℝ)*degreeBase m n^(2*(m+k)) := by
  have hh := norm_iteratedFDeriv_comp_le (JacobiAngular.polynomial_contDiff (polynomial m n))
    Real.contDiff_cos (n := k) (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤)) x
    (C := degreeBase m n^(2*(m+k))) (D := 1)
    (fun j hj => polynomial_all_derivative_bound m n j k hj x)
    (fun j _ _ => by simpa using cos_derivative_norm_le_one j x)
  simpa only [Function.comp_def,one_pow,mul_one] using hh

theorem eigenfunction_derivative_bound (m n k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (eigenfunction m n) x‖ ≤
      (rawDerivativeConstant m k:ℝ)*degreeBase m n^(2*(m+k)) := by
  have hh := norm_iteratedFDeriv_mul_le (Real.contDiff_sin.pow m)
    ((JacobiAngular.polynomial_contDiff (polynomial m n)).comp Real.contDiff_cos) x
    (n := k) (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
  change ‖iteratedFDeriv ℝ k (fun y => Real.sin y^m*(polynomial m n).eval (Real.cos y)) x‖ ≤ _
  refine hh.trans ?_
  rw [rawDerivativeConstant,Nat.cast_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hp := polynomial_cos_derivative_bound m n (k-i) x
  have hp' : ‖iteratedFDeriv ℝ (k-i) (fun y => (polynomial m n).eval (Real.cos y)) x‖ ≤
      ((k-i).factorial:ℝ)*degreeBase m n^(2*(m+k)) := by
    refine hp.trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (degreeBase_one_le m n) (by omega)) (Nat.cast_nonneg _)
  have hm := mul_le_mul (sin_pow_derivative_bound m i x) hp' (norm_nonneg _) (Nat.cast_nonneg _)
  have hc := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (k.choose i) : (0:ℝ) ≤ k.choose i)
  simpa only [Nat.cast_mul,mul_assoc,Function.comp_def] using! hc

theorem normalizedFunction_derivative_bound (m n k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (normalizedFunction m n) x‖ ≤
      derivativeConstant m k*degreeBase m n^(derivativeDegree m k) := by
  have hcd : ContDiffAt ℝ (k:ℕ∞ω) (eigenfunction m n) x :=
    ((eigenfunction_contDiff m n).of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).contDiffAt
  have he := iteratedFDeriv_const_smul_apply' (a := (Real.sqrt (normSquared m n))⁻¹) hcd
  simp only [smul_eq_mul] at he
  change ‖iteratedFDeriv ℝ k (fun y => (Real.sqrt (normSquared m n))⁻¹*eigenfunction m n y) x‖ ≤ _
  rw [he,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (normSquared_pos m n)))]
  have hh := mul_le_mul (inverse_sqrt_normSquared_bound m n) (eigenfunction_derivative_bound m n k x)
    (norm_nonneg _) (normalizationBound_nonneg m n)
  refine hh.trans_eq ?_
  dsimp [normalizationBound,derivativeConstant,derivativeDegree]
  rw [mul_pow,← pow_mul,pow_add]
  ring

#print axioms normalizedFunction_derivative_bound
end Legacy.BecknerOnofri.JacobiHeatBounds
