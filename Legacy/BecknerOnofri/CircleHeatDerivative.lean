module

public import Legacy.BecknerOnofri.PolarizationDensity
public import Mathlib.Analysis.Calculus.SmoothSeries

@[expose] public section

/-! Actual Fourier-series differentiation of the unit-circle heat kernel. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint TorusHeatPositivity
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleHeat

def realHeat (t x : ℝ) : ℝ := (theta t (x : UnitAddCircle)).re

def cosineTerm (t : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-Real.pi*t*(n+1:ℝ)^2)*Real.cos (2*Real.pi*(n+1:ℝ)*x)

def sineTerm (t : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (n+1:ℝ)*Real.exp (-Real.pi*t*(n+1:ℝ)^2)*Real.sin (2*Real.pi*(n+1:ℝ)*x)

theorem summable_polynomial_gaussian {A : ℝ} (hA : 0 < A) (k : ℕ) :
    Summable (fun n : ℕ => (n:ℝ)^k*Real.exp (-A*(n:ℝ)^2)) := by
  apply (Real.summable_pow_mul_exp_neg_nat_mul k hA).of_nonneg_of_le (fun _ => by positivity)
  intro n
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  apply Real.exp_le_exp.mpr
  have hn : (n:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast Nat.le_self_pow (by norm_num : 2 ≠ 0) n
  nlinarith

theorem summable_polynomial_gaussian_succ {A : ℝ} (hA : 0 < A) (k : ℕ) :
    Summable (fun n : ℕ => (n+1:ℝ)^k*Real.exp (-A*(n+1:ℝ)^2)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (summable_polynomial_gaussian hA k)

theorem fourier_term_re (t x : ℝ) (n : ℤ) :
    (((Real.exp (-Real.pi*t*(n:ℝ)^2) : ℂ)*fourier n (x : UnitAddCircle))).re =
      Real.exp (-Real.pi*t*(n:ℝ)^2)*Real.cos (2*Real.pi*(n:ℝ)*x) := by
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [fourier_coe_apply, Complex.exp_re]
  simp

theorem summable_cosineTerm {t : ℝ} (ht : 0 < t) (x : ℝ) : Summable (fun n => cosineTerm t n x) := by
  have hs := summable_polynomial_gaussian_succ (mul_pos Real.pi_pos ht) 0
  simp only [pow_zero, one_mul, neg_mul] at hs
  apply hs.of_norm_bounded
  intro n
  unfold cosineTerm
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [neg_mul]
  exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)

theorem realHeat_eq_cosine_series {t : ℝ} (ht : 0 < t) (x : ℝ) :
    realHeat t x = 1+2*∑' n : ℕ, cosineTerm t n x := by
  let f : ℤ → ℝ := fun n => Real.exp (-Real.pi*t*(n:ℝ)^2)*Real.cos (2*Real.pi*(n:ℝ)*x)
  have hs : HasSum f (realHeat t x) := by
    simpa only [fourier_term_re] using! (Complex.hasSum_re (theta_summable ht (x : UnitAddCircle)).hasSum)
  have heven : Function.Even f := by
    intro n
    dsimp [f]
    simp only [Int.cast_neg, neg_sq]
    rw [show 2*Real.pi*(-(n:ℝ))*x = -(2*Real.pi*(n:ℝ)*x) by ring, Real.cos_neg]
  rw [← hs.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs.summable]
  simp only [f, Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.exp_zero,
    zero_mul, Real.cos_zero, mul_one, nsmul_eq_mul, Nat.cast_ofNat, Int.cast_natCast]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => Real.exp (-Real.pi*t*(n:ℝ)^2)*Real.cos (2*Real.pi*(n:ℝ)*x))]
  simp only [cosineTerm, Nat.cast_add, Nat.cast_one]

theorem summable_sineTerm {t : ℝ} (ht : 0 < t) (x : ℝ) : Summable (fun n => sineTerm t n x) := by
  have hs := summable_polynomial_gaussian_succ (mul_pos Real.pi_pos ht) 1
  simp only [pow_one, neg_mul] at hs
  apply hs.of_norm_bounded
  intro n
  unfold sineTerm
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n+1:ℝ)*Real.exp _)]
  simp only [neg_mul]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)

theorem hasDerivAt_cosineTerm (t : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (cosineTerm t n) (-2*Real.pi*sineTerm t n x) x := by
  have hh := ((Real.hasDerivAt_cos (2*Real.pi*(n+1:ℝ)*x)).comp x
    ((hasDerivAt_id x).const_mul (2*Real.pi*(n+1:ℝ)))).const_mul (Real.exp (-Real.pi*t*(n+1:ℝ)^2))
  convert! hh using 1; dsimp [cosineTerm, sineTerm]; ring

theorem hasDerivAt_realHeat {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (realHeat t) (-4*Real.pi*∑' n : ℕ, sineTerm t n x) x := by
  have hs := summable_polynomial_gaussian_succ (mul_pos Real.pi_pos ht) 1
  simp only [pow_one, neg_mul] at hs
  have hd := hasDerivAt_tsum (hs.mul_left (2*Real.pi)) (hasDerivAt_cosineTerm t)
    (g' := fun n x => -2*Real.pi*sineTerm t n x) (by
      intro n y
      norm_num only [norm_mul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
      have hn : ‖sineTerm t n y‖ ≤ (n+1:ℝ)*Real.exp (-Real.pi*t*(n+1:ℝ)^2) := by
        unfold sineTerm
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n+1:ℝ)*Real.exp _)]
        simp only [neg_mul]
        exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
      simpa only [neg_mul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hn (by positivity : 0≤2*Real.pi))
    (summable_cosineTerm ht 0) x
  have hfinal := (hd.const_mul 2).const_add 1
  simp only [tsum_mul_left] at hfinal
  convert! hfinal using 1
  · funext y
    exact realHeat_eq_cosine_series ht y
  · ring

/-- This bound is valid for every angle; on [0,pi] its right hand side is n sin x. -/
theorem abs_sin_nat_mul_le (n : ℕ) (x : ℝ) : |Real.sin ((n:ℝ)*x)| ≤ (n:ℝ)*|Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.sin_add]
    have h1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg (Real.sin ((n:ℝ)*x)))
    have h2 := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one ((n:ℝ)*x)) (abs_nonneg (Real.sin x))
    have ha := abs_add_le (Real.sin ((n:ℝ)*x)*Real.cos x) (Real.cos ((n:ℝ)*x)*Real.sin x)
    rw [abs_mul, abs_mul] at ha
    nlinarith only [ha, h1, h2, ih]

#print axioms hasDerivAt_realHeat
end Legacy.BecknerOnofri.CircleHeat
