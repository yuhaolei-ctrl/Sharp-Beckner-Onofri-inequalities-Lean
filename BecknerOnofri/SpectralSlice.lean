module

public import Legacy.BecknerOnofri.ThetaIntegrability
public import Legacy.TorusEndpoint.GreenMellinMultiplier
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SumIntegralComparisons

@[expose] public section

/-! The actual one-dimensional spectral slice, with its Mellin representation. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace BecknerOnofri.SpectralSlice

open Legacy.BecknerOnofri.ThetaDomination

def term (p a : ℝ) (n : ℤ) : ℝ := (1 + ((n : ℝ) / a) ^ 2) ^ (-p / 2)
def phi (p a : ℝ) : ℝ := a⁻¹ * ∑' n : ℤ, term p a n

theorem term_nonneg (p a : ℝ) (n : ℤ) : 0 ≤ term p a n := by
  exact Real.rpow_nonneg (by positivity) _

theorem summable_term {p a : ℝ} (hp : 2 ≤ p) (ha : 1 ≤ a) :
    Summable (term p a) := by
  have ha0 : 0 < a := by linarith
  apply (Legacy.TorusEndpoint.GreenMultiplierSummability.summable_int_one_add_sq_inv.mul_left
    (a ^ 2)).of_nonneg_of_le (term_nonneg p a)
  intro n
  have hc : 0 < 1 + ((n : ℝ) / a) ^ 2 := by positivity
  calc
    term p a n ≤ (1 + ((n : ℝ) / a) ^ 2) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ((n : ℝ) / a)])
        (by linarith)
    _ = a ^ 2 / (a ^ 2 + (n : ℝ) ^ 2) := by
      rw [Real.rpow_neg_one]
      field_simp
      <;> ring
    _ ≤ a ^ 2 * (1 + (n : ℝ) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left (sq_nonneg a) (by positivity)
      nlinarith

theorem phi_antitone_exponent {p q a : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) (ha : 1 ≤ a) :
    phi q a ≤ phi p a := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith))
  apply (summable_term (hp.trans hpq) ha).tsum_le_tsum _ (summable_term hp ha)
  intro n
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ((n : ℝ) / a)])
    (by linarith)

theorem theta_jacobi {t : ℝ} (ht : 0 < t) :
    realTheta t = Real.sqrt (Real.pi / t) * realTheta (Real.pi ^ 2 / t) := by
  have h := Real.tsum_exp_neg_mul_int_sq (div_pos ht Real.pi_pos)
  have hl : -Real.pi * (t / Real.pi) = -t := by field_simp
  have hr : -Real.pi / (t / Real.pi) = -(Real.pi ^ 2 / t) := by field_simp
  have hf : (1 : ℝ) / (t / Real.pi) ^ (1 / 2 : ℝ) = Real.sqrt (Real.pi / t) := by
    rw [← Real.sqrt_eq_rpow, one_div, ← Real.sqrt_inv, inv_div]
  rw [hl, hr, hf] at h
  exact h

def mellinTerm (p a : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  t ^ (p / 2 - 1) * Real.exp (-( (1 + ((n : ℝ) / a) ^ 2) * t))

theorem mellinTerm_integrable {p a : ℝ} (hp : 0 < p) (n : ℤ) :
    IntegrableOn (mellinTerm p a n) (Ioi 0) :=
  Legacy.TorusEndpoint.GreenMellinMultiplier.gamma_integrand_integrable
    (by positivity) (by positivity)

theorem integral_mellinTerm {p a : ℝ} (hp : 0 < p) (n : ℤ) :
    (∫ t in Ioi 0, mellinTerm p a n t) = Real.Gamma (p / 2) * term p a n := by
  unfold mellinTerm
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) (by positivity)]
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  unfold term
  rw [show -(p / 2) = -p / 2 by ring]
  exact mul_comm _ _

theorem mellinTerm_nonneg {p a t : ℝ} (ht : 0 < t) (n : ℤ) :
    0 ≤ mellinTerm p a n t := by
  unfold mellinTerm
  positivity

theorem integral_norm_mellinTerm {p a : ℝ} (hp : 0 < p) (n : ℤ) :
    (∫ t in Ioi 0, ‖mellinTerm p a n t‖) = Real.Gamma (p / 2) * term p a n := by
  rw [← integral_mellinTerm hp n]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact Real.norm_of_nonneg (mellinTerm_nonneg ht n)

def kernel (p a t : ℝ) : ℝ :=
  t ^ (p / 2 - 1) * Real.exp (-t) * realTheta (t / a ^ 2)

theorem mellinTerm_sum (p a t : ℝ) : (∑' n : ℤ, mellinTerm p a n t) = kernel p a t := by
  have he (n : ℤ) : mellinTerm p a n t =
      (t ^ (p / 2 - 1) * Real.exp (-t)) * Real.exp (-(t / a ^ 2) * (n : ℝ) ^ 2) := by
    unfold mellinTerm
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [he, tsum_mul_left]
  rfl

theorem kernel_integral {p a : ℝ} (hp : 2 ≤ p) (ha : 1 ≤ a) :
    (∫ t in Ioi 0, kernel p a t) = Real.Gamma (p / 2) * ∑' n : ℤ, term p a n := by
  have hp0 : 0 < p := by linarith
  have hs : Summable (fun n : ℤ => ∫ t in Ioi 0, ‖mellinTerm p a n t‖) := by
    simp_rw [integral_norm_mellinTerm hp0]
    exact (summable_term hp ha).mul_left _
  rw [← show (fun t => ∑' n : ℤ, mellinTerm p a n t) = kernel p a from
    funext (mellinTerm_sum p a)]
  rw [← integral_tsum_of_summable_integral_norm (mellinTerm_integrable hp0) hs]
  simp_rw [integral_mellinTerm hp0, tsum_mul_left]

theorem kernel_integrable {p a : ℝ} (hp : 2 ≤ p) (ha : 1 ≤ a) :
    IntegrableOn (kernel p a) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [kernel_integral hp ha]
  apply (mul_pos (Real.Gamma_pos_of_pos (by linarith : 0 < p / 2)) ?_).ne'
  have h := (summable_term hp ha).le_tsum (0 : ℤ) (fun n _ => term_nonneg p a n)
  have hzero : term p a 0 = 1 := by simp [term]
  rw [hzero] at h
  linarith

theorem normalized_kernel_jacobi {p a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    a⁻¹ * kernel p a t =
      (t ^ (p / 2 - 1) * Real.exp (-t) * Real.sqrt (Real.pi / t)) *
        realTheta (Real.pi ^ 2 * a ^ 2 / t) := by
  have hs : Real.pi / (t / a ^ 2) = a ^ 2 * (Real.pi / t) := by field_simp
  have htarg : Real.pi ^ 2 / (t / a ^ 2) = Real.pi ^ 2 * a ^ 2 / t := by field_simp
  rw [kernel, theta_jacobi (div_pos ht (sq_pos_of_pos ha)), hs, htarg,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  field_simp

theorem phi_antitone_radius {p a b : ℝ} (hp : 2 ≤ p) (ha : 1 ≤ a) (hab : a ≤ b) :
    phi p b ≤ phi p a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hpoint : (fun t => b⁻¹ * kernel p b t) ≤ᵐ[volume.restrict (Ioi 0)]
      (fun t => a⁻¹ * kernel p a t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [normalized_kernel_jacobi hb0 ht, normalized_kernel_jacobi ha0 ht]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply realTheta_antitone (by positivity)
    apply div_le_div_of_nonneg_right _ ht.le
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg Real.pi)
  have h := integral_mono_ae ((kernel_integrable hp (ha.trans hab)).const_mul b⁻¹)
    ((kernel_integrable hp ha).const_mul a⁻¹) hpoint
  rw [integral_const_mul, integral_const_mul, kernel_integral hp (ha.trans hab),
    kernel_integral hp ha] at h
  have h' : Real.Gamma (p / 2) * phi p b ≤ Real.Gamma (p / 2) * phi p a := by
    dsimp [phi]
    nlinarith [h]
  exact (mul_le_mul_iff_right₀ (Real.Gamma_pos_of_pos (by linarith : 0 < p / 2))).mp h'

theorem term_rescale {p a : ℝ} (ha : 0 < a) (n : ℤ) :
    term p a n = a ^ p * (a ^ 2 + (n : ℝ) ^ 2) ^ (-p / 2) := by
  have he : 1 + ((n : ℝ) / a) ^ 2 = (a ^ 2 + (n : ℝ) ^ 2) / a ^ 2 := by
    field_simp
    <;> ring
  have hpow : (a ^ 2) ^ (-p / 2) = a ^ (-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    ring
  rw [term, he, Real.div_rpow (by positivity) (sq_nonneg a), hpow,
    Real.rpow_neg ha.le, div_inv_eq_mul, mul_comm]

theorem phi_rescale {p a : ℝ} (ha : 0 < a) :
    phi p a = a ^ (p - 1) * ∑' n : ℤ, (a ^ 2 + (n : ℝ) ^ 2) ^ (-p / 2) := by
  simp_rw [phi, term_rescale ha, tsum_mul_left]
  rw [Real.rpow_sub ha, Real.rpow_one]
  ring

theorem summable_radial {p a : ℝ} (hp : 2 ≤ p) (ha : 1 ≤ a) :
    Summable (fun n : ℤ => (a ^ 2 + (n : ℝ) ^ 2) ^ (-p / 2)) := by
  have ha0 : 0 < a := by linarith
  have hs := summable_term hp ha
  change Summable (fun n : ℤ => term p a n) at hs
  simp_rw [term_rescale ha0] at hs
  exact (summable_mul_left_iff (Real.rpow_pos_of_pos ha0 p).ne').mp hs

#print axioms phi_antitone_radius

end BecknerOnofri.SpectralSlice
