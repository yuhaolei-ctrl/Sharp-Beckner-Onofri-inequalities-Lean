import Legacy.BecknerOnofri.CircleEqualitySeries
import Legacy.BecknerOnofri.EndpointPotential

/-! Explicit conformal potentials and Poisson densities, with their genuine Fourier series. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators ComplexConjugate
namespace Legacy.BecknerOnofri.CircleEquality
set_option maxHeartbeats 800000

def logarithmicCoefficient (z : ℂ) (n : ℕ) : ℂ := z ^ n / (n : ℂ)
def geometricCoefficient (z : ℂ) (n : ℕ) : ℂ := z ^ n

def logPotential (z : ℂ) (x : Torus 1) : ℝ := -2 * Real.log ‖1 - z * character x‖
def poisson (z : ℂ) (x : Torus 1) : ℝ := (1 - ‖z‖ ^ 2) / ‖1 - z * character x‖ ^ 2

theorem geometric_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => ‖geometricCoefficient z n‖) := by
  simpa only [geometricCoefficient, norm_pow] using summable_geometric_of_lt_one (norm_nonneg z) hz

theorem logarithmic_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => ‖logarithmicCoefficient z n‖) := by
  apply (geometric_summable hz).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  by_cases hn : n = 0
  · simp [hn, logarithmicCoefficient, geometricCoefficient]
  · simp only [logarithmicCoefficient, geometricCoefficient, norm_div, norm_pow, Complex.norm_natCast]
    exact div_le_self (pow_nonneg (norm_nonneg z) _)
      (by exact_mod_cast (show 1 ≤ n by omega))

theorem norm_parameter_character {z : ℂ} (x : Torus 1) : ‖z * character x‖ = ‖z‖ := by
  rw [norm_mul, character_norm, mul_one]

theorem denominator_ne_zero {z : ℂ} (hz : ‖z‖ < 1) (x : Torus 1) : 1 - z * character x ≠ 0 := by
  intro h
  have he : z * character x = 1 := (sub_eq_zero.mp h).symm
  have hn := congrArg norm he
  rw [norm_parameter_character, norm_one] at hn
  linarith

theorem normSq_parameter_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖z‖ ^ 2 < 1 := by
  nlinarith [norm_nonneg z]

theorem poisson_pos {z : ℂ} (hz : ‖z‖ < 1) (x : Torus 1) : 0 < poisson z x :=
  div_pos (sub_pos.mpr (normSq_parameter_lt_one hz)) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
    (denominator_ne_zero hz x)))

theorem logarithmic_series {z : ℂ} (hz : ‖z‖ < 1) (x : Torus 1) :
    series (logarithmicCoefficient z) x = (logPotential z x : ℂ) := by
  rw [series_eq _ (logarithmic_summable hz)]
  have hs : (∑' n : ℕ, logarithmicCoefficient z n * character x ^ n) =
      -Complex.log (1 - z * character x) := by
    convert! (Complex.hasSum_taylorSeries_neg_log
      (z := z * character x) (by simpa only [norm_parameter_character] using hz)).tsum_eq using 1
    apply tsum_congr
    intro n
    simp only [logarithmicCoefficient, mul_pow]
    ring
  rw [hs]
  simp only [logarithmicCoefficient, pow_zero, Nat.cast_zero, div_zero, map_zero, sub_zero]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.neg_re, Complex.conj_re, Complex.ofReal_re, Complex.log_re]
    unfold logPotential
    ring
  · simp

theorem inverse_real_identity (q : ℂ) (hq : 1 - q ≠ 0) :
    (1 - q)⁻¹ + conj ((1 - q)⁻¹) - 1 =
      (((1 - ‖q‖ ^ 2) / ‖1 - q‖ ^ 2 : ℝ) : ℂ) := by
  have hd : Complex.normSq (1 - q) ≠ 0 := (Complex.normSq_pos.mpr hq).ne'
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.inv_re, ← Complex.normSq_eq_norm_sq]
    field_simp
    simp only [Complex.normSq_sub, Complex.normSq_one, one_mul, Complex.conj_re]
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.conj_im, Complex.one_im,
      Complex.ofReal_im, add_neg_cancel, sub_zero]

theorem geometric_series {z : ℂ} (hz : ‖z‖ < 1) (x : Torus 1) :
    series (geometricCoefficient z) x = (poisson z x : ℂ) := by
  rw [series_eq _ (geometric_summable hz)]
  have hs : (∑' n : ℕ, geometricCoefficient z n * character x ^ n) =
      (1 - z * character x)⁻¹ := by
    simpa only [geometricCoefficient, ← mul_pow] using
      (hasSum_geometric_of_norm_lt_one
        (by simpa only [norm_parameter_character] using hz : ‖z * character x‖ < 1)).tsum_eq
  rw [hs]
  simp only [geometricCoefficient, pow_zero, map_one]
  rw [inverse_real_identity _ (denominator_ne_zero hz x), norm_parameter_character]
  rfl

theorem logPotential_continuous {z : ℂ} (hz : ‖z‖ < 1) : Continuous (logPotential z) := by
  have h := Complex.continuous_re.comp (series_continuous _ (logarithmic_summable hz))
  simpa only [Function.comp_def, logarithmic_series hz, Complex.ofReal_re] using h

theorem poisson_continuous {z : ℂ} (hz : ‖z‖ < 1) : Continuous (poisson z) := by
  have h := Complex.continuous_re.comp (series_continuous _ (geometric_summable hz))
  simpa only [Function.comp_def, geometric_series hz, Complex.ofReal_re] using h

theorem logPotential_fourier {z : ℂ} (hz : ‖z‖ < 1) (k : Frequency 1) :
    densityFourier (logPotential z) k = coefficient (logarithmicCoefficient z) k := by
  have h := series_fourier _ (logarithmic_summable hz) k
  rw [show series (logarithmicCoefficient z) = (fun x => (logPotential z x : ℂ)) from
    funext (logarithmic_series hz)] at h
  exact h

theorem poisson_fourier {z : ℂ} (hz : ‖z‖ < 1) (k : Frequency 1) :
    densityFourier (poisson z) k = coefficient (geometricCoefficient z) k := by
  have h := series_fourier _ (geometric_summable hz) k
  rw [show series (geometricCoefficient z) = (fun x => (poisson z x : ℂ)) from
    funext (geometric_series hz)] at h
  exact h

theorem logPotential_mean {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ x, logPotential z x ∂torusMeasure 1) = 0 := by
  have h := series_integral _ (logarithmic_summable hz)
  simp_rw [logarithmic_series hz] at h
  rw [integral_complex_ofReal] at h
  simpa [logarithmicCoefficient] using congrArg Complex.re h

theorem poisson_mass {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ x, poisson z x ∂torusMeasure 1) = 1 := by
  have h := series_integral _ (geometric_summable hz)
  simp_rw [geometric_series hz] at h
  rw [integral_complex_ofReal] at h
  simpa [geometricCoefficient] using congrArg Complex.re h

def poissonDensity (z : ℂ) (hz : ‖z‖ < 1) : ProbabilityDensity 1 where
  value := poisson z
  nonneg := ae_of_all _ (fun x => (poisson_pos hz x).le)
  integrable := (poisson_continuous hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  mass := poisson_mass hz

theorem poisson_finiteEntropy {z : ℂ} (hz : ‖z‖ < 1) : (poissonDensity z hz).FiniteEntropy :=
  (Real.continuous_mul_log.comp (poisson_continuous hz)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem exp_logPotential {z : ℂ} (hz : ‖z‖ < 1) (x : Torus 1) :
    Real.exp (logPotential z x) = poisson z x / (1 - ‖z‖ ^ 2) := by
  have hn : 0 < ‖1 - z * character x‖ := norm_pos_iff.mpr (denominator_ne_zero hz x)
  have hd : 1 - ‖z‖ ^ 2 ≠ 0 := (sub_pos.mpr (normSq_parameter_lt_one hz)).ne'
  rw [logPotential, show (-2 : ℝ) * Real.log ‖1 - z * character x‖ =
    -(2 * Real.log ‖1 - z * character x‖) by ring, Real.exp_neg,
    show Real.exp (2 * Real.log ‖1 - z * character x‖) = ‖1 - z * character x‖ ^ 2 by
      rw [show (2 : ℝ) * Real.log ‖1 - z * character x‖ =
        Real.log ‖1 - z * character x‖ + Real.log ‖1 - z * character x‖ by ring,
        Real.exp_add, Real.exp_log hn, pow_two]]
  unfold poisson
  field_simp

theorem logPotential_partition {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ x, Real.exp (logPotential z x) ∂torusMeasure 1) = (1 - ‖z‖ ^ 2)⁻¹ := by
  simp_rw [exp_logPotential hz]
  rw [integral_div, poisson_mass hz, one_div]

#print axioms logarithmic_series
#print axioms geometric_series
#print axioms poisson_fourier
#print axioms logPotential_partition
end Legacy.BecknerOnofri.CircleEquality
