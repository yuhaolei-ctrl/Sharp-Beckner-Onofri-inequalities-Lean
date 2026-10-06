module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuadraticCorrectionCoefficients
public import BecknerOnofri.LocalElevenCore.FirstShellProduct

@[expose] public section

/-! Exact Fourier coefficients of the actual analytic graph's quadratic correction. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticModes

open BecknerOnofri.HighDim.QuadraticModes hiding actual_quartic_coefficients amplitude_sum_square assembly_fourth_moment assembly_product_coefficient assembly_quartic_cumulant assembly_second_moment assembly_third_moment complementGreen_synthesis complementMap_center complementMap_const complementMap_synthesis complementMap_synthesis_zero complementSynthesis green_complementMap green_synthesis inverseGreen_factor mixedAmplitudeSum off_diagonal_sum quadraticCorrection_coefficient quadraticCorrection_diff quadraticCorrection_double quadraticCorrection_eq_resolvent quadraticCorrection_sum quadraticSource_expansion quadraticSource_value quadratic_schur_identity quartic_slaving_contribution resolvent resolventPair resolventPair_apply resolventPair_synthesis resolvent_coefficient resolvent_synthesis schur_diagonal schur_double_sum schur_off_diagonal shellSquare_first_coefficient shellSquare_mean shellSquare_projection sourcePair sourcePair_diagonal sourcePair_off_diagonal source_norm_moment source_norm_sq synthesis_complex synthesis_mem_complement synthesis_product_coefficient
open BecknerOnofri.HighDim.QuadraticSlaving hiding correction_quadratic_expansion inverseGreen mean_slicePotential nonlinear_error_cubic normalized_error_cubic pow_down quadraticCorrection quadraticTerm_difference_cubic sliceCorrection sliceCorrection_coe_quadratic sliceCorrection_inverse sliceCorrection_quadratic slicePotential slicePotential_linear slicePotential_tendsto
open ContinuousGibbs ContinuousFirstShell QuadraticSlaving

theorem resolvent_coefficient {d : ℕ} (hd : 11 ≤ d) (f : complement d)
    {k : Frequency d} (hk : ComplementFrequency k) :
    coefficient k (resolvent hd f).val = ((1/(frequencyLength k^d-1):ℝ):ℂ)*coefficient k f.val := by
  have h := congrArg (fun a : realLpComplement d => a.val.val k)
    (continuousComplementInverse_fourier hd (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤2)
      (continuousComplementGreen (by omega) f))
  change coefficient k (resolvent hd f).val =
    (complementInverseMultiplier 1 k : ℂ)*coefficient k (greenContinuous d f.val) at h
  rw [coefficient_green (by omega), if_neg hk.1] at h
  simp only [complementInverseMultiplier, if_pos hk] at h
  rw [h]
  have hEig := complement_eigenvalue_ge_thirtytwo hd hk
  have hEig0 : frequencyLength k^d ≠ 0 := by linarith
  have hEig1 : frequencyLength k^d-1 ≠ 0 := by linarith
  have hs : (1-1/frequencyLength k^d)⁻¹*(1/frequencyLength k^d) = 1/(frequencyLength k^d-1) := by
    field_simp [hEig0, hEig1]
  rw [← mul_assoc, ← Complex.ofReal_mul, hs]

theorem quadraticCorrection_coefficient {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d)
    {k : Frequency d} (hk : ComplementFrequency k) :
    coefficient k (quadraticCorrection hd z).val =
      ((1/(2*(frequencyLength k^d-1)):ℝ):ℂ)*coefficient k (quadraticSource z).val := by
  rw [quadraticCorrection_eq_resolvent]
  change coefficient k ((1/2:ℝ) • (resolvent hd (quadraticSource z)).val) = _
  rw [map_smul, resolvent_coefficient hd _ hk]
  simp only [Complex.real_smul, one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv]
  norm_num only [Complex.ofReal_ofNat]
  ring

theorem quadraticCorrection_double {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) (i : Fin d) :
    coefficient (axisFrequency i+axisFrequency i) (quadraticCorrection hd z).val =
      ((1/(2*((2:ℝ)^d-1)):ℝ):ℂ) * z i^2 := by
  rw [quadraticCorrection_coefficient hd z (complement_double i), eigenvalue_double, quadraticSource_double]

theorem quadraticCorrection_sum {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d)
    {i j : Fin d} (hij : i ≠ j) :
    coefficient (axisFrequency i+axisFrequency j) (quadraticCorrection hd z).val =
      ((1/((2:ℝ)^((d:ℝ)/2)-1):ℝ):ℂ) * z i*z j := by
  rw [quadraticCorrection_coefficient hd z (complement_sum hij), eigenvalue_sum hij, quadraticSource_sum z hij]
  simp only [one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv]
  norm_num only [Complex.ofReal_ofNat]
  ring

theorem quadraticCorrection_diff {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d)
    {i j : Fin d} (hij : i ≠ j) :
    coefficient (axisFrequency i-axisFrequency j) (quadraticCorrection hd z).val =
      ((1/((2:ℝ)^((d:ℝ)/2)-1):ℝ):ℂ) * z i*conj (z j) := by
  rw [quadraticCorrection_coefficient hd z (complement_diff hij), eigenvalue_diff hij, quadraticSource_diff z hij]
  simp only [one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv]
  norm_num only [Complex.ofReal_ofNat]
  ring

#print axioms quadraticCorrection_diff
end BecknerOnofri.HighDim.LocalEleven.QuadraticModes
