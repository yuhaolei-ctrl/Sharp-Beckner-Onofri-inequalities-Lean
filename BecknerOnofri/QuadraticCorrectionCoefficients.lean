import BecknerOnofri.FirstShellProduct

/-! Exact Fourier coefficients of the actual analytic graph's quadratic correction. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.QuadraticModes
open ContinuousGibbs ContinuousFirstShell QuadraticSlaving

theorem resolvent_coefficient {d : ℕ} (hd : 12 ≤ d) (f : complement d)
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
  have hEig := complement_eigenvalue_ge_sixtyfour hd hk
  have hEig0 : frequencyLength k^d ≠ 0 := by linarith
  have hEig1 : frequencyLength k^d-1 ≠ 0 := by linarith
  have hs : (1-1/frequencyLength k^d)⁻¹*(1/frequencyLength k^d) = 1/(frequencyLength k^d-1) := by
    field_simp [hEig0, hEig1]
  rw [← mul_assoc, ← Complex.ofReal_mul, hs]

theorem quadraticCorrection_coefficient {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d)
    {k : Frequency d} (hk : ComplementFrequency k) :
    coefficient k (quadraticCorrection hd z).val =
      ((1/(2*(frequencyLength k^d-1)):ℝ):ℂ)*coefficient k (quadraticSource z).val := by
  rw [quadraticCorrection_eq_resolvent]
  change coefficient k ((1/2:ℝ) • (resolvent hd (quadraticSource z)).val) = _
  rw [map_smul, resolvent_coefficient hd _ hk]
  simp only [Complex.real_smul, one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv]
  norm_num only [Complex.ofReal_ofNat]
  ring

theorem quadraticCorrection_double {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) (i : Fin d) :
    coefficient (axisFrequency i+axisFrequency i) (quadraticCorrection hd z).val =
      ((1/(2*((2:ℝ)^d-1)):ℝ):ℂ) * z i^2 := by
  rw [quadraticCorrection_coefficient hd z (complement_double i), eigenvalue_double, quadraticSource_double]

theorem quadraticCorrection_sum {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d)
    {i j : Fin d} (hij : i ≠ j) :
    coefficient (axisFrequency i+axisFrequency j) (quadraticCorrection hd z).val =
      ((1/((2:ℝ)^((d:ℝ)/2)-1):ℝ):ℂ) * z i*z j := by
  rw [quadraticCorrection_coefficient hd z (complement_sum hij), eigenvalue_sum hij, quadraticSource_sum z hij]
  simp only [one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv]
  norm_num only [Complex.ofReal_ofNat]
  ring

theorem quadraticCorrection_diff {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d)
    {i j : Fin d} (hij : i ≠ j) :
    coefficient (axisFrequency i-axisFrequency j) (quadraticCorrection hd z).val =
      ((1/((2:ℝ)^((d:ℝ)/2)-1):ℝ):ℂ) * z i*conj (z j) := by
  rw [quadraticCorrection_coefficient hd z (complement_diff hij), eigenvalue_diff hij, quadraticSource_diff z hij]
  simp only [one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv]
  norm_num only [Complex.ofReal_ofNat]
  ring

#print axioms quadraticCorrection_diff
end BecknerOnofri.HighDim.QuadraticModes
