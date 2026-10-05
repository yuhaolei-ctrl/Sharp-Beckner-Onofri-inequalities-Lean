module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.CubicFirstShell
public import BecknerOnofri.LocalElevenCore.QuadraticCorrectionCoefficients
public import BecknerOnofri.Kappa

@[expose] public section

/-! Actual cubic first-shell term of the reduced normalized Gibbs equation. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate

open Classical
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticModes

open BecknerOnofri.HighDim.QuadraticModes hiding actual_quartic_coefficients actual_reduced_cubic_coefficient actual_reduced_cubic_diagonal actual_reduced_cubic_diagonal_nonzero amplitude_sum_square assembly_cube_coefficient assembly_fourth_moment assembly_product_coefficient assembly_quadraticCorrection_coefficient assembly_quartic_cumulant assembly_second_moment assembly_third_moment complementGreen_synthesis complementMap_center complementMap_const complementMap_synthesis complementMap_synthesis_zero complementSynthesis cubicTerm_first_coefficient green_complementMap green_synthesis inverseGreen_factor mixedAmplitudeSum off_diagonal_sum quadraticCorrection_coefficient quadraticCorrection_diff quadraticCorrection_double quadraticCorrection_eq_resolvent quadraticCorrection_sum quadraticSource_expansion quadraticSource_value quadratic_schur_identity quartic_slaving_contribution resolvent resolventPair resolventPair_apply resolventPair_synthesis resolvent_coefficient resolvent_synthesis schur_diagonal schur_double_sum schur_off_diagonal shellSquare_first_coefficient shellSquare_mean shellSquare_projection sourcePair sourcePair_diagonal sourcePair_off_diagonal source_norm_moment source_norm_sq synthesis_complex synthesis_mem_complement synthesis_product_coefficient
open BecknerOnofri.HighDim.QuadraticSlaving hiding correction_quadratic_expansion inverseGreen mean_slicePotential nonlinear_error_cubic normalized_error_cubic pow_down quadraticCorrection quadraticTerm_difference_cubic sliceCorrection sliceCorrection_coe_quadratic sliceCorrection_inverse sliceCorrection_quadratic slicePotential slicePotential_linear slicePotential_tendsto
open ContinuousGibbs ContinuousFirstShell QuadraticSlaving

private theorem conj_mul_norm (w : ℂ) : conj w*w = ((‖w‖^2:ℝ):ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

theorem assembly_cube_coefficient {d : ℕ} (z : Coordinates d) (i : Fin d) :
    coefficient (axisFrequency i) ((assembly d z)^3) =
      6*z i*((∑ j : Fin d, ‖z j‖^2 : ℝ):ℂ) - 3*z i*((‖z i‖^2:ℝ):ℂ) := by
  have he : (assembly d z)^3 = assembly d z * shellSquare z := by unfold shellSquare; ring
  rw [he, assembly_product_coefficient]
  have hp (j : Fin d) : z j * coefficient (axisFrequency i-axisFrequency j) (shellSquare z) +
      conj (z j)*coefficient (axisFrequency i+axisFrequency j) (shellSquare z) =
      4*z i*((‖z j‖^2:ℝ):ℂ) +
        (if j=i then 2*z i*((∑ j : Fin d, ‖z j‖^2:ℝ):ℂ) - 3*z i*((‖z i‖^2:ℝ):ℂ) else 0) := by
    by_cases hij : i=j
    · subst j
      rw [sub_self, coefficient_zero, shellSquare_mean, shellSquare_double, if_pos rfl]
      push_cast
      have hn := conj_mul_norm (z i)
      push_cast at hn
      linear_combination z i * hn
    · rw [shellSquare_diff z hij, shellSquare_sum z hij, if_neg (Ne.symm hij), add_zero]
      have hn := conj_mul_norm (z j)
      linear_combination 4*z i * hn
  simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp
  push_cast
  ring

theorem cubicTerm_first_coefficient {d : ℕ} (z : Coordinates d) (i : Fin d) :
    coefficient (axisFrequency i) (cubicTerm (assembly d z)) =
      -(1/2:ℂ) * z i * ((‖z i‖^2:ℝ):ℂ) := by
  rw [cubicTerm_of_mean_zero (mean_assembly z),
    center_eq_self_of_mean_zero (assembly_third_moment z), map_sub, map_smul, map_smul,
    assembly_cube_coefficient, assembly_second_moment]
  have hi : coefficient (axisFrequency i) (assembly d z) = z i :=
    congrFun (coordinates_assembly z) i
  rw [hi]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem assembly_quadraticCorrection_coefficient {d : ℕ} (hd : 11 ≤ d)
    (z : Coordinates d) (i : Fin d) :
    coefficient (axisFrequency i) (assembly d z * (quadraticCorrection hd z).val) =
      ((1/(2*((2:ℝ)^d-1)):ℝ):ℂ) * z i * ((‖z i‖^2:ℝ):ℂ) +
      ((2/((2:ℝ)^((d:ℝ)/2)-1):ℝ):ℂ) * z i *
        (((∑ j : Fin d, ‖z j‖^2)-‖z i‖^2:ℝ):ℂ) := by
  rw [assembly_product_coefficient]
  have hzero : coefficient (0 : Frequency d) (quadraticCorrection hd z).val = 0 := by
    exact (mem_complement_fourier_iff (quadraticCorrection hd z).val).mp
      (quadraticCorrection hd z).property 0 (by simp [ComplementFrequency])
  let a : ℂ := ((1/(2*((2:ℝ)^d-1)):ℝ):ℂ)
  let b : ℂ := ((2/((2:ℝ)^((d:ℝ)/2)-1):ℝ):ℂ)
  have hp (j : Fin d) : z j * coefficient (axisFrequency i-axisFrequency j) (quadraticCorrection hd z).val +
      conj (z j)*coefficient (axisFrequency i+axisFrequency j) (quadraticCorrection hd z).val =
      b*z i*((‖z j‖^2:ℝ):ℂ) + (if j=i then (a-b)*z i*((‖z i‖^2:ℝ):ℂ) else 0) := by
    by_cases hij : i=j
    · subst j
      rw [sub_self, hzero, mul_zero, zero_add, quadraticCorrection_double, if_pos rfl]
      change conj (z i)*(a*z i^2) = _
      linear_combination a*z i*conj_mul_norm (z i)
    · rw [quadraticCorrection_diff hd z hij, quadraticCorrection_sum hd z hij,
        if_neg (Ne.symm hij), add_zero]
      dsimp only [b]
      push_cast
      have hn := conj_mul_norm (z j)
      push_cast at hn
      have hh := congrArg (fun w : ℂ => ((2/((2:ℝ)^((d:ℝ)/2)-1):ℝ):ℂ)*z i*w) hn
      push_cast at hh
      linear_combination hh
  simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp
  dsimp [a,b]
  push_cast
  simp only [one_div, mul_inv_rev]
  ring

/-- The genuine cubic term, including the actual quadratic graph correction, has the source's coefficients. -/
theorem actual_reduced_cubic_coefficient {d : ℕ} (hd : 11 ≤ d)
    (z : Coordinates d) (i : Fin d) :
    coefficient (axisFrequency i)
      (assembly d z * (quadraticCorrection hd z).val + cubicTerm (assembly d z)) =
      ((2*quarticA d : ℝ):ℂ)*z i*((‖z i‖^2:ℝ):ℂ) +
      ((quarticB d : ℝ):ℂ)*z i*(((∑ j : Fin d, ‖z j‖^2)-‖z i‖^2:ℝ):ℂ) := by
  rw [map_add, assembly_quadraticCorrection_coefficient, cubicTerm_first_coefficient]
  unfold quarticA quarticB
  simp only [one_div, mul_inv_rev, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_inv]
  norm_num only [Complex.ofReal_ofNat]
  ring

/-- Along the full symmetric diagonal the reduced equation has cubic coefficient κd. -/
theorem actual_reduced_cubic_diagonal {d : ℕ} (hd : 11 ≤ d) (t : ℂ) (i : Fin d) :
    -coefficient (axisFrequency i)
      (assembly d (fun _ => t) * (quadraticCorrection hd (fun _ => t)).val +
        cubicTerm (assembly d (fun _ => t))) =
      (kappa d : ℂ)*t*((‖t‖^2:ℝ):ℂ) := by
  rw [actual_reduced_cubic_coefficient]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold kappa
  push_cast
  ring

theorem actual_reduced_cubic_diagonal_nonzero {d : ℕ} (hd : 11 ≤ d) (i : Fin d) :
    -coefficient (axisFrequency i)
      (assembly d (fun _ => (1:ℂ)) * (quadraticCorrection hd (fun _ => (1:ℂ))).val +
        cubicTerm (assembly d (fun _ => (1:ℂ)))) ≠ 0 := by
  rw [actual_reduced_cubic_diagonal]
  simp only [norm_one, one_pow, Complex.ofReal_one, mul_one]
  exact Complex.ofReal_ne_zero.mpr (BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd).ne'

#print axioms actual_reduced_cubic_coefficient
#print axioms actual_reduced_cubic_diagonal_nonzero
end BecknerOnofri.HighDim.LocalEleven.QuadraticModes
