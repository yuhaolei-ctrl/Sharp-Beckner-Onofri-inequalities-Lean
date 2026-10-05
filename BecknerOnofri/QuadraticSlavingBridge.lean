module

public import BecknerOnofri.QuadraticSchur
public import BecknerOnofri.QuadraticSlaving

@[expose] public section

/-! Identification of the actual analytic implicit-map quadratic term with its
finite Fourier resolvent and Schur coefficient. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace BecknerOnofri.HighDim.QuadraticModes
open ContinuousGibbs ContinuousFirstShell QuadraticSlaving

theorem green_complementMap {d : ℕ} (hd : 0 < d) (f : Space d) :
    complementMap d (greenContinuous d f) = continuousComplementGreen hd (complementMap d f) := by
  apply Subtype.ext
  apply coefficient_ext
  intro k
  simp only [complementMap_coefficient, continuousComplementGreen_coe, coefficient_green hd]
  by_cases hk : ComplementFrequency k <;> simp only [hk, if_true, if_false, mul_zero]

theorem complementMap_const {d : ℕ} (c : ℝ) :
    complementMap d (ContinuousMap.const (Torus d) c) = 0 := by
  apply Subtype.ext
  simp [complementMap_coe, complementProjection_apply, meanProjection_apply]

theorem complementMap_center {d : ℕ} (f : Space d) :
    complementMap d (center d f) = complementMap d f := by
  have h : center d f = f - ContinuousMap.const (Torus d) (mean d f) := by
    ext x
    rfl
  rw [h, map_sub, complementMap_const, sub_zero]

theorem inverseGreen_factor {d : ℕ} (hd : 12 ≤ d) (f : Space d) :
    inverseGreen hd f = resolvent hd (complementMap d f) := by
  change (continuousComplementContinuousLinearEquiv hd _ _).symm
      (complementMap d (greenContinuous d f)) = _
  rw [green_complementMap (by omega)]
  rfl

/-- The quadratic Taylor term of the actual implicit correction is exactly the source's slaved mode. -/
theorem quadraticCorrection_eq_resolvent {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) :
    quadraticCorrection hd z = (1/2:ℝ) • resolvent hd (quadraticSource z) := by
  unfold quadraticCorrection
  rw [quadraticTerm_of_mean_zero (mean_assembly z), map_smul, inverseGreen_factor,
    complementMap_center]
  rfl

/-- The actual slaving contribution to the quartic reduced functional. -/
theorem quartic_slaving_contribution {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) :
    (1/8:ℝ) * pairing (quadraticSource z).val (resolvent hd (quadraticSource z)).val =
      (1/(4*((2:ℝ)^d-1))) * (∑ i : Fin d, ‖z i‖^4) +
      (2/((2:ℝ)^((d:ℝ)/2)-1)) * mixedAmplitudeSum z := by
  rw [quadratic_schur_identity]
  simp only [one_div, mul_inv_rev]
  ring

#print axioms quadraticCorrection_eq_resolvent
#print axioms quartic_slaving_contribution
end BecknerOnofri.HighDim.QuadraticModes
