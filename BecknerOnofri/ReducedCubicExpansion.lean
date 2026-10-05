import BecknerOnofri.CubicFirstShell
import BecknerOnofri.SlavedMoments

/-! Fourth-order control of the actual reduced first-shell equation on the critical slice. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.ReducedCubicExpansion
open ContinuousGibbs ContinuousFirstShell QuadraticModes QuadraticSlaving SlavedMoments ReducedEquation

theorem coordinates_const {d : ℕ} (c : ℝ) :
    coordinates d (ContinuousMap.const (Torus d) c) = 0 := by
  funext i
  simp [coordinates_apply, coefficient_const, axisFrequency_ne_zero]

theorem coordinates_center {d : ℕ} (f : Space d) : coordinates d (center d f) = coordinates d f := by
  have h : center d f = f - ContinuousMap.const (Torus d) (mean d f) := rfl
  rw [h, map_sub, coordinates_const, sub_zero]

theorem coordinates_shellSquare {d : ℕ} (z : Coordinates d) : coordinates d (V d z^2) = 0 := by
  funext i
  exact shellSquare_first_coefficient z i

theorem coordinates_U {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) : coordinates d (U hd z) = z :=
  coordinates_reconstruction _

theorem U_square_difference {d : ℕ} (hd : 12 ≤ d) :
    (fun z => U hd z^2 - V d z^2) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  have h : (fun z => W hd z * (U hd z + V d z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
    convert! (W_order_two hd).mul ((U_order hd).add V_order) using 1 <;> (ext z; ring)
  apply h.congr_left
  intro z
  rw [U_eq]
  ring

theorem U_cube_difference {d : ℕ} (hd : 12 ≤ d) :
    (fun z => U hd z^3 - V d z^3) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) := by
  have hUV : (fun z => U hd z * V d z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^2) := by
    convert! (U_order hd).mul V_order using 1 <;> (ext z; ring)
  have h : (fun z => W hd z * (U hd z^2 + U hd z*V d z + V d z^2))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) := by
    convert! (W_order_two hd).mul ((((U_order hd).pow 2).add hUV).add (V_order.pow 2))
      using 1 <;> (ext z; ring)
  apply h.congr_left
  intro z
  rw [U_eq]
  ring

theorem cubicTerm_difference {d : ℕ} (hd : 12 ≤ d) :
    (fun z => cubicTerm (U hd z) - cubicTerm (V d z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) := by
  have h1 := (((center d).isBigO_comp _ _).trans (U_cube_difference hd)).const_smul_left (1/6:ℝ)
  have h2 : (fun z => mean d (U hd z^2) • W hd z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) := by
    convert! (((mean d).isBigO_comp _ _).trans ((U_order hd).pow 2)).smul (W_order_two hd)
      using 1 <;> (ext z; simp [smul_eq_mul]; ring)
  have h3 : (fun z => mean d (U hd z^2 - V d z^2) • V d z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) := by
    convert! (((mean d).isBigO_comp _ _).trans (U_square_difference hd)).smul V_order
      using 1 <;> (ext z; simp [smul_eq_mul]; ring)
  apply (h1.sub ((h2.add h3).const_smul_left (1/2:ℝ))).congr_left
  intro z
  dsimp only [Pi.smul_apply]
  rw [cubicTerm_of_mean_zero (mean_slicePotential hd z), cubicTerm_of_mean_zero (mean_assembly z),
    map_sub, map_sub]
  ext x
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have hU := congrArg (fun f : Space d => f x) (U_eq hd z)
  change U hd z x = V d z x + W hd z x at hU
  rw [hU]
  ring

theorem coordinates_quadraticTerm_difference {d : ℕ} (hd : 12 ≤ d) :
    (fun z => coordinates d (quadraticTerm (U hd z) - V d z * W hd z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) := by
  have h := (((coordinates d).isBigO_comp _ _).trans ((W_order_two hd).pow 2)).const_smul_left (1/2:ℝ)
  simp only [← pow_mul, show 2*2=4 from rfl] at h
  apply h.congr_left
  intro z
  rw [map_sub, quadraticTerm_of_mean_zero (mean_slicePotential hd z), map_smul, coordinates_center]
  have he : U hd z^2 = V d z^2 + (2:ℝ) • (V d z * W hd z) + W hd z^2 := by
    rw [U_eq]
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [he, map_add, map_add, map_smul, coordinates_shellSquare, zero_add]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Complex.real_smul]
  push_cast
  ring

theorem quadraticCorrection_product_error {d : ℕ} (hd : 12 ≤ d) :
    (fun z => V d z * (W hd z - (quadraticCorrection hd z : Space d)))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) := by
  have hw : (fun z => W hd z - (quadraticCorrection hd z : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) :=
    ((complement d).subtypeL.isBigO_comp _ _).trans (correction_quadratic_expansion hd)
  convert! V_order.mul hw using 1 <;> (ext z; ring)

def cubicModel {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) : Coordinates d :=
  -coordinates d (V d z * (quadraticCorrection hd z : Space d) + cubicTerm (V d z))

theorem cubicModel_apply {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) (i : Fin d) :
    cubicModel hd z i = -(((2*quarticA d:ℝ):ℂ)*z i*((‖z i‖^2:ℝ):ℂ) +
      ((quarticB d:ℝ):ℂ)*z i*(((∑ j : Fin d, ‖z j‖^2)-‖z i‖^2:ℝ):ℂ)) := by
  exact congrArg Neg.neg (actual_reduced_cubic_coefficient hd z i)

/-- Actual reduced equation on τ=1, with its exact cubic polynomial and C-coordinate O4 error. -/
theorem reduced_cubic_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun z => reduced hd (1,z) - cubicModel hd z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) := by
  have hN : (fun z => normalized (U hd z) - cubicPolynomial (U hd z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) := by
    exact ((normalized_cubic_remainder d).comp_tendsto (slicePotential_tendsto hd)).trans
      ((U_order hd).norm_left.pow 4)
  have hN' := ((coordinates d).isBigO_comp _ _).trans hN
  have hQ := coordinates_quadraticTerm_difference hd
  have hC := ((coordinates d).isBigO_comp _ _).trans (cubicTerm_difference hd)
  have hW := ((coordinates d).isBigO_comp _ _).trans (quadraticCorrection_product_error hd)
  apply (((hN'.add hQ).add hC).add hW).neg_left.congr_left
  intro z
  simp only [map_sub, map_add, mul_sub, cubicModel, cubicPolynomial, quadraticPolynomial,
    coordinates_one, coordinates_center, zero_add, coordinates_U]
  change -(coordinates d (normalized (U hd z)) - (z + coordinates d (quadraticTerm (U hd z)) +
      coordinates d (cubicTerm (U hd z))) +
    (coordinates d (quadraticTerm (U hd z)) - coordinates d (V d z * W hd z)) +
    (coordinates d (cubicTerm (U hd z)) - coordinates d (cubicTerm (V d z))) +
    (coordinates d (V d z * W hd z) - coordinates d (V d z * (quadraticCorrection hd z : Space d)))) = _
  unfold reduced
  simp only [one_smul]
  change _ = z - coordinates d (normalized (U hd z)) -
    -(coordinates d (V d z * (quadraticCorrection hd z : Space d)) + coordinates d (cubicTerm (V d z)))
  abel

/-- Real symmetric diagonal in the full complex first shell. -/
def realDiagonal (d : ℕ) : ℝ →L[ℝ] Coordinates d :=
  ContinuousLinearMap.pi (fun _ => Complex.ofRealCLM)

@[simp] theorem realDiagonal_apply (d : ℕ) (t : ℝ) (i : Fin d) : realDiagonal d t i = (t:ℂ) := rfl

theorem cubicModel_diagonal {d : ℕ} (hd : 12 ≤ d) (t : ℝ) (i : Fin d) :
    cubicModel hd (realDiagonal d t) i = ((kappa d*t^3:ℝ):ℂ) := by
  have h := actual_reduced_cubic_diagonal hd (t:ℂ) i
  change cubicModel hd (realDiagonal d t) i = _ at h
  rw [h]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  push_cast
  ring

/-- The actual scalar diagonal reduced equation has nonzero cubic coefficient κd. -/
theorem reduced_diagonal_cubic_expansion {d : ℕ} (hd : 12 ≤ d) (i : Fin d) :
    (fun t : ℝ => (reduced hd (1, realDiagonal d t) i).re - kappa d*t^3)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^4) := by
  have ht : Tendsto (realDiagonal d) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (realDiagonal d).continuous.continuousAt.tendsto (x := (0:ℝ))
  have h := (reduced_cubic_expansion hd).comp_tendsto ht
  have hnorm := ((realDiagonal d).isBigO_id (𝓝 0)).norm_left.norm_right.pow 4
  have h' := h.trans hnorm
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj i)
  apply (((ev).isBigO_comp _ _).trans h').congr_left
  intro t
  change (reduced hd (1, realDiagonal d t) i - cubicModel hd (realDiagonal d t) i).re = _
  rw [cubicModel_diagonal, Complex.sub_re, Complex.ofReal_re]

#print axioms reduced_cubic_expansion
#print axioms reduced_diagonal_cubic_expansion
end BecknerOnofri.HighDim.ReducedCubicExpansion
