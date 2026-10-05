module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.SlavedMoments
public import BecknerOnofri.LocalElevenCore.ComplexFirstShellMoments
public import BecknerOnofri.ContinuousLogPartitionTaylor

@[expose] public section

/-! Actual moment expansions on the genuine implicit complementary graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SlavedMoments

open BecknerOnofri.HighDim.SlavedMoments hiding U U_eq U_fourth_error U_order U_second U_third_error V VW_mean V_order W W_mean W_order_one W_order_two mean_mul_assembly
open BecknerOnofri.HighDim.QuadraticModes hiding actual_quartic_coefficients amplitude_sum_square assembly_fourth_moment assembly_quartic_cumulant assembly_second_moment assembly_third_moment complementGreen_synthesis complementMap_center complementMap_const complementMap_synthesis complementMap_synthesis_zero complementSynthesis green_complementMap green_synthesis inverseGreen_factor mixedAmplitudeSum off_diagonal_sum quadraticCorrection_eq_resolvent quadraticSource_expansion quadraticSource_value quadratic_schur_identity quartic_slaving_contribution resolvent resolventPair resolventPair_apply resolventPair_synthesis resolvent_synthesis schur_diagonal schur_double_sum schur_off_diagonal shellSquare_first_coefficient shellSquare_mean shellSquare_projection sourcePair sourcePair_diagonal sourcePair_off_diagonal source_norm_moment source_norm_sq synthesis_mem_complement
open BecknerOnofri.HighDim.QuadraticSlaving hiding correction_quadratic_expansion inverseGreen mean_slicePotential nonlinear_error_cubic normalized_error_cubic pow_down quadraticCorrection quadraticTerm_difference_cubic sliceCorrection sliceCorrection_coe_quadratic sliceCorrection_inverse sliceCorrection_quadratic slicePotential slicePotential_linear slicePotential_tendsto
open ContinuousGibbs ContinuousFirstShell QuadraticModes QuadraticSlaving

/-- First-shell and complementary functions are exactly Haar-orthogonal. -/
theorem mean_mul_assembly {d : ℕ} (w : complement d) (z : Coordinates d) :
    mean d (w.val * assembly d z) = 0 := by
  change pairing w.val (assembly d z) = 0
  rw [assembly_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [pairing_synthesis, (mem_complement_iff w.val).mp w.property |>.2 i]
  simp

abbrev V (d : ℕ) : Coordinates d → Space d := assembly d
abbrev W {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) : Space d := sliceCorrection hd z
abbrev U {d : ℕ} (hd : 11 ≤ d) : Coordinates d → Space d := slicePotential hd

theorem U_eq {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) : U hd z = V d z + W hd z := rfl

theorem V_order {d : ℕ} : V d =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) :=
  ((assembly d).isBigO_id _).norm_right

theorem W_order_two {d : ℕ} (hd : 11 ≤ d) :
    W hd =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^2) := sliceCorrection_coe_quadratic hd

theorem W_order_one {d : ℕ} (hd : 11 ≤ d) :
    W hd =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) := (W_order_two hd).trans pow_down

theorem U_order {d : ℕ} (hd : 11 ≤ d) :
    U hd =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) := slicePotential_linear hd

@[simp] theorem W_mean {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) : mean d (W hd z) = 0 :=
  (sliceCorrection hd z).property.1

@[simp] theorem VW_mean {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) :
    mean d (V d z * W hd z) = 0 := by
  rw [mul_comm]
  exact mean_mul_assembly (sliceCorrection hd z) z

theorem U_second {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) :
    mean d (U hd z^2) = mean d (V d z^2) + mean d (W hd z^2) := by
  have he : U hd z^2 = V d z^2 + (2:ℝ) • (V d z * W hd z) + W hd z^2 := by
    rw [U_eq]
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [he, map_add, map_add, map_smul, VW_mean, smul_zero, add_zero]

theorem U_third_error {d : ℕ} (hd : 11 ≤ d) :
    (fun z => mean d (U hd z^3) - 3*mean d (V d z^2 * W hd z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  have hvww : (fun z => V d z * W hd z^2)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
    convert! V_order.mul ((W_order_two hd).pow 2) using 1 <;> (ext z; ring)
  have hwww : (fun z => W hd z^3)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
    convert! ((W_order_two hd).pow 2).mul (W_order_one hd) using 1 <;> (ext z; ring)
  have he := (((mean d).isBigO_comp _ _).trans hvww).const_mul_left (3:ℝ)
  have he' := he.add (((mean d).isBigO_comp _ _).trans hwww)
  apply he'.congr_left
  intro z
  have hpoly : U hd z^3 = V d z^3 + (3:ℝ) • (V d z^2 * W hd z) +
      (3:ℝ) • (V d z * W hd z^2) + W hd z^3 := by
    rw [U_eq]
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [hpoly, map_add, map_add, map_add, map_smul, map_smul, assembly_third_moment]
  simp only [smul_eq_mul]
  ring

theorem U_fourth_error {d : ℕ} (hd : 11 ≤ d) :
    (fun z => mean d (U hd z^4) - mean d (V d z^4))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  have h1 : (fun z => U hd z^3) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := (U_order hd).pow 3
  have h2 : (fun z => U hd z^2 * V d z) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
    convert! ((U_order hd).pow 2).mul V_order using 1 <;> (ext z; ring)
  have h3 : (fun z => U hd z * V d z^2) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
    convert! (U_order hd).mul (V_order.pow 2) using 1 <;> (ext z; ring)
  have h4 : (fun z => V d z^3) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := V_order.pow 3
  have hp : (fun z => W hd z * (U hd z^3 + U hd z^2*V d z + U hd z*V d z^2 + V d z^3))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
    convert! (W_order_two hd).mul (((h1.add h2).add h3).add h4) using 1 <;> (ext z; ring)
  apply (((mean d).isBigO_comp _ _).trans hp).congr_left
  intro z
  rw [← map_sub]
  congr 1
  rw [U_eq]
  ring

#print axioms U_third_error
#print axioms U_fourth_error
end BecknerOnofri.HighDim.LocalEleven.SlavedMoments
