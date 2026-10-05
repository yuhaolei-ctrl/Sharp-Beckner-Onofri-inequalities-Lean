import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.QuarticSignsEleven
import BecknerOnofri.UniformReducedCubic
import BecknerOnofri.LocalElevenCore.UniformComplementBounds

/-! Uniform cubic size of the nonlinear part of the actual reduced equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds

open BecknerOnofri.HighDim.UniformComplementBounds hiding correction_coe_uniform_quadratic correction_controlled_by_nonlinear correction_inverse_parameter correction_potential_quadratic correction_tendsto correction_uniform_quadratic nonlinearGreen nonlinear_coordinates_uniform_cubic parameter_interval potential_square_coordinates potential_square_coordinates_cubic potential_tendsto potential_uniform_linear reduced_uniform_cubic uniformInverseBound uniformInverseBound_pos
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.QuadraticSlaving hiding correction_quadratic_expansion inverseGreen mean_slicePotential nonlinear_error_cubic normalized_error_cubic pow_down quadraticCorrection quadraticTerm_difference_cubic sliceCorrection sliceCorrection_coe_quadratic sliceCorrection_inverse sliceCorrection_quadratic slicePotential slicePotential_linear slicePotential_tendsto
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open ReducedCubicExpansion QuadraticSlaving

theorem potential_square_coordinates {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d) :
    coordinates d (potential hd x ^ 2) =
      (2:ℝ) • coordinates d (assembly d x.2 * (correction hd x : Space d)) +
      coordinates d ((correction hd x : Space d)^2) := by
  have he : potential hd x ^ 2 = (assembly d x.2)^2 +
      (2:ℝ) • (assembly d x.2 * (correction hd x : Space d)) +
      (correction hd x : Space d)^2 := by
    change (assembly d x.2 + (correction hd x : Space d))^2 = _
    ext t
    simp only [ContinuousMap.add_apply, ContinuousMap.pow_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, smul_eq_mul]
    ring
  rw [he, map_add, map_add, map_smul, coordinates_shellSquare, zero_add]

theorem potential_square_coordinates_cubic {d : ℕ} (hd : 11 ≤ d) :
    (fun x => coordinates d (potential hd x^2))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
  have hV : (fun x : ℝ × Coordinates d => assembly d x.2)
      =O[𝓝 (1,0)] (fun x => ‖x.2‖) := ((assembly d).isBigO_comp _ _).norm_right
  have hVW : (fun x => assembly d x.2 * (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
    convert! hV.mul (correction_coe_uniform_quadratic hd) using 1 <;> (ext x; ring)
  have hW1 := (correction_coe_uniform_quadratic hd).trans
    (pow_down.comp_tendsto (continuous_snd.continuousAt :
      Tendsto (Prod.snd : ℝ × Coordinates d → Coordinates d) (𝓝 (1,0)) (𝓝 0)))
  have hWW : (fun x => (correction hd x : Space d)^2)
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
    convert! (correction_coe_uniform_quadratic hd).mul hW1 using 1 <;> (ext x; ring)
  exact ((((coordinates d).isBigO_comp _ _).trans hVW).const_smul_left (2:ℝ)).add
    (((coordinates d).isBigO_comp _ _).trans hWW) |>.congr_left
      (fun x => (potential_square_coordinates hd x).symm)

theorem nonlinear_coordinates_uniform_cubic {d : ℕ} (hd : 11 ≤ d) :
    (fun x => coordinates d (nonlinearRemainder (potential hd x)))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
  have hN := ((normalized_quadratic_remainder d).comp_tendsto (potential_tendsto hd)).trans
    ((potential_uniform_linear hd).norm_left.pow 3)
  have hQ := (potential_square_coordinates_cubic hd).const_smul_left (1/2:ℝ)
  apply ((((coordinates d).isBigO_comp _ _).trans hN).add hQ).congr_left
  intro x
  dsimp only [Pi.smul_apply]
  have hm : mean d (potential hd x) = 0 := mean_reconstruction _
  rw [← coordinates_center (potential hd x^2), ← map_smul,
    ← quadraticTerm_of_mean_zero hm, ← map_add]
  congr 1
  dsimp only [Function.comp_apply]
  unfold quadraticPolynomial nonlinearRemainder
  abel

/-- The parameter-axis linearization is removed exactly, leaving a uniform cubic bound. -/
theorem reduced_uniform_cubic {d : ℕ} (hd : 11 ≤ d) :
    (fun x => reduced hd x - (1-x.1) • x.2)
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
  have hμ : (Prod.fst : ℝ × Coordinates d → ℝ) =O[𝓝 (1,0)] (fun _ => (1:ℝ)) :=
    continuous_fst.continuousAt.isBigO
  have hh := hμ.smul (nonlinear_coordinates_uniform_cubic hd)
  simp only [smul_eq_mul, one_mul] at hh
  apply hh.neg_left.congr_left
  intro x
  rw [reduced_eq_linear_remainder]
  abel

#print axioms nonlinear_coordinates_uniform_cubic
#print axioms reduced_uniform_cubic
end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
