import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.QuarticSignsEleven
import BecknerOnofri.ComplementParameterDifference
import BecknerOnofri.LocalElevenCore.GibbsDifferenceBound
import BecknerOnofri.LocalElevenCore.UniformReducedCubic

/-! Quantitative dependence of the actual complementary graph on the parameter. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds

open BecknerOnofri.HighDim.UniformComplementBounds hiding correction_coe_uniform_quadratic correction_controlled_by_nonlinear correction_difference_resolvent correction_equation correction_inverse_parameter correction_potential_quadratic correction_tendsto correction_uniform_quadratic nonlinearGreen nonlinearRemainder_difference nonlinear_coordinates_uniform_cubic parameter_interval potential_difference potential_square_coordinates potential_square_coordinates_cubic potential_tendsto potential_uniform_linear reduced_uniform_cubic sliceMap sliceMap_tendsto uniformInverseBound uniformInverseBound_pos
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.QuadraticSlaving hiding correction_quadratic_expansion inverseGreen mean_slicePotential nonlinear_error_cubic normalized_error_cubic pow_down quadraticCorrection quadraticTerm_difference_cubic sliceCorrection sliceCorrection_coe_quadratic sliceCorrection_inverse sliceCorrection_quadratic slicePotential slicePotential_linear slicePotential_tendsto
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open ReducedCubicExpansion QuadraticSlaving

def sliceMap (d : ℕ) (x : ℝ × Coordinates d) : ℝ × Coordinates d := (1,x.2)

theorem sliceMap_tendsto (d : ℕ) : Tendsto (sliceMap d) (𝓝 (1,0)) (𝓝 (1,0)) :=
  (continuous_const.prodMk continuous_snd).continuousAt

theorem correction_equation {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d)
    (hx : projectedEquation (greenContinuous d) (x,correction hd x) = 0) :
    correction hd x - x.1 • (continuousComplementGreen (by omega) (correction hd x) +
      nonlinearGreen d (nonlinearRemainder (potential hd x))) = 0 := by
  rw [projectedEquation_eq (greenContinuous d) (green_first_complement_zero (by omega)),
    linearPart_eq (by omega)] at hx
  exact hx

theorem correction_difference_resolvent {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d)
    (hx : projectedEquation (greenContinuous d) (x,correction hd x) = 0)
    (hs : projectedEquation (greenContinuous d) (sliceMap d x,correction hd (sliceMap d x)) = 0)
    (hμ0 : 0 ≤ x.1) (hμ2 : x.1 ≤ 2) :
    correction hd x - correction hd (sliceMap d x) =
      continuousComplementInverse hd hμ0 hμ2
        ((x.1-1) • (continuousComplementGreen (by omega) (correction hd (sliceMap d x)) +
          nonlinearGreen d (nonlinearRemainder (potential hd (sliceMap d x)))) +
         x.1 • nonlinearGreen d (nonlinearRemainder (potential hd x) -
           nonlinearRemainder (potential hd (sliceMap d x)))) := by
  let e := continuousComplementContinuousLinearEquiv hd hμ0 hμ2
  have he : e (correction hd x - correction hd (sliceMap d x)) =
      (x.1-1) • (continuousComplementGreen (by omega) (correction hd (sliceMap d x)) +
        nonlinearGreen d (nonlinearRemainder (potential hd (sliceMap d x)))) +
      x.1 • nonlinearGreen d (nonlinearRemainder (potential hd x) -
        nonlinearRemainder (potential hd (sliceMap d x))) := by
    have ht := congrArg (fun F : complement d →L[ℝ] complement d =>
      F (correction hd x - correction hd (sliceMap d x)))
      (continuousComplementContinuousLinearEquiv_toCLM hd hμ0 hμ2)
    change e _ = _ at ht
    rw [ht]
    have h1 := correction_equation hd x hx
    have h2 := correction_equation hd (sliceMap d x) hs
    simp only [show (sliceMap d x).1 = 1 from rfl, one_smul] at h2
    change correction hd x - correction hd (sliceMap d x) -
      x.1 • continuousComplementGreen (by omega) (correction hd x - correction hd (sliceMap d x)) = _
    rw [map_sub, map_sub]
    calc
      _ = (correction hd x - x.1 • (continuousComplementGreen (by omega) (correction hd x) +
              nonlinearGreen d (nonlinearRemainder (potential hd x)))) -
            (correction hd (sliceMap d x) - (continuousComplementGreen (by omega)
              (correction hd (sliceMap d x)) + nonlinearGreen d
              (nonlinearRemainder (potential hd (sliceMap d x))))) +
            ((x.1-1) • (continuousComplementGreen (by omega) (correction hd (sliceMap d x)) +
              nonlinearGreen d (nonlinearRemainder (potential hd (sliceMap d x)))) +
              x.1 • (nonlinearGreen d (nonlinearRemainder (potential hd x)) -
                nonlinearGreen d (nonlinearRemainder (potential hd (sliceMap d x))))) := by module
      _ = _ := by rw [h1, h2]; simp only [sub_zero, zero_add]
  exact ((e.symm_apply_eq).mpr he.symm).symm

theorem potential_difference {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d) :
    potential hd x - potential hd (sliceMap d x) =
      ((correction hd x - correction hd (sliceMap d x) : complement d) : Space d) := by
  change (assembly d x.2 + (correction hd x : Space d)) -
    (assembly d x.2 + (correction hd (sliceMap d x) : Space d)) = _
  change _ = (correction hd x : Space d) - (correction hd (sliceMap d x) : Space d)
  abel

end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
