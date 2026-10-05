module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.ComplementParameterBound
public import BecknerOnofri.LocalElevenCore.ComplementParameterDifference

@[expose] public section

/-! The actual complement varies by O(|μ−1|‖z‖²), uniformly near the onset. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds

open BecknerOnofri.HighDim.UniformComplementBounds hiding correction_coe_uniform_quadratic correction_controlled_by_nonlinear correction_difference_resolvent correction_equation correction_inverse_parameter correction_parameter_bound correction_potential_quadratic correction_tendsto correction_uniform_quadratic nonlinearGreen nonlinearRemainder_difference nonlinear_coordinates_uniform_cubic parameter_interval potential_difference potential_square_coordinates potential_square_coordinates_cubic potential_tendsto potential_uniform_linear reduced_uniform_cubic sliceMap sliceMap_tendsto uniformInverseBound uniformInverseBound_pos
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.QuadraticSlaving hiding correction_quadratic_expansion inverseGreen mean_slicePotential nonlinear_error_cubic normalized_error_cubic pow_down quadraticCorrection quadraticTerm_difference_cubic sliceCorrection sliceCorrection_coe_quadratic sliceCorrection_inverse sliceCorrection_quadratic slicePotential slicePotential_linear slicePotential_tendsto
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open ReducedCubicExpansion QuadraticSlaving

theorem correction_parameter_bound {d : ℕ} (hd : 11 ≤ d) :
    (fun x => correction hd x - correction hd (sliceMap d x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => |x.1-1| *‖x.2‖^2) := by
  let B := uniformInverseBound d
  let L := nonlinearGreen d
  have hB : 0 < B := uniformInverseBound_pos d
  have hUpair : Tendsto (fun x => (potential hd x,potential hd (sliceMap d x)))
      (𝓝 (1,(0 : Coordinates d))) (𝓝 (0,0)) :=
    (potential_tendsto hd).prodMk_nhds ((potential_tendsto hd).comp (sliceMap_tendsto d))
  obtain ⟨C,hC,hLip⟩ := ((nonlinearRemainder_difference d).comp_tendsto hUpair).exists_pos
  have hm : Tendsto (fun x => max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖)
      (𝓝 (1,(0 : Coordinates d))) (𝓝 0) := by
    convert! (potential_tendsto hd).norm.max
      (((potential_tendsto hd).comp (sliceMap_tendsto d)).norm) using 1 <;>
      simp only [Function.comp_apply, norm_zero, max_self]
  have hsmall : ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      2*B*‖L‖*C*max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖ < 1/2 := by
    have ht := hm.const_mul (2*B*‖L‖*C)
    simp only [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  have hD : (fun x => correction hd x - correction hd (sliceMap d x))
      =O[𝓝 (1,(0 : Coordinates d))]
        (fun x => |x.1-1| *‖correction hd (sliceMap d x)‖) := by
    apply IsBigO.of_bound (2*B)
    filter_upwards [correction_solves hd, (sliceMap_tendsto d).eventually (correction_solves hd),
      parameter_interval (d := d), hLip.bound, hsmall] with x hx hs hμ hLipx hsmallx
    have h0 := correction_equation hd (sliceMap d x) hs
    simp only [show (sliceMap d x).1 = 1 from rfl, one_smul, sub_eq_zero] at h0
    have he := correction_difference_resolvent hd x hx hs hμ.1 hμ.2
    rw [← h0] at he
    have hLipx' : ‖nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x))‖ ≤
        C*(max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖ *
          ‖correction hd x - correction hd (sliceMap d x)‖) := by
      simpa only [Function.comp_apply, norm_mul, norm_norm,
        Real.norm_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _)), potential_difference, Submodule.norm_coe] using hLipx
    have hmain : ‖correction hd x - correction hd (sliceMap d x)‖ ≤
        B*(|x.1-1| *‖correction hd (sliceMap d x)‖ +
          2*‖L‖*C*max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖*
            ‖correction hd x - correction hd (sliceMap d x)‖) := by
      calc
        _ ≤ B*‖(x.1-1) • correction hd (sliceMap d x) +
            x.1 • L (nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x)))‖ := by
          rw [he]
          exact continuousComplementInverse_norm_le hd hμ.1 hμ.2 _
        _ ≤ B*(‖(x.1-1) • correction hd (sliceMap d x)‖ +
            ‖x.1 • L (nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x)))‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hB.le
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hB.le
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ.1]
          apply add_le_add le_rfl
          have hb := mul_le_mul hμ.2 (L.le_opNorm
            (nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x))))
            (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
          have hc := mul_le_mul_of_nonneg_left hLipx' (show (0:ℝ)≤2*‖L‖ by positivity)
          nlinarith
    have hh := mul_le_mul_of_nonneg_right hsmallx.le
      (norm_nonneg (correction hd x - correction hd (sliceMap d x)))
    simp only [norm_mul, norm_norm, Real.norm_eq_abs, abs_abs, abs_norm]
    nlinarith
  have hw := (correction_uniform_quadratic hd).comp_tendsto (sliceMap_tendsto d)
  have ha : (fun x : ℝ × Coordinates d => |x.1-1|) =O[𝓝 (1,0)] (fun x => |x.1-1|) := isBigO_refl _ _
  exact hD.trans (ha.mul hw.norm_left)

#print axioms correction_parameter_bound
end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
