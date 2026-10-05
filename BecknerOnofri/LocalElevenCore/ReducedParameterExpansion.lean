module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.ReducedParameterExpansion
public import BecknerOnofri.LocalElevenCore.ComplementParameterBound

@[expose] public section

/-! The exact cubic reduced equation with a quantitative joint parameter remainder. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds

open BecknerOnofri.HighDim.UniformComplementBounds hiding correction_coe_uniform_quadratic correction_controlled_by_nonlinear correction_difference_resolvent correction_equation correction_inverse_parameter correction_parameter_bound correction_potential_quadratic correction_tendsto correction_uniform_quadratic nonlinearGreen nonlinearRemainder_difference nonlinear_coordinates_uniform_cubic nonlinear_parameter_bound parameter_interval potential_difference potential_square_coordinates potential_square_coordinates_cubic potential_tendsto potential_uniform_linear realDiagonal_norm reduced_diagonal_parameter_expansion reduced_parameter_cubic_expansion reduced_parameter_difference reduced_uniform_cubic sliceMap sliceMap_tendsto uniformInverseBound uniformInverseBound_pos
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.QuadraticSlaving hiding correction_quadratic_expansion inverseGreen mean_slicePotential nonlinear_error_cubic normalized_error_cubic pow_down quadraticCorrection quadraticTerm_difference_cubic sliceCorrection sliceCorrection_coe_quadratic sliceCorrection_inverse sliceCorrection_quadratic slicePotential slicePotential_linear slicePotential_tendsto
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open ReducedCubicExpansion QuadraticSlaving

theorem nonlinear_parameter_bound {d : ℕ} (hd : 11 ≤ d) :
    (fun x => nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x)))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => |x.1-1| * ‖x.2‖^3) := by
  have hUpair : Tendsto (fun x => (potential hd x,potential hd (sliceMap d x)))
      (𝓝 (1,(0 : Coordinates d))) (𝓝 (0,0)) :=
    (potential_tendsto hd).prodMk_nhds ((potential_tendsto hd).comp (sliceMap_tendsto d))
  have hdiff := (nonlinearRemainder_difference d).comp_tendsto hUpair
  have hmax0 : (fun x => max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖)
      =O[𝓝 (1,(0 : Coordinates d))]
        (fun x => ‖potential hd x‖ + ‖potential hd (sliceMap d x)‖) := by
    apply IsBigO.of_norm_le
    intro x
    rw [Real.norm_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hmax := hmax0.trans ((potential_uniform_linear hd).norm_left.add
    (((potential_uniform_linear hd).comp_tendsto (sliceMap_tendsto d)).norm_left))
  have hwdiff : (fun x => ‖potential hd x - potential hd (sliceMap d x)‖)
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => |x.1-1| * ‖x.2‖^2) := by
    simpa only [potential_difference, Submodule.norm_coe] using (correction_parameter_bound hd).norm_left
  have hh := hdiff.trans (hmax.mul hwdiff)
  convert! hh using 1 <;> (ext x; ring)

theorem reduced_parameter_difference {d : ℕ} (hd : 11 ≤ d) :
    (fun x => reduced hd x - (1-x.1) • x.2 - reduced hd (sliceMap d x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => |x.1-1| * ‖x.2‖^3) := by
  have hδ : (fun x : ℝ × Coordinates d => x.1-1)
      =O[𝓝 (1,0)] (fun x => |x.1-1|) := (isBigO_refl _ _).norm_right
  have hN0 := (nonlinear_coordinates_uniform_cubic hd).comp_tendsto (sliceMap_tendsto d)
  have ha := hδ.smul hN0
  have hμ : (Prod.fst : ℝ × Coordinates d → ℝ) =O[𝓝 (1,0)] (fun _ => (1:ℝ)) :=
    continuous_fst.continuousAt.isBigO
  have hb := hμ.smul (((coordinates d).isBigO_comp _ _).trans (nonlinear_parameter_bound hd))
  simp only [smul_eq_mul, one_mul] at ha hb
  apply (ha.neg_left.sub hb).congr_left
  intro x
  dsimp only [Function.comp_apply]
  rw [map_sub, reduced_eq_linear_remainder, reduced_eq_linear_remainder]
  simp only [sliceMap, sub_self, zero_smul, one_smul, zero_sub]
  module

/-- Actual full first-shell equation, uniformly in parameter and amplitude near onset. -/
theorem reduced_parameter_cubic_expansion {d : ℕ} (hd : 11 ≤ d) :
    (fun x => reduced hd x - (1-x.1) • x.2 - cubicModel hd x.2)
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^5 + |x.1-1| * ‖x.2‖^3) := by
  have ht : Tendsto (Prod.snd : ℝ × Coordinates d → Coordinates d) (𝓝 (1,0)) (𝓝 0) :=
    continuous_snd.continuousAt
  have hslice := (reduced_cubic_expansion_fifth hd).comp_tendsto ht
  have hh := hslice.add_add (reduced_parameter_difference hd)
  dsimp only [Function.comp_apply] at hh
  simp only [norm_pow, norm_norm, norm_mul, Real.norm_eq_abs, abs_abs, abs_norm] at hh
  apply hh.congr_left
  intro x
  dsimp only [Function.comp_apply, sliceMap]
  abel

theorem realDiagonal_norm {d : ℕ} (hd : 0 < d) (t : ℝ) : ‖realDiagonal d t‖ = ‖t‖ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  change ‖fun _ : Fin d => (t:ℂ)‖ = ‖t‖
  rw [pi_norm_const, Complex.norm_real]

/-- The scalar diagonal equation is (1−μ)t+κt³+O(t⁵+|μ−1|t³), for the actual Gibbs reduction. -/
theorem reduced_diagonal_parameter_expansion {d : ℕ} (hd : 11 ≤ d) (i : Fin d) :
    (fun x : ℝ × ℝ => (reduced hd (x.1,realDiagonal d x.2) i).re -
      (1-x.1)*x.2 - kappa d*x.2^3)
      =O[𝓝 (1,0)] (fun x : ℝ × ℝ => ‖x.2‖^5 + |x.1-1| * ‖x.2‖^3) := by
  have ht : Tendsto (fun x : ℝ × ℝ => (x.1, realDiagonal d x.2))
      (𝓝 (1,0)) (𝓝 (1,0)) := by
    convert! (continuous_fst.prodMk ((realDiagonal d).continuous.comp continuous_snd)).continuousAt.tendsto
      (x := ((1,0) : ℝ × ℝ)) using 1 <;> simp only [Function.comp_apply, map_zero]
  have hh := (reduced_parameter_cubic_expansion hd).comp_tendsto ht
  simp only [Function.comp_def, realDiagonal_norm (by omega : 0<d)] at hh
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj i)
  apply ((ev.isBigO_comp _ _).trans hh).congr_left
  intro x
  change (reduced hd (x.1,realDiagonal d x.2) i - (1-x.1) • realDiagonal d x.2 i -
    cubicModel hd (realDiagonal d x.2) i).re = _
  rw [cubicModel_diagonal]
  simp only [Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, realDiagonal_apply, mul_zero, sub_zero]

#print axioms reduced_parameter_cubic_expansion
#print axioms reduced_diagonal_parameter_expansion
end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
