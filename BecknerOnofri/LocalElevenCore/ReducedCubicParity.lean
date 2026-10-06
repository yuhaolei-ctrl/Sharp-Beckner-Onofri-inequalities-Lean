module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.ReducedCubicParity
public import BecknerOnofri.LocalElevenCore.ReducedCubicExpansion
public import BecknerOnofri.AnalyticEvenOrder
public import BecknerOnofri.LocalElevenCore.FirstShellOrbits

@[expose] public section

/-! Genuine translation parity improves the actual reduced cubic remainder to order five. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ReducedCubicExpansion

open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth
open BecknerOnofri.HighDim.QuadraticModes hiding actual_quartic_coefficients actual_reduced_cubic_coefficient actual_reduced_cubic_diagonal actual_reduced_cubic_diagonal_nonzero amplitude_sum_square assembly_cube_coefficient assembly_fourth_moment assembly_product_coefficient assembly_quadraticCorrection_coefficient assembly_quartic_cumulant assembly_second_moment assembly_third_moment complementGreen_synthesis complementMap_center complementMap_const complementMap_synthesis complementMap_synthesis_zero complementSynthesis cubicTerm_first_coefficient green_complementMap green_synthesis inverseGreen_factor mixedAmplitudeSum off_diagonal_sum quadraticCorrection_coefficient quadraticCorrection_diff quadraticCorrection_double quadraticCorrection_eq_resolvent quadraticCorrection_sum quadraticSource_expansion quadraticSource_value quadratic_schur_identity quartic_slaving_contribution resolvent resolventPair resolventPair_apply resolventPair_synthesis resolvent_coefficient resolvent_synthesis schur_diagonal schur_double_sum schur_off_diagonal shellSquare_first_coefficient shellSquare_mean shellSquare_projection sourcePair sourcePair_diagonal sourcePair_off_diagonal source_norm_moment source_norm_sq synthesis_complex synthesis_mem_complement synthesis_product_coefficient
open BecknerOnofri.HighDim.QuadraticSlaving hiding correction_quadratic_expansion inverseGreen mean_slicePotential nonlinear_error_cubic normalized_error_cubic pow_down quadraticCorrection quadraticTerm_difference_cubic sliceCorrection sliceCorrection_coe_quadratic sliceCorrection_inverse sliceCorrection_quadratic slicePotential slicePotential_linear slicePotential_tendsto
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open BecknerOnofri.HighDim.SlavedMoments hiding U U_eq U_fourth_error U_order U_second U_third_error V VW_mean V_order W W_mean W_order_one W_order_two mean_mul_assembly
open ContinuousGibbs ContinuousFirstShell QuadraticModes QuadraticSlaving SlavedMoments ReducedEquation

theorem quadraticCorrection_analytic {d : ℕ} (hd : 11 ≤ d) :
    AnalyticAt ℝ (quadraticCorrection hd) (0 : Coordinates d) := by
  have hv := (assembly d).analyticAt (0 : Coordinates d)
  have hc := ((center d).analyticAt _).comp (hv.pow 2)
  have hq : AnalyticAt ℝ (fun z : Coordinates d => (1/2:ℝ) • center d ((assembly d z)^2)) 0 :=
    by convert! (show AnalyticAt ℝ (fun _ : Coordinates d => (1/2:ℝ)) 0 from analyticAt_const).smul hc using 1
  have hh := ((inverseGreen hd).analyticAt _).comp hq
  convert! hh using 1
  funext z
  unfold quadraticCorrection
  rw [quadraticTerm_of_mean_zero (mean_assembly z)]
  rfl

theorem cubicTerm_assembly_analytic (d : ℕ) :
    AnalyticAt ℝ (fun z : Coordinates d => cubicTerm (assembly d z)) 0 := by
  have hv := (assembly d).analyticAt (0 : Coordinates d)
  have hc := ((center d).analyticAt _).comp (hv.pow 3)
  have hm := ((mean d).analyticAt _).comp (hv.pow 2)
  have h1 : AnalyticAt ℝ (fun z : Coordinates d => (1/6:ℝ) • center d ((assembly d z)^3)) 0 :=
    by convert! (show AnalyticAt ℝ (fun _ : Coordinates d => (1/6:ℝ)) 0 from analyticAt_const).smul hc using 1
  have h2 : AnalyticAt ℝ (fun z : Coordinates d => ((1/2:ℝ)*mean d ((assembly d z)^2)) • assembly d z) 0 :=
    (analyticAt_const.mul hm).smul hv
  convert! h1.sub h2 using 1
  funext z
  exact cubicTerm_of_mean_zero (mean_assembly z)

theorem cubicModel_analytic {d : ℕ} (hd : 11 ≤ d) :
    AnalyticAt ℝ (cubicModel hd) (0 : Coordinates d) := by
  have hv := (assembly d).analyticAt (0 : Coordinates d)
  have hw := ((complement d).subtypeL.analyticAt _).comp (quadraticCorrection_analytic hd)
  exact (((coordinates d).analyticAt _).comp ((hv.mul hw).add (cubicTerm_assembly_analytic d))).neg

theorem cubicModel_neg {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) : cubicModel hd (-z) = -cubicModel hd z := by
  funext i
  rw [Pi.neg_apply, cubicModel_apply, cubicModel_apply]
  simp only [Pi.neg_apply, norm_neg]
  ring

/-- The actual vector reduced equation has the sharp parity-consistent O5 cubic remainder. -/
theorem reduced_cubic_expansion_fifth {d : ℕ} (hd : 11 ≤ d) :
    (fun z => reduced hd (1,z) - cubicModel hd z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  have ha : AnalyticAt ℝ (fun z : Coordinates d => reduced hd (1,z)) 0 :=
    (reduced_analytic hd).comp (analyticAt_const.prod analyticAt_id)
  apply analytic_odd_fourth_order (ha.sub (cubicModel_analytic hd)) (reduced_cubic_expansion hd)
  have ht : Tendsto (fun z : Coordinates d => ((1:ℝ),z)) (𝓝 0) (𝓝 (1,0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [ht.eventually (ContinuousSymmetry.reduced_neg hd)] with z hz
  change reduced hd (1,-z) - cubicModel hd (-z) = -(reduced hd (1,z) - cubicModel hd z)
  change reduced hd (1,-z) = -reduced hd (1,z) at hz
  rw [hz, cubicModel_neg]
  abel

/-- Actual diagonal scalar equation R(1,t)=κd t³+O(t⁵). -/
theorem reduced_diagonal_cubic_expansion_fifth {d : ℕ} (hd : 11 ≤ d) (i : Fin d) :
    (fun t : ℝ => (reduced hd (1, realDiagonal d t) i).re - kappa d*t^3)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^5) := by
  have ht : Tendsto (realDiagonal d) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (realDiagonal d).continuous.continuousAt.tendsto (x := (0:ℝ))
  have h := (reduced_cubic_expansion_fifth hd).comp_tendsto ht
  have hnorm := ((realDiagonal d).isBigO_id (𝓝 0)).norm_left.norm_right.pow 5
  have h' := h.trans hnorm
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj i)
  apply (((ev).isBigO_comp _ _).trans h').congr_left
  intro t
  change (reduced hd (1, realDiagonal d t) i - cubicModel hd (realDiagonal d t) i).re = _
  rw [cubicModel_diagonal, Complex.sub_re, Complex.ofReal_re]

#print axioms reduced_cubic_expansion_fifth
#print axioms reduced_diagonal_cubic_expansion_fifth
end BecknerOnofri.HighDim.LocalEleven.ReducedCubicExpansion
