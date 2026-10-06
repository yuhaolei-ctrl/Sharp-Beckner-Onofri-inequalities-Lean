module

public import BecknerOnofri.QuarticCoercivityEleven
public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.CriticalGraphCoercivity
public import BecknerOnofri.LocalElevenCore.ReducedQuarticParity
public import BecknerOnofri.QuarticBranches

@[expose] public section

/-! Strict local negativity of the actual physical critical reduced energy,
with a uniform quartic norm bound. -/
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.ReducedPhysicalEnergy

open BecknerOnofri.HighDim.ReducedPhysicalEnergy hiding criticalReducedEnergy criticalReducedEnergy_coercive criticalReducedEnergy_eq criticalReducedEnergy_quartic criticalReducedEnergy_quartic_sixth criticalReducedEnergy_strictly_negative dualFunctional_graphExpression norm_fourth_le_sum quarticValue_coercive quarticValue_eq_reducedQuartic
open BecknerOnofri.HighDim.QuadraticModes hiding actual_quartic_coefficients amplitude_sum_square assembly_fourth_moment assembly_quartic_cumulant assembly_second_moment assembly_third_moment complementGreen_synthesis complementMap_center complementMap_const complementMap_synthesis complementMap_synthesis_zero complementSynthesis green_complementMap green_synthesis inverseGreen_factor mixedAmplitudeSum off_diagonal_sum quadraticCorrection_eq_resolvent quadraticSource_expansion quadraticSource_value quadratic_schur_identity quartic_slaving_contribution resolvent resolventPair resolventPair_apply resolventPair_synthesis resolvent_synthesis schur_diagonal schur_double_sum schur_off_diagonal shellSquare_first_coefficient shellSquare_mean shellSquare_projection sourcePair sourcePair_diagonal sourcePair_off_diagonal source_norm_moment source_norm_sq synthesis_mem_complement
open BecknerOnofri.HighDim.ReducedQuarticExpansion hiding U_analytic W_analytic centeredLogPartition_analytic centeredLogPartition_translation graphExpression graphExpression_analytic graphExpression_error graphExpression_even graphExpression_quartic graphExpression_quartic_sixth graphExpression_translation pairing_quadraticCorrection pairing_remainder_order_five quadraticCorrection_analytic quarticValue quarticValue_analytic quarticValue_even translation_mul translation_pow
open ContinuousFirstShell ReducedQuarticExpansion QuadraticModes

theorem quarticValue_eq_reducedQuartic {d : ℕ} (z : Coordinates d) :
    quarticValue z = reducedQuartic d 0 (fun i => ‖z i‖^2) := by
  have h := amplitude_sum_square z
  unfold quarticValue reducedQuartic
  simp only [zero_mul, zero_add, ← pow_mul, show 2*2=4 from rfl]
  rw [h]
  ring

theorem norm_fourth_le_sum {d : ℕ} (hd : 0 < d) (z : Coordinates d) :
    ‖z‖^4 ≤ ∑ i, ‖z i‖^4 := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i : Fin d => ‖z i‖)
    Finset.univ_nonempty
  have hnorm : ‖z‖ ≤ ‖z i‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hi j (Finset.mem_univ j))
  exact (pow_le_pow_left₀ (norm_nonneg z) hnorm 4).trans
    (Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg (z j)) 4) (Finset.mem_univ i))

theorem quarticValue_coercive {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) :
    quarticValue z ≤ -(kappa d / 2) * ‖z‖^4 := by
  have h := BecknerOnofri.HighDim.LocalQuartic.reducedQuartic_coercive hd 0 (fun i => ‖z i‖^2)
  rw [← quarticValue_eq_reducedQuartic] at h
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, sub_zero,
    zero_sub, ← pow_mul, show 2*2=4 from rfl] at h
  have hs := norm_fourth_le_sum (by omega : 0 < d) z
  have hk := BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd
  nlinarith

/-- At critical coupling the exact reduced energy is bounded above by a
strict negative quartic, throughout one neighborhood of zero. -/
theorem criticalReducedEnergy_coercive {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      criticalReducedEnergy hd z ≤ -(kappa d / 4) * ‖z‖^4 := by
  have ho : (fun z => criticalReducedEnergy hd z - quarticValue z)
      =o[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) :=
    (criticalReducedEnergy_quartic_sixth hd).trans_isLittleO
      (isLittleO_norm_pow_norm_pow (by decide : 4 < 6))
  have hk := BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd
  filter_upwards [ho.bound (show 0 < kappa d / 4 by positivity)] with z hz
  have hab : criticalReducedEnergy hd z - quarticValue z ≤ kappa d / 4 * ‖z‖^4 := by
    have hh : |criticalReducedEnergy hd z - quarticValue z| ≤ kappa d / 4 * ‖z‖^4 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg z) 4)] using hz
    exact (le_abs_self _).trans hh
  have hq := quarticValue_coercive hd z
  linarith

theorem criticalReducedEnergy_strictly_negative {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), z ≠ 0 → criticalReducedEnergy hd z < 0 := by
  filter_upwards [criticalReducedEnergy_coercive hd] with z hz
  intro hne
  exact hz.trans_lt (mul_neg_of_neg_of_pos (by have := BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd; linarith)
    (pow_pos (norm_pos_iff.mpr hne) 4))

#print axioms criticalReducedEnergy_coercive
#print axioms criticalReducedEnergy_strictly_negative
end BecknerOnofri.HighDim.LocalEleven.ReducedPhysicalEnergy
