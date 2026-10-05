import BecknerOnofri.BranchSecondDerivativeRemainder
import BecknerOnofri.PressureDerivativeOnset

/-! The differentiated pressure asymptotics from the analytic local branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.DiagonalScalarBranch

lemma supercriticalEnergy_second_derivative_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => deriv (deriv (supercriticalEnergy hd)) μ-(d:ℝ)/kappa d)
      =O[𝓝[>] (1:ℝ)] onset := by
  have hb : (fun μ => ‖amplitude hd μ‖^2) =O[𝓝[>] (1:ℝ)] onset := by
    simpa only [Real.norm_eq_abs,sq_abs] using amplitude_square_bound hd
  have h := ((energy_parameter_second_derivative_expansion hd).comp_tendsto
    (amplitude_tendsto_right hd)).trans hb
  apply h.congr'
  · filter_upwards [supercriticalEnergy_second_hasDerivAt hd] with μ hm
    exact congrArg (fun x => x-(d:ℝ)/kappa d) hm.deriv.symm
  · rfl

end BecknerOnofri.HighDim.DiagonalScalarBranch
namespace BecknerOnofri.HighDim.OnsetConsequences
open DiagonalScalarBranch

lemma pressure_second_derivative_expansion (d : ℕ) (hd : 12 ≤ d) :
    (fun β => deriv (deriv (fun γ => (pressure d γ).toReal)) β-
      (d:ℝ)/(kappa d*(spectralThreshold d)^2))
      =O[𝓝[>] (spectralThreshold d)] (onsetDelta d) := by
  have hσ := (spectralThreshold_pos (by omega : 0 < d)).ne'
  have he : (fun β => (pressure d β).toReal) =ᶠ[𝓝[>] (spectralThreshold d)]
      (fun β => supercriticalEnergy hd ((spectralThreshold d)⁻¹*β)) := by
    filter_upwards [(normalized_parameter_tendsto hd).eventually (pressure_eq_supercritical d hd)] with β hβ
    change (pressure d ((β / spectralThreshold d) * spectralThreshold d)).toReal = _ at hβ
    rw [div_mul_cancel₀ _ hσ] at hβ
    simpa only [div_eq_mul_inv,mul_comm] using hβ
  have h := ((supercriticalEnergy_second_derivative_expansion hd).comp_tendsto
    (normalized_parameter_tendsto hd)).const_mul_left ((spectralThreshold d)⁻¹^2)
  apply h.congr'
  · filter_upwards [second_deriv_eventuallyEq_right he] with β hb
    rw [hb,second_deriv_scaled]
    dsimp only [Function.comp_apply]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · exact Eventually.of_forall (fun β => by simpa only [Function.comp_apply] using physical_onset_eq hd β)

lemma pressure_first_derivative_right (d : ℕ) (hd : 12 ≤ d) :
    Tendsto (deriv (fun β => (pressure d β).toReal))
      (𝓝[>] (spectralThreshold d)) (𝓝 0) := by
  have hδ : Tendsto (onsetDelta d) (𝓝[>] (spectralThreshold d)) (𝓝 0) := by
    simpa only [Function.comp_def,physical_onset_eq hd] using onset_tendsto.comp (normalized_parameter_tendsto hd)
  have hr := (pressure_derivative_expansion d hd).trans_tendsto
    (show Tendsto (fun β => (onsetDelta d β)^2) _ (𝓝 0) by simpa using hδ.pow 2)
  have h := hr.add (hδ.const_mul ((d:ℝ)/(kappa d*spectralThreshold d)))
  simpa only [sub_add_cancel,mul_zero,zero_add] using h

lemma pressure_first_derivative_left (d : ℕ) (hd : 12 ≤ d) :
    Tendsto (deriv (fun β => (pressure d β).toReal))
      (𝓝[<] (spectralThreshold d)) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have he : (fun γ => (pressure d γ).toReal) =ᶠ[𝓝 β] (fun _ => 0) := by
    filter_upwards [gt_mem_nhds hβ] with γ hγ
    simp [pressure_zero_below hd hγ.le]
  simpa using he.deriv_eq.symm

#print axioms pressure_second_derivative_expansion
#print axioms pressure_first_derivative_right
#print axioms pressure_first_derivative_left
end BecknerOnofri.HighDim.OnsetConsequences
