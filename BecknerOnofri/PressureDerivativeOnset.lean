module

public import BecknerOnofri.BranchFirstDerivativeRemainder
public import BecknerOnofri.PressureSecondDerivative

@[expose] public section

/-! The manuscript's quantitative first-derivative onset formula. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.DiagonalScalarBranch

lemma supercriticalEnergy_derivative_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => deriv (supercriticalEnergy hd) μ-(d:ℝ)/kappa d*onset μ)
      =O[𝓝[>] (1:ℝ)] (fun μ => (onset μ)^2) := by
  have hfour : (fun μ => ‖amplitude hd μ‖^4) =O[𝓝[>] (1:ℝ)] (fun μ => (onset μ)^2) := by
    convert! (amplitude_square_bound hd).pow 2 using 1
    funext μ
    rw [Real.norm_eq_abs,abs_of_nonneg (amplitude_nonneg hd μ)]
    ring
  have hmain := ((energy_parameter_derivative_expansion hd).comp_tendsto
    (amplitude_tendsto_right hd)).trans hfour
  have hamp := (amplitude_square_expansion hd).const_mul_left (d:ℝ)
  apply (hmain.add hamp).congr'
  · filter_upwards [supercriticalEnergy_hasDerivAt hd] with μ hm
    rw [hm.deriv]
    dsimp only [Function.comp_apply]
    ring
  · rfl

end BecknerOnofri.HighDim.DiagonalScalarBranch
namespace BecknerOnofri.HighDim.OnsetConsequences
open DiagonalScalarBranch

lemma pressure_derivative_expansion (d : ℕ) (hd : 12 ≤ d) :
    (fun β => deriv (fun γ => (pressure d γ).toReal) β-
      (d:ℝ)/(kappa d*spectralThreshold d)*onsetDelta d β)
      =O[𝓝[>] (spectralThreshold d)] (fun β => (onsetDelta d β)^2) := by
  have hσ := (spectralThreshold_pos (by omega : 0 < d)).ne'
  have he : (fun β => (pressure d β).toReal) =ᶠ[𝓝[>] (spectralThreshold d)]
      (fun β => supercriticalEnergy hd ((spectralThreshold d)⁻¹*β)) := by
    filter_upwards [(normalized_parameter_tendsto hd).eventually (pressure_eq_supercritical d hd)] with β hβ
    change (pressure d ((β / spectralThreshold d) * spectralThreshold d)).toReal = _ at hβ
    rw [div_mul_cancel₀ _ hσ] at hβ
    simpa only [div_eq_mul_inv,mul_comm] using hβ
  have h := ((supercriticalEnergy_derivative_expansion hd).comp_tendsto
    (normalized_parameter_tendsto hd)).const_mul_left ((spectralThreshold d)⁻¹)
  apply h.congr'
  · filter_upwards [eventually_local_right he] with β hb
    change (fun γ => (pressure d γ).toReal) =ᶠ[𝓝 β]
      (fun γ => supercriticalEnergy hd ((spectralThreshold d)⁻¹*γ)) at hb
    rw [hb.deriv_eq,deriv_comp_mul_left]
    dsimp only [Function.comp_apply]
    rw [physical_onset_eq hd]
    simp only [smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
    ring
  · exact Eventually.of_forall (fun β => by simp only [Function.comp_apply,physical_onset_eq hd])

#print axioms pressure_derivative_expansion
end BecknerOnofri.HighDim.OnsetConsequences
