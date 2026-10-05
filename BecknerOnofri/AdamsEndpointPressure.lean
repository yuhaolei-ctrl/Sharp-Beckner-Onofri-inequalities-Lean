import BecknerOnofri.AdamsEndpointEnergy
import BecknerOnofri.SmoothPressureRestriction
import BecknerOnofri.FiniteEntropyPhysical
import BecknerOnofri.LowDimensionDefinitions
import BecknerOnofri.UniformFourierHessian

/-! Transfer of the critical energy bound to the full finite-entropy and
raw critical-Sobolev variational domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim

 theorem pressure_at_collapse_le {d : ℕ} (hd : 0 < d) :
    pressure d (2*(d:ℝ)) ≤ ((d:ℝ)*AdamsEndpoint.coordinateComparisonConstant d : ℝ) := by
  rw [pressure_eq_smooth_sup hd]
  refine iSup_le (fun ρ => iSup_le (fun hρ => iSup_le (fun hs => iSup_le (fun hp => ?_))))
  have hc := AdamsEndpoint.critical_entropy_energy hd (Bridge.density ρ)
    (UniformFourier.smooth_continuous hs) hp
  rw [FiniteEntropyPhysical.physical_eq_spectral hd (Bridge.density ρ) hρ,
    Legacy.BecknerOnofri.normalized_energy] at hc
  have he : Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = ∑' k, spectralTerm ρ k :=
    tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  rw [he] at hc
  change (d:ℝ)*((∑' k, spectralTerm ρ k)/spectralThreshold d)-entropy ρ ≤ _ at hc
  rw [spectralEnergy_coe_eq_tsum hd ρ hρ,← EReal.coe_mul,← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  convert hc using 1 <;> ring

theorem pressure_at_collapse_finite {d : ℕ} (hd : 0 < d) :
    pressure d (2*(d:ℝ)) < ⊤ :=
  (pressure_at_collapse_le hd).trans_lt (EReal.coe_lt_top _)

theorem coefficient_at_collapse_le {d : ℕ} (hd : 0 < d) :
    coefficientDefect d (collapseCoefficient d) ≤
      ((d:ℝ)*AdamsEndpoint.coordinateComparisonConstant d : ℝ) := by
  have hβ : 0 < 2*(d:ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr hd)
  have he : spectralThreshold d / (2*(2*(d:ℝ))*(2*Real.pi)^d) = collapseCoefficient d := by
    unfold collapseCoefficient
    congr 1
    ring
  have hh := pressure_at_collapse_le hd
  rw [pressure_eq_coefficientDefect hd hβ,he] at hh
  exact hh

theorem critical_adams_bound {d : ℕ} (hd : 0 < d) :
    ∃ B : ℝ, ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u + B : ℝ) : EReal) := by
  refine ⟨(d:ℝ)*AdamsEndpoint.coordinateComparisonConstant d, fun u hu => ?_⟩
  have hself : logPartition u - ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ≤
      coefficientDefect d (collapseCoefficient d) :=
    le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  have hh := hself.trans (coefficient_at_collapse_le hd)
  rw [logPartition_eq_log_integral hd u hu,← EReal.coe_sub] at hh
  have hreal := EReal.coe_le_coe_iff.mp hh
  rw [logPartition_eq_log_integral hd u hu]
  apply EReal.coe_le_coe_iff.mpr
  linarith

#print axioms pressure_at_collapse_finite
#print axioms critical_adams_bound
end BecknerOnofri.HighDim
