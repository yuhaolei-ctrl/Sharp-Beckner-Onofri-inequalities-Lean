module

public import BecknerOnofri.LowDimensionDefinitions
public import BecknerOnofri.FiniteEntropyEnergy
public import Legacy.BecknerOnofri.LowDimensionComplete

@[expose] public section

/-! The recovered low-dimensional proof on the current trusted raw-function
domains. All comparisons use actual Haar integrals and Fourier energies. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate
namespace BecknerOnofri.HighDim
namespace LowDimension

theorem coefficient_eq {d : ℕ} (hd : 0 < d) :
    collapseCoefficient d = 1 / (4 * (d : ℝ) * Legacy.TorusEndpoint.endpointSymbolConstant d) := by
  unfold collapseCoefficient
  change Legacy.TorusEndpoint.endpointSigma d / (4 * (d : ℝ) * (2 * Real.pi)^d) = _
  rw [← Legacy.TorusEndpoint.endpointSymbolConstant_mul_sigma hd]
  have hs := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hc := Legacy.TorusEndpoint.endpointSymbolConstant_pos hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  field_simp

theorem fourierEnergy_eq {d : ℕ} (ρ : ProbabilityDensity d) :
    Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = ∑' k, spectralTerm ρ k := by
  exact tsum_congr (Bridge.densitySpectralTerm_eq ρ)

theorem density_bound {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ (entropy ρ : EReal) := by
  have h := (Legacy.BecknerOnofri.endpoint_through_ten d hd hd10 (Bridge.density ρ) hρ).2
  rw [fourierEnergy_eq] at h
  change (d : ℝ) / spectralThreshold d * (∑' k, spectralTerm ρ k) ≤ entropy ρ at h
  rw [spectralEnergy_coe_eq_tsum (by omega) ρ hρ]
  exact_mod_cast h

theorem density_rigidity {d : ℕ} (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    ((((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal = (entropy ρ : EReal) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1) := by
  have h := Legacy.BecknerOnofri.endpoint_equality_iff_uniform hd hd10 (Bridge.density ρ) hρ
  rw [fourierEnergy_eq] at h
  change ((d : ℝ) / spectralThreshold d * (∑' k, spectralTerm ρ k) = entropy ρ ↔ _) at h
  rw [spectralEnergy_coe_eq_tsum (by omega) ρ hρ]
  exact_mod_cast h

theorem partition_eq {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    Legacy.BecknerOnofri.EndpointPotential.centeredPartition (Bridge.potentialLp u hu) =
      ∫ x, Real.exp (centered u x) ∂torusMeasure d := by
  have hr : (fun x => (Bridge.potentialLp u hu x).re) =ᵐ[torusMeasure d] u := by
    filter_upwards [Bridge.potentialLp_ae u hu] with x hx
    simp [hx]
  have hi := integral_congr_ae hr
  apply integral_congr_ae
  filter_upwards [hr] with x hx
  change Real.exp ((Bridge.potentialLp u hu x).re -
    ∫ y, (Bridge.potentialLp u hu y).re ∂torusMeasure d) = Real.exp (centered u x)
  simp only [centered, hx, hi]

theorem manuscriptEnergy_eq {d : ℕ} (hd : 0 < d) (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Legacy.BecknerOnofri.EndpointPotential.manuscriptEnergy (Bridge.potentialLp u hu.1) =
      potentialEnergy u := by
  rw [Legacy.BecknerOnofri.EndpointPotential.manuscriptEnergy_eq hd _
    (Bridge.potentialLp_summable hd u hu), Bridge.potentialLp_energy hd u hu]

theorem potential_bound {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  have h := (Legacy.BecknerOnofri.onofri_through_ten hd hd10
    (Bridge.potentialLp_real u hu.1) (Bridge.potentialLp_summable (by omega) u hu)).2
  rw [partition_eq, manuscriptEnergy_eq (by omega) u hu, ← coefficient_eq (by omega)] at h
  refine ⟨critical_exp_integrable (by omega) u hu zero_lt_one |>.congr (by simp), ?_⟩
  rw [logPartition_eq_log_integral (by omega) u hu]
  exact_mod_cast h

theorem potential_rigidity {d : ℕ} (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c) := by
  have h := Legacy.BecknerOnofri.onofri_equality_iff_constant hd hd10
    (Bridge.potentialLp_real u hu.1) (Bridge.potentialLp_summable (by omega) u hu)
  rw [partition_eq, manuscriptEnergy_eq (by omega) u hu, ← coefficient_eq (by omega)] at h
  rw [logPartition_eq_log_integral (by omega) u hu, EReal.coe_eq_coe_iff, h]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    filter_upwards [hc, Bridge.potentialLp_ae u hu.1] with x hx hu'
    have := congrArg Complex.re (hu'.symm.trans hx)
    simpa using this
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    filter_upwards [hc, Bridge.potentialLp_ae u hu.1] with x hx hu'
    simpa [hx] using hu'

#print axioms density_bound
#print axioms potential_rigidity
end LowDimension
end BecknerOnofri.HighDim
