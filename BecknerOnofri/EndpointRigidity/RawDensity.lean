module

public import BecknerOnofri.EndpointRigidity.MixtureInduction
public import BecknerOnofri.Uniform

@[expose] public section

/-! Exact extended-real Fourier-energy equality formulation, with the original
raw density domain and normalized Haar measure. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim
open CosineMixtureTransfer EndpointRigidity

theorem density_rigidity_from_twelve (h12 : MixtureEndpoint 12)
    (hRig12 : MixtureRigidity 12) {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  constructor
  · intro he
    have hEndpoint := finite_entropy_endpoint_from_mixture hd
      (mixture_endpoint_from_twelve h12 hd) (Bridge.density ρ) hρ
    have hraw : Bridge.rawDensity (Bridge.density ρ) = ρ := by cases ρ; rfl
    rw [← hraw, Bridge.rawDensity_spectralEnergy _ hEndpoint.1] at he
    have hQ : 0 ≤ Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) := by
      apply tsum_nonneg
      intro k
      unfold Legacy.TorusEndpoint.densitySpectralTerm
      exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
    have hEnt : 0 ≤ 2 * entropy (Bridge.rawDensity (Bridge.density ρ)) :=
      mul_nonneg (by norm_num) (entropy_nonneg _ hρ)
    have hreal := (ENNReal.ofReal_eq_ofReal_iff hQ hEnt).mp he
    apply uniform_from_twelve h12 hRig12 hd (Bridge.density ρ) hρ
    change Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = 2 * entropy ρ at hreal
    change (1/2:ℝ) * Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = entropy ρ
    linarith
  · intro he
    have hEnt : entropy ρ = 0 := (entropy_eq_zero_iff ρ hρ).mpr he
    have hCoeff (k : NonzeroFrequency d) : fourierCoeff ρ.value k.val = 0 := by
      rw [← fourierCoeff_one_nonzero k.val k.property]
      apply integral_congr_ae
      filter_upwards [he] with x hx
      simp only [hx]
    simp only [spectralEnergy, spectralTerm, hCoeff, norm_zero, zero_pow (by decide : 2 ≠ 0),
      ENNReal.ofReal_zero, tsum_zero, hEnt, mul_zero]

#print axioms density_rigidity_from_twelve
end BecknerOnofri.HighDim
