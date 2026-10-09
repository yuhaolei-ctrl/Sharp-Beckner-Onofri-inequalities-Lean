module

public import BecknerOnofri.V2.Rearrangement.FiberPairing
public import BecknerOnofri.V2.Rearrangement.Equimeasurable
public import BecknerOnofri.V2.Vocab.HomEntropyTorus
public import BecknerOnofri.V2.Vocab.Normalization
public import BecknerOnofri.FiniteEntropyEnergy
public import BecknerOnofri.LegacyBridge
public import Legacy.BecknerOnofri.GreenPolarization

@[expose] public section

/-! # From heat pairings to the energy (written route, Lemma 2.9)

Manuscript: for bounded `r`, Plancherel gives
`∫ r e^{tΔ} r - 1 = ∑_{k≠0} e^{-4π²|k|²t}|r̂(k)|² ≥ 0`; integrating against
`t^{d/2-1} dt / Γ(d/2)` and Tonelli yield `eq:rearrangement`,
`‖r‖²_{Ḣ^{-d/2}} = Γ(d/2)⁻¹ ∫_0^∞ t^{d/2-1} (⟨r, P_t r⟩ - 1) dt`.  Consequently a pointwise-in-`t`
inequality `⟨r, P_t r⟩ ≤ ⟨s, P_t s⟩` implies `‖r‖² ≤ ‖s‖²`.

In the repository these two steps are
`CoordinatePolarization.centeredHeatPairing_hasSum` / `centeredHeatPairing_eq_sub_one`
(Plancherel for the heat quadratic form, performed at fixed finite `t` for the *subtracted* form
`pairing (heatKernel t (x-y) - 1)`), and `CoordinatePolarization.integral_mellinPairing`
(Tonelli against `t^{d/2-1}`, requiring summability of the spectral terms, which holds for finite
entropy).  Time scale: `Legacy theta τ` has multiplier `exp(-π τ n²)`, i.e. `τ = 4π t` in the
manuscript's `e^{-4π² n² t}`; the Mellin weight `τ^{d/2-1}` differs from `t^{d/2-1}` by the
constant `(4π)^{d/2}`, absorbed in the normalization constant of the repository's
`integral_mellinPairing`. -/

noncomputable section
open MeasureTheory Set
open Legacy.BecknerOnofri.CoordinatePolarization
open Legacy.BecknerOnofri.HeatDensityApproximation (heatKernel)
open scoped ENNReal

namespace BecknerOnofri.V2.Rearrangement
open BecknerOnofri.HighDim

variable {d : ℕ}

/-- The (real) spectral series of a finite-entropy density is summable. -/
theorem spectralTerm_summable (hd : 0 < d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    Summable (spectralTerm ρ) :=
  finiteEntropy_spectralTerm_summable hd ρ hρ

theorem spectralEnergy_eq_ofReal_tsum (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) : spectralEnergy ρ = ENNReal.ofReal (∑' k, spectralTerm ρ k) := by
  have hn (k : NonzeroFrequency d) : 0 ≤ spectralTerm ρ k := by
    unfold spectralTerm frequencyLength
    positivity
  unfold spectralEnergy
  rw [← ENNReal.ofReal_tsum_of_nonneg hn (spectralTerm_summable hd ρ hρ)]

/-- **Heat pairings control the energy.**  If `⟨ρ, P_τ ρ⟩ ≤ ⟨η, P_τ η⟩` for all `τ > 0`
(finite entropy on both sides) then `‖ρ‖²_{Ḣ^{-d/2}} ≤ ‖η‖²_{Ḣ^{-d/2}}`. -/
theorem spectralTerm_tsum_le_of_heat_pairing_le (hd : 0 < d) (ρ η : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (hη : η.FiniteEntropy)
    (h : ∀ τ : ℝ, 0 < τ →
      pairing (fun x y => heatKernel τ (x - y)) ρ.value ≤
        pairing (fun x y => heatKernel τ (x - y)) η.value) :
    ∑' k, spectralTerm ρ k ≤ ∑' k, spectralTerm η k := by
  have hsρ : Summable (Legacy.TorusEndpoint.densitySpectralTerm (Bridge.density ρ)) :=
    (spectralTerm_summable hd ρ hρ).congr (fun k => (Bridge.densitySpectralTerm_eq ρ k).symm)
  have hsη : Summable (Legacy.TorusEndpoint.densitySpectralTerm (Bridge.density η)) :=
    (spectralTerm_summable hd η hη).congr (fun k => (Bridge.densitySpectralTerm_eq η k).symm)
  have hi := integral_mono_ae (mellinPairing_integrable hd (Bridge.density ρ) hsρ)
    (mellinPairing_integrable hd (Bridge.density η) hsη) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := ht
      unfold mellinPairing
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht'.le _)
      rw [centeredHeatPairing_eq_sub_one (Bridge.density ρ) ht',
        centeredHeatPairing_eq_sub_one (Bridge.density η) ht']
      exact sub_le_sub_right (h t ht') 1)
  rw [integral_mellinPairing hd (Bridge.density ρ) hsρ,
    integral_mellinPairing hd (Bridge.density η) hsη] at hi
  have hσ : 0 < Legacy.TorusEndpoint.endpointSigma d := Legacy.TorusEndpoint.endpointSigma_pos hd
  unfold Legacy.TorusEndpoint.densitySpectralEnergy at hi
  have e1 : ∑' k, Legacy.TorusEndpoint.densitySpectralTerm (Bridge.density ρ) k = ∑' k, spectralTerm ρ k :=
    tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  have e2 : ∑' k, Legacy.TorusEndpoint.densitySpectralTerm (Bridge.density η) k = ∑' k, spectralTerm η k :=
    tsum_congr (Bridge.densitySpectralTerm_eq η)
  rw [e1, e2] at hi
  have := (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp hi
  exact (mul_le_mul_iff_of_pos_left (one_div_pos.mpr hσ)).mp this

theorem spectralEnergy_le_of_heat_pairing_le (hd : 0 < d) (ρ η : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (hη : η.FiniteEntropy)
    (h : ∀ τ : ℝ, 0 < τ →
      pairing (fun x y => heatKernel τ (x - y)) ρ.value ≤
        pairing (fun x y => heatKernel τ (x - y)) η.value) :
    spectralEnergy ρ ≤ spectralEnergy η := by
  rw [spectralEnergy_eq_ofReal_tsum hd ρ hρ, spectralEnergy_eq_ofReal_tsum hd η hη]
  exact ENNReal.ofReal_le_ofReal (spectralTerm_tsum_le_of_heat_pairing_le hd ρ η hρ hη h)

end BecknerOnofri.V2.Rearrangement
