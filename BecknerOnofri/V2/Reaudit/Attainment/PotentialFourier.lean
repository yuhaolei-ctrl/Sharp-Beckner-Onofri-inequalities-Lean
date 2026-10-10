module

public import BecknerOnofri.V2.Reaudit.Attainment.Basic
public import BecknerOnofri.V2.Vocab.Section2Gibbs
public import BecknerOnofri.RawGapBridges
public import BecknerOnofri.OnsetSobolev
public import BecknerOnofri.V2.Onset.Bootstrap

@[expose] public section

/-! # Fourier coefficients of the density potential `u_ρ = β g * ρ` (package `Attainment`)

The potential identity `eq:intro-kernel` in Fourier variables, used in the Euler-Lagrange system
(`Regularity.lean`) and in the Fourier square completion (`GapIdentities.lean`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

/-- The Fourier coefficients of `β g * ρ`: for `k ≠ 0`, `|k|^d û_ρ(k) = (β/β_s) ρ̂(k)`
(the potential identity `eq:intro-kernel` in Fourier variables). -/
theorem fourierCoeff_densityPotential (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) {k : Frequency d} (hk : k ≠ 0) :
    (frequencyLength k : ℂ) ^ d * fourierCoeff (Gap.densityPotential β ρ.value) k =
      ((β / spectralThreshold d : ℝ) : ℂ) * fourierCoeff ρ.value k := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  set A' : ℝ := spectralThreshold d / (2 * β) with hA'
  have he := Gap.potential_ae hd hβ (Bridge.density ρ) hρ
  have hreal := (FiniteEntropyGreen.dualPotential_admissible hd A' (Bridge.density ρ) hρ).1
  have h1 : fourierCoeff (Gap.densityPotential β ρ.value) k =
      Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d
        (FiniteEntropyGreen.dualPotential hd A' (Bridge.density ρ) hρ) k := by
    rw [← OnsetSobolev.realValue_fourier _ hreal k]
    exact (fourierCoeff_congr_ae he k).symm
  rw [h1]
  unfold FiniteEntropyGreen.dualPotential
  rw [map_smul]
  change (frequencyLength k : ℂ) ^ d * (((1 / (2 * A') : ℝ) : ℂ) *
    Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d (FiniteEntropyGreen.potentialLp hd (Bridge.density ρ) hρ) k) = _
  rw [FiniteEntropyGreen.potentialLp_fourier hd (Bridge.density ρ) hρ k, if_neg hk]
  have hr : (0 : ℝ) < frequencyLength k ^ d := by
    have : 1 ≤ frequencyLength k := Onset.one_le_frequencyLength hk
    positivity
  have : Legacy.TorusEndpoint.densityFourier (Bridge.density ρ).value k = fourierCoeff ρ.value k := rfl
  rw [this]
  have hc : (1 / (2 * A') : ℝ) = β / spectralThreshold d := by
    rw [hA']; field_simp
  rw [hc]
  have hrc : (frequencyLength k : ℂ) ^ d ≠ 0 := by exact_mod_cast hr.ne'
  change (frequencyLength k : ℂ) ^ d * (((β / spectralThreshold d : ℝ) : ℂ) *
    (((1 / Legacy.TorusEndpoint.frequencyRadius k ^ d : ℝ) : ℂ) * fourierCoeff ρ.value k)) = _
  have : (((1 / Legacy.TorusEndpoint.frequencyRadius k ^ d : ℝ) : ℂ)) = ((frequencyLength k : ℂ) ^ d)⁻¹ := by
    push_cast; rw [one_div]; rfl
  rw [this]
  field_simp

end BecknerOnofri.V2.Reaudit.Attainment
