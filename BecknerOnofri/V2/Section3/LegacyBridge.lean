module

public import BecknerOnofri.V2.Section3.Defs
public import BecknerOnofri.EndpointDuality
public import Legacy.BecknerOnofri.Endpoint

@[expose] public section

/-! # Dictionary between the manuscript quantities and the repository's legacy density vocabulary (G04)

For a high-dimension density `ρ` and a legacy density `r` with `ρ.value =ᵐ r.value`:

* `d c_d ‖ρ‖²_{Ḣ^{-d/2}} = endpointConstant d * fourierEnergy r` (given summability of the spectral
  terms of `r`), because `c_d β_s(d) = (2π)^d`, `spectralEnergy ρ = (2π)^d ‖ρ‖²`,
  `endpointConstant d = d / β_s(d)`;
* `Ent ρ = densityEntropy r.value`. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

theorem energy_real_eq_legacy (hd : 0 < d) (ρ : ProbabilityDensity d)
    (r : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hae : ρ.value =ᵐ[torusMeasure d] r.value)
    (hsum : Summable (Legacy.TorusEndpoint.densitySpectralTerm r)) :
    (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal =
      Legacy.BecknerOnofri.endpointConstant d * Legacy.BecknerOnofri.fourierEnergy r := by
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos' hd
  have hE : spectralEnergy ρ = ENNReal.ofReal (Legacy.BecknerOnofri.fourierEnergy r) := by
    rw [← Bridge.rawDensity_spectralEnergy r hsum]
    exact BecknerOnofri.V2.Rearrangement.spectralEnergy_congr_ae hae
  have hnn : 0 ≤ Legacy.BecknerOnofri.fourierEnergy r :=
    tsum_nonneg fun k => by
      unfold Legacy.TorusEndpoint.densitySpectralTerm
      exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hkey := kernelConstant_mul_negSobolevEnergy_toReal hd ρ
  rw [hE, ENNReal.toReal_ofReal hnn] at hkey
  rw [mul_assoc, hkey]
  have hc : Legacy.BecknerOnofri.endpointConstant d = (d : ℝ) / spectralThreshold d := rfl
  rw [hc]
  ring

theorem entropy_real_eq_legacy (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (r : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hae : ρ.value =ᵐ[torusMeasure d] r.value) :
    (torusEntropy ρ.value).toReal = Legacy.TorusEndpoint.densityEntropy r.value := by
  rw [← entropy_eq_toReal_torusEntropy ρ hρ]
  unfold entropy Legacy.TorusEndpoint.densityEntropy
  exact integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])

/-- Translation of the legacy endpoint (with a margin `g`) to the manuscript normalization. -/
theorem entropyBound_add_of_legacy (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (r : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hae : ρ.value =ᵐ[torusMeasure d] r.value)
    (hsum : Summable (Legacy.TorusEndpoint.densitySpectralTerm r)) {g : ℝ}
    (h : Legacy.BecknerOnofri.endpointConstant d * Legacy.BecknerOnofri.fourierEnergy r + g ≤
      Legacy.TorusEndpoint.densityEntropy r.value) :
    (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal + g ≤
      (torusEntropy ρ.value).toReal := by
  rw [energy_real_eq_legacy hd ρ r hae hsum, entropy_real_eq_legacy ρ hρ r hae]
  exact h

end BecknerOnofri.V2.Section3
