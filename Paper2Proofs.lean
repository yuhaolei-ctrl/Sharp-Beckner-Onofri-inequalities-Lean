import Paper2Definitions
import BecknerOnofri.ExtendedEntropy
import BecknerOnofri.EntropyMainTheorems

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace BecknerOnofri.Paper2
open HighDim

theorem negativeSobolevEnergy_normalization {d : ℕ} (ρ : ProbabilityDensity d) :
    ENNReal.ofReal ((2 * Real.pi) ^ d) * negativeSobolevEnergy ρ =
      spectralEnergy ρ := by
  have hp : 0 < (2 * Real.pi) ^ d := by positivity
  simp [negativeSobolevEnergy, ← mul_assoc, ENNReal.mul_inv_cancel,
    ne_of_gt (ENNReal.ofReal_pos.mpr hp)]

theorem negativeSobolevEnergy_fourier {d : ℕ} (ρ : ProbabilityDensity d) :
    negativeSobolevEnergy ρ = negativeSobolevFourierSeries ρ := by
  unfold negativeSobolevEnergy spectralEnergy negativeSobolevFourierSeries
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  have hn : 0 < frequencyLength k.val :=
    Legacy.TorusEndpoint.frequencyRadius_pos k.property
  have hp : 0 ≤ (2 * Real.pi) ^ d := by positivity
  rw [spectralTerm, ENNReal.ofReal_mul (inv_nonneg.mpr (pow_pos hn d).le),
    ENNReal.ofReal_inv_of_pos (pow_pos hn d),
    mul_pow (2 * Real.pi) (frequencyLength k.val) d,
    ENNReal.ofReal_inv_of_pos (mul_pos (by positivity) (pow_pos hn d)),
    ENNReal.ofReal_mul hp, ENNReal.mul_inv]
  · ac_rfl
  all_goals simp

theorem low_density_extended (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) *
      (ENNReal.ofReal ((2 * Real.pi) ^ d) * negativeSobolevEnergy ρ).toEReal ≤
        extendedEntropy ρ := by
  rw [negativeSobolevEnergy_normalization]
  exact HighDim.low_density_extended hd hd10 ρ

theorem high_density_extended (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) :
    ((1 / 2 : ℝ) : EReal) *
      (ENNReal.ofReal ((2 * Real.pi) ^ d) * negativeSobolevEnergy ρ).toEReal ≤
        extendedEntropy ρ := by
  rw [negativeSobolevEnergy_normalization]
  by_cases hρ : ρ.FiniteEntropy
  · rw [extendedEntropy_eq ρ hρ, spectralEnergy_coe_eq_tsum (by omega) ρ hρ]
    have hent := entropy_nonneg ρ hρ
    have he := Target.density_endpoint d hd ρ hρ
    have he' := EReal.coe_ennreal_le_coe_ennreal_iff.mpr he
    rw [spectralEnergy_coe_eq_tsum (by omega) ρ hρ,
      EReal.coe_ennreal_ofReal, max_eq_left] at he'
    · have hb : (∑' k, spectralTerm ρ k) ≤ 2 * entropy ρ := by exact_mod_cast he'
      exact_mod_cast (show (1 / 2 : ℝ) * (∑' k, spectralTerm ρ k) ≤ entropy ρ by linarith)
    · exact_mod_cast (show (0 : ℝ) ≤ 2 * entropy ρ by positivity)
  · rw [extendedEntropy_top ρ hρ]
    exact le_top

theorem physicalSpectralPowerGraph_scaling {d : ℕ}
    (α : Friedrichs.MixedSpatial.MultiIndex d) (s : ℝ)
    (f g : Friedrichs.MixedSpatial.H α)
    (h : Friedrichs.MixedSpatial.SpectralPowerGraph α s f g) :
    physicalSpectralPowerGraph α s f (((2 * Real.pi) ^ 2) ^ s • g) := by
  intro n
  simp only [inner_smul_left, conj_trivial, h n]
  rw [Real.mul_rpow (by positivity) (by
    unfold Friedrichs.MixedSpatial.mixedEigenvalue
    positivity)]
  ring

end BecknerOnofri.Paper2
