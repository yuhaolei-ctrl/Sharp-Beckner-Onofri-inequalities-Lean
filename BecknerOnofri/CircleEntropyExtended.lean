module

public import BecknerOnofri.ExtendedEntropy
public import BecknerOnofri.CirclePositiveEnergy

@[expose] public section

/-! The circle entropy inequality including infinite entropy and divergent
positive-frequency series, with neither replaced by a default real integral. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BecknerOnofri.HighDim

theorem circle_entropy_extended (ρ : ProbabilityDensity 1) :
    (circlePositiveEnergy ρ).toEReal ≤ extendedEntropy ρ := by
  have hσ : spectralThreshold 1 = 2 := Legacy.BecknerOnofri.endpointSigma_one
  have hfull : (2:EReal)*(circlePositiveEnergy ρ).toEReal ≤ (spectralEnergy ρ).toEReal := by
    have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr (circlePositiveEnergy_twice_le ρ)
    rw [EReal.coe_ennreal_mul] at h
    exact h
  calc
    _ = ((1/2:ℝ):EReal)*((2:EReal)*(circlePositiveEnergy ρ).toEReal) := by
      rw [← mul_assoc]
      have hc : ((1/2:ℝ):EReal)*(2:EReal) = (1:EReal) := by
        change ((1/2:ℝ):EReal)*((2:ℝ):EReal) = ((1:ℝ):EReal)
        rw [← EReal.coe_mul]
        norm_num
      rw [hc, one_mul]
    _ ≤ ((1/2:ℝ):EReal)*(spectralEnergy ρ).toEReal :=
      mul_le_mul_of_nonneg_left hfull (by norm_num)
    _ ≤ extendedEntropy ρ := by
      simpa only [Nat.cast_one, hσ] using low_density_extended (d := 1) (by omega) (by omega) ρ

#print axioms circle_entropy_extended
end BecknerOnofri.HighDim
