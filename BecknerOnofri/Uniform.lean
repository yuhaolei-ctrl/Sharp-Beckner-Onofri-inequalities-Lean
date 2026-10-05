module

public import BecknerOnofri.Definitions

@[expose] public section

/-! The actual uniform Haar density attains the spectral endpoint equality. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.HighDim

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

@[simp] theorem uniformDensity_value (d : ℕ) (x : Torus d) :
    (uniformDensity d).value x = 1 := rfl

theorem uniformDensity_finiteEntropy (d : ℕ) :
    (uniformDensity d).FiniteEntropy := by
  simp [ProbabilityDensity.FiniteEntropy, uniformDensity]

@[simp] theorem uniformDensity_entropy (d : ℕ) :
    entropy (uniformDensity d) = 0 := by
  simp [entropy, uniformDensity]

theorem fourierCoeff_one_nonzero {d : ℕ} (k : Frequency d) (hk : k ≠ 0) :
    fourierCoeff (fun _ : Torus d => 1) k = 0 := by
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin d))) k 0
  simp only [ContinuousMap.inner_toLp, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul, ← UnitAddTorus.mFourier_neg, if_neg hk] at h
  simpa [fourierCoeff, torusMeasure, volume] using h

@[simp] theorem uniformDensity_fourierCoeff_zero (d : ℕ) :
    fourierCoeff (uniformDensity d).value 0 = 1 := by
  simp [fourierCoeff, uniformDensity, UnitAddTorus.mFourier_zero]

theorem uniformDensity_fourierCoeff_nonzero {d : ℕ} (k : Frequency d) (hk : k ≠ 0) :
    fourierCoeff (uniformDensity d).value k = 0 :=
  fourierCoeff_one_nonzero k hk

@[simp] theorem uniformDensity_spectralTerm {d : ℕ} (k : NonzeroFrequency d) :
    spectralTerm (uniformDensity d) k = 0 := by
  simp [spectralTerm, uniformDensity_fourierCoeff_nonzero k.val k.property]

@[simp] theorem uniformDensity_spectralEnergy (d : ℕ) :
    spectralEnergy (uniformDensity d) = 0 := by
  simp [spectralEnergy]

theorem uniformDensity_endpoint_equality (d : ℕ) :
    spectralEnergy (uniformDensity d) = ENNReal.ofReal (2 * entropy (uniformDensity d)) := by
  simp

end BecknerOnofri.HighDim
