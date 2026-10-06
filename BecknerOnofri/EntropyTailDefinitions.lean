module

public import BecknerOnofri.Definitions
public import Mathlib.NumberTheory.Harmonic.Defs

@[expose] public section

/-! The actual scalar Fourier tail and matching harmonic budget in the
2026-09-21 manuscript. No numerical or analytic estimate is assumed here. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

def scalarCoefficient (n j : ℕ) : ℝ :=
  ((2*n).choose (n+j) : ℝ) / ((2*n).choose n : ℝ)

def outsideCube (k : Frequency 12) : Prop := ∃ i : Fin 12, 1 < (k i).natAbs

instance (k : Frequency 12) : Decidable (outsideCube k) := Classical.propDecidable _

def scalarTailWeight (k : Frequency 12) : ℝ :=
  if outsideCube k then (frequencyLength k ^ 12)⁻¹ else 0

def scalarTail (n : ℕ) : ℝ :=
  ∑' k : Frequency 12, scalarTailWeight k * ∏ i : Fin 12, scalarCoefficient n (k i).natAbs

def scalarBudget (n : ℕ) : ℝ :=
  12*((21/500)*scalarCoefficient n 2+
    (67/100)*((harmonic n : ℝ)-2*scalarCoefficient n 1-scalarCoefficient n 2))

/-- The weighted Gaussian sum over the complement of the frequency cube. -/
def gaussianTail (η : ℝ) : ℝ :=
  ∑' k : Frequency 12, scalarTailWeight k *
    Real.exp (-η * ∑ i : Fin 12, (k i : ℝ)^2)

/-- The heat sum after removing the complete frequency cube. -/
def heatComplement (s : ℝ) : ℝ :=
  (∑' j : ℤ, Real.exp (-s * (j : ℝ)^2))^12 - (1+2*Real.exp (-s))^12

end BecknerOnofri.HighDim.EntropyTail
