module

public import BecknerOnofri.BranchDefinitions

@[expose] public section

/-! Definitions for the literal dimension-eleven statements in the September
21 manuscript. No regularity, normalization, certificate, or transition
conclusion is assumed by these definitions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace BecknerOnofri.HighDim.Eleven

def fourierPolynomial (z : ℝ) : ℝ :=
  z^5 + 15*z^4 + 105*z^3 + 420*z^2 + 945*z + 945

def fourierProfile (z : ℝ) : ℝ := Real.exp (-z) * fourierPolynomial z / 945

/-- The global zero-pressure threshold is determined by the actual pressure. -/
def globalTransition : ℝ := sSup {β : ℝ | 0 ≤ β ∧ pressure 11 β = 0}

def zeroDefectCoefficient : ℝ :=
  spectralThreshold 11 / (2 * globalTransition * (2 * Real.pi)^11)

def pressureReal (β : ℝ) : ℝ := (pressure 11 β).toReal
def defectReal (A : ℝ) : ℝ := (coefficientDefect 11 A).toReal

end BecknerOnofri.HighDim.Eleven
