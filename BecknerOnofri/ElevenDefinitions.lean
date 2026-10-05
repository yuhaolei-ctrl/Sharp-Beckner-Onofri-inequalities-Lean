import BecknerOnofri.BranchDefinitions

/-! Definitions for the literal dimension-eleven statements in the September
21 manuscript. No regularity, normalization, certificate, or transition
conclusion is assumed by these definitions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace BecknerOnofri.HighDim.Eleven

/-- Representative in the same half-open cube as Section 4. -/
def representative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (p := (1 : ℝ)) (-(1 / 2 : ℝ)) x).val

def euclideanProfile (x : Fin 11 → ℝ) : ℝ :=
  (5 : ℝ)^11 * (122880 / Real.pi^6) *
    (1 + 25 * ∑ i : Fin 11, (x i)^2)^(-11 : ℤ)

/-- Exactly the periodized profile in (1.20)/(Section 4), not an arbitrary witness. -/
def periodizedProfile (x : Torus 11) : ℝ :=
  ∑' n : Frequency 11, euclideanProfile (fun i => representative (x i) + (n i : ℝ))

def fourierPolynomial (z : ℝ) : ℝ :=
  z^5 + 15*z^4 + 105*z^3 + 420*z^2 + 945*z + 945

def fourierProfile (z : ℝ) : ℝ := Real.exp (-z) * fourierPolynomial z / 945

/-- The global zero-pressure threshold is determined by the actual pressure. -/
def globalTransition : ℝ := sSup {β : ℝ | 0 ≤ β ∧ pressure 11 β = 0}

def zeroDefectCoefficient : ℝ :=
  spectralThreshold 11 / (2 * globalTransition * (2 * Real.pi)^11)

def pressureReal (β : ℝ) : ℝ := (pressure 11 β).toReal
def defectReal (A : ℝ) : ℝ := (coefficientDefect 11 A).toReal

/-- Raw free energy, used only for smooth positive perturbations when taking
derivatives. The relevant theorems must establish those analytic conditions. -/
def rawFreeEnergy (β : ℝ) (f : Torus 11 → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂torusMeasure 11) -
    β / (2 * spectralThreshold 11) *
      ∑' k : NonzeroFrequency 11,
        (frequencyLength k.val^11)⁻¹ * ‖fourierCoeff f k.val‖^2

def uniformHessian (β : ℝ) (h : Torus 11 → ℝ) : ℝ :=
  deriv (deriv (fun t : ℝ => rawFreeEnergy β (fun x => 1 + t * h x))) 0

end BecknerOnofri.HighDim.Eleven
