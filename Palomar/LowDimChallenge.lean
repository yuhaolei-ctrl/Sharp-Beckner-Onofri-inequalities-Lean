module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Sharp low-dimensional Beckner–Onofri inequalities

The complete mathematical definitions used below are included here.
Only Mathlib modules are imported. These are statement placeholders; the
corresponding proof entrypoint never imports this Challenge.
-/

@[expose] public section

/-!
Trusted analytic definitions for the high-dimensional endpoint.

The measure is actual normalized Haar measure on (R/Z)^d. Frequencies use
the Euclidean length, not the default maximum norm on a function type.
Infinite spectral energies use ENNReal; a divergent series is never silently
replaced by the default real `tsum` value. No analytic bound is a field of
the probability-density or Sobolev-domain definitions.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.HighDim

/-- The unit flat torus (R/Z)^d, with each circle of period one. -/
abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)
/-- An integer Fourier frequency in dimension d. -/
abbrev Frequency (d : ℕ) := Fin d → ℤ
/-- The nonzero integer frequencies; the constant mode is excluded. -/
abbrev NonzeroFrequency (d : ℕ) := {k : Frequency d // k ≠ 0}

/-- Product normalized Haar measure on the unit torus. -/
def torusMeasure (d : ℕ) : Measure (Torus d) :=
  Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)

instance (d : ℕ) : IsProbabilityMeasure (torusMeasure d) := by
  unfold torusMeasure
  infer_instance

/-- Fourier coefficient with character exp(-2*pi*i*k.x), against Haar probability measure. -/
def fourierCoeff {d : ℕ} (f : Torus d → ℝ) (k : Frequency d) : ℂ :=
  ∫ x, UnitAddTorus.mFourier (-k) x * (f x : ℂ) ∂torusMeasure d

/-- Euclidean length of the integer frequency, not the coordinate maximum norm. -/
def frequencyLength {d : ℕ} (k : Frequency d) : ℝ :=
  Real.sqrt (∑ i : Fin d, (k i : ℝ) ^ 2)

/-- An almost-everywhere nonnegative, integrable real density of total mass one. -/
structure ProbabilityDensity (d : ℕ) where
  value : Torus d → ℝ
  nonneg : ∀ᵐ x ∂torusMeasure d, 0 ≤ value x
  integrable : Integrable value (torusMeasure d)
  mass : (∫ x, value x ∂torusMeasure d) = 1

/-- The constant probability density one. -/
def uniformDensity (d : ℕ) : ProbabilityDensity d where
  value := fun _ => 1
  nonneg := Filter.Eventually.of_forall (fun _ => zero_le_one)
  integrable := integrable_const 1
  mass := by simp

/-- Absolute integrability of rho log rho; this excludes default values of divergent real integrals. -/
def ProbabilityDensity.FiniteEntropy {d : ℕ} (ρ : ProbabilityDensity d) : Prop :=
  Integrable (fun x => ρ.value x * Real.log (ρ.value x)) (torusMeasure d)

/-- The integral of rho log rho, used in the conclusions below under finite-entropy hypotheses. -/
def entropy {d : ℕ} (ρ : ProbabilityDensity d) : ℝ :=
  ∫ x, ρ.value x * Real.log (ρ.value x) ∂torusMeasure d

/-- The nonzero Fourier-energy summand |k|^(-d) times |rho_hat(k)|^2. -/
def spectralTerm {d : ℕ} (ρ : ProbabilityDensity d)
    (k : NonzeroFrequency d) : ℝ :=
  (frequencyLength k.val ^ d)⁻¹ * ‖fourierCoeff ρ.value k.val‖ ^ 2

/-- Extended nonnegative Fourier energy; a divergent series has value infinity. -/
def spectralEnergy {d : ℕ} (ρ : ProbabilityDensity d) : ℝ≥0∞ :=
  ∑' k : NonzeroFrequency d, ENNReal.ofReal (spectralTerm ρ k)

/-- The critical Sobolev-energy summand (2*pi*|k|)^d times |u_hat(k)|^2. -/
def potentialTerm {d : ℕ} (u : Torus d → ℝ)
    (k : NonzeroFrequency d) : ℝ :=
  (2 * Real.pi * frequencyLength k.val) ^ d * ‖fourierCoeff u k.val‖ ^ 2

/-- Fourier definition of the real critical Sobolev space on the unit torus. -/
def InCriticalSobolev {d : ℕ} (u : Torus d → ℝ) : Prop :=
  MemLp u 2 (torusMeasure d) ∧ Summable (potentialTerm u)

/-- Critical Sobolev energy; all inequalities below require summability through InCriticalSobolev. -/
def potentialEnergy {d : ℕ} (u : Torus d → ℝ) : ℝ :=
  ∑' k : NonzeroFrequency d, potentialTerm u k

/-- Subtract the Haar mean of the potential. -/
def centered {d : ℕ} (u : Torus d → ℝ) (x : Torus d) : ℝ :=
  u x - ∫ y, u y ∂torusMeasure d

/-- Extended logarithm of the exponential integral of the centered potential. -/
def logPartition {d : ℕ} (u : Torus d → ℝ) : EReal :=
  ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (centered u x)) ∂torusMeasure d)

/-- The coefficient 1 / (2*(2*pi)^d) fixed by the first Fourier shell. -/
def spectralCoefficient (d : ℕ) : ℝ := 1 / (2 * (2 * Real.pi) ^ d)

/-- The inverse-temperature threshold 2*pi^(d/2)/Gamma(d/2) fixed by the first shell. -/
def spectralThreshold (d : ℕ) : ℝ :=
  2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)

/-- Pressure has its full extended-real supremum, including divergent energies. -/
def pressure (d : ℕ) (β : ℝ) : EReal :=
  ⨆ ρ : ProbabilityDensity d, ⨆ (_ : ρ.FiniteEntropy),
    (β / (2 * spectralThreshold d) : ℝ) * (spectralEnergy ρ).toEReal -
      (entropy ρ : EReal)

/-- Optimal additive defect, as an extended-real supremum over the full critical Sobolev domain. -/
def coefficientDefect (d : ℕ) (A : ℝ) : EReal :=
  ⨆ u : Torus d → ℝ, ⨆ (_ : InCriticalSobolev u),
    logPartition u - (A * potentialEnergy u : ℝ)

end BecknerOnofri.HighDim

/-! The collapse coefficient in the same Fourier normalization as the
trusted raw-function statements. Since c_d σ_d = (2π)^d, this is 1/(4d c_d).
This file contains definitions only. -/
namespace BecknerOnofri.HighDim
/-- The sharp low-dimensional potential coefficient sigma_d / (4*d*(2*pi)^d). -/
noncomputable def collapseCoefficient (d : ℕ) : ℝ :=
  spectralThreshold d / (4 * (d : ℝ) * (2 * Real.pi)^d)
end BecknerOnofri.HighDim

namespace BecknerOnofri.Target
open HighDim MeasureTheory Set
open scoped ENNReal BigOperators ContDiff ComplexConjugate

/-- Manuscript claim registered as `BecknerOnofri.Target.low_density_endpoint`. -/
theorem low_density_endpoint (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ (entropy ρ : EReal) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.low_potential_endpoint`. -/
theorem low_potential_endpoint (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.low_density_rigidity`. -/
theorem low_density_rigidity (d : ℕ) (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    ((((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal = (entropy ρ : EReal) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.low_potential_rigidity`. -/
theorem low_potential_rigidity (d : ℕ) (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.low_circle_potential`. -/
theorem low_circle_potential (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    (logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x => -2 * Real.log ‖1-conj a*fourier 1 (x 0)‖+c) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.low_circle_density`. -/
theorem low_circle_density (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    ((((1 : ℝ) / spectralThreshold 1 : ℝ) : EReal) * (spectralEnergy ρ).toEReal = (entropy ρ : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ρ.value =ᵐ[torusMeasure 1]
        fun x => (1-‖a‖^2)/‖fourier 1 (x 0)-a‖^2) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.low_coefficient_sharp`. -/
theorem low_coefficient_sharp (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.low_pressure_formula`. -/
theorem low_pressure_formula (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) (β : ℝ) :
    pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤ := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.low_coefficient_formula`. -/
theorem low_coefficient_formula (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) (A : ℝ) :
    coefficientDefect d A = if collapseCoefficient d ≤ A then 0 else ⊤ := by
  sorry

end BecknerOnofri.Target
