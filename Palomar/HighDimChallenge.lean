module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Sharp high-dimensional Beckner–Onofri inequalities and onset

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

/-! Exact coefficients in (1.28); definitions only. -/
namespace BecknerOnofri.HighDim

/-- Self-interaction coefficient of the reduced quartic form. -/
noncomputable def quarticA (d : ℕ) : ℝ :=
  -(1 / 4 : ℝ) + 1 / (4 * ((2 : ℝ) ^ d - 1))

/-- Interaction coefficient of two distinct first-shell coordinate modes. -/
noncomputable def quarticB (d : ℕ) : ℝ :=
  2 / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1)

/-- The negative quartic coefficient along the full equal-amplitude branch, in the manuscript normalization. -/
noncomputable def kappa (d : ℕ) : ℝ :=
  -(2 * quarticA d + ((d : ℝ) - 1) * quarticB d)

end BecknerOnofri.HighDim

/-!
Analytic objects needed to state (1.32)--(1.34). These are definitions, not
existence assumptions. Sobolev norms are used only together with the explicit
membership predicate, which includes summability of the actual Fourier series.
Translation tangent vectors are actual directional derivatives on the torus.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.HighDim

/-- Inhomogeneous Fourier summand defining the order-s Sobolev norm. -/
def sobolevTerm {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (k : Frequency d) : ℝ :=
  (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ s * ‖fourierCoeff u k‖ ^ 2

/-- L2 membership together with summability of the actual order-s Fourier norm series. -/
def InSobolev {d : ℕ} (s : ℝ) (u : Torus d → ℝ) : Prop :=
  MemLp u 2 (torusMeasure d) ∧ Summable (sobolevTerm s u)

/-- The square root of the inhomogeneous Fourier norm series, used together with InSobolev. -/
def sobolevNorm {d : ℕ} (s : ℝ) (u : Torus d → ℝ) : ℝ :=
  Real.sqrt (∑' k : Frequency d, sobolevTerm s u k)

/-- The Haar integral of the real potential is zero. -/
def MeanZero {d : ℕ} (u : Torus d → ℝ) : Prop :=
  (∫ x, u x ∂torusMeasure d) = 0

/-- Smoothness of the periodic lift from the unit torus to Euclidean coordinate space. -/
def SmoothOnTorus {d : ℕ} (u : Torus d → ℝ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : Fin d → ℝ => u (fun j => (x j : UnitAddCircle)))

/-- Translation of a torus function by x0. -/
def translate {d : ℕ} (u : Torus d → ℝ) (x₀ : Torus d) : Torus d → ℝ :=
  fun x => u (x - x₀)

/-- The unit integer frequency in coordinate j. -/
def axisFrequency {d : ℕ} (j : Fin d) : Frequency d :=
  fun i => if i = j then 1 else 0

/-- Derivative along the j-th one-parameter translation subgroup. -/
def coordinateDerivative {d : ℕ} (u : Torus d → ℝ) (j : Fin d) (x : Torus d) : ℝ :=
  deriv (fun t : ℝ => u (x + fun i => if i = j then (t : UnitAddCircle) else 0)) 0

/-- A real linear combination of the actual translation tangent vectors. -/
def tangentCombination {d : ℕ} (u : Torus d → ℝ) (a : Fin d → ℝ) : Torus d → ℝ :=
  fun x => ∑ j : Fin d, a j * coordinateDerivative u j x

/-- The normalized exponential density associated with a smooth potential. -/
def normalizedGibbs {d : ℕ} (u : Torus d → ℝ) : Torus d → ℝ :=
  fun x => Real.exp (u x) / (∫ y, Real.exp (u y) ∂torusMeasure d)

/-- Critical potential energy divided by (2*pi)^d. -/
def normalizedPotentialEnergy {d : ℕ} (u : Torus d → ℝ) : ℝ :=
  potentialEnergy u / (2 * Real.pi) ^ d

/-- Extended log-partition minus the inverse-temperature-scaled potential energy. -/
def dualFunctional {d : ℕ} (β : ℝ) (u : Torus d → ℝ) : EReal :=
  logPartition u - ((spectralThreshold d / (2 * β) * normalizedPotentialEnergy u : ℝ) : EReal)

/-- The quadratic Hessian of the actual log-partition minus Fourier energy. -/
def secondVariation {d : ℕ} (β : ℝ) (u h : Torus d → ℝ) : ℝ :=
  (∫ x, normalizedGibbs u x * (h x) ^ 2 ∂torusMeasure d) -
    (∫ x, normalizedGibbs u x * h x ∂torusMeasure d) ^ 2 -
      spectralThreshold d / β * normalizedPotentialEnergy h

/-- The density contribution to the extended variational pressure. -/
def pressureValue {d : ℕ} (β : ℝ) (ρ : ProbabilityDensity d) : EReal :=
  (β / (2 * spectralThreshold d) : ℝ) * (spectralEnergy ρ).toEReal -
    (entropy ρ : EReal)

/-- Finite entropy and attainment of the variational pressure, equivalently global free-energy minimality. -/
def IsGlobalMinimizer {d : ℕ} (β : ℝ) (ρ : ProbabilityDensity d) : Prop :=
  ρ.FiniteEntropy ∧ ∀ σ : ProbabilityDensity d, σ.FiniteEntropy →
    pressureValue β σ ≤ pressureValue β ρ

/-- The sum of coordinate cosines in the translated first Fourier shell. -/
def firstShellProfile {d : ℕ} (x₀ x : Torus d) : ℝ :=
  ∑ j : Fin d, (fourier (1 : ℤ) (x j - x₀ j)).re

/-- The positive onset parameter 1 - sigma_d / beta above the spectral threshold. -/
def onsetDelta (d : ℕ) (β : ℝ) : ℝ := 1 - spectralThreshold d / β

/-- Difference between the translated potential and its leading full-mode cosine profile. -/
def branchRemainder {d : ℕ} (β : ℝ) (u : Torus d → ℝ) (x₀ : Torus d) : Torus d → ℝ :=
  fun x => translate u x₀ x -
    2 * Real.sqrt (onsetDelta d β / kappa d) * firstShellProfile x₀ x

/-- A smooth full-coordinate stationary orbit with a Morse--Bott maximum:
the Hessian kernel is exactly the d independent translation directions, with
a strictly negative normal Hessian, and the actual functional is locally
maximal in each H^s topology above the algebra threshold. -/
structure FullModeMorseBott {d : ℕ} (β : ℝ) (u : Torus d → ℝ) : Prop where
  smooth : SmoothOnTorus u
  sobolev : ∀ s : ℝ, 0 ≤ s → InSobolev s u
  criticalSobolev : InCriticalSobolev u
  meanZero : MeanZero u
  stationary : ∀ k : NonzeroFrequency d,
    (frequencyLength k.val ^ d : ℂ) * fourierCoeff u k.val =
      (β / spectralThreshold d : ℝ) * fourierCoeff (normalizedGibbs u) k.val
  fullModes : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0
  tangentIndependent : ∀ a : Fin d → ℝ,
    tangentCombination u a =ᵐ[torusMeasure d] (fun _ => 0) → a = 0
  hessianNonpos : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
    secondVariation β u h ≤ 0
  hessianKernel : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
    (secondVariation β u h = 0 ↔
      ∃ a : Fin d → ℝ, h =ᵐ[torusMeasure d] tangentCombination u a)
  normalCoercivity : ∃ c : ℝ, 0 < c ∧
    ∀ h : Torus d → ℝ, InCriticalSobolev h → InSobolev ((d : ℝ) / 2) h →
      MeanZero h → (∀ j : Fin d,
        (∫ x, h x * coordinateDerivative u j x ∂torusMeasure d) = 0) →
      secondVariation β u h ≤ -c * sobolevNorm ((d : ℝ) / 2) h ^ 2
  localMaximum : ∀ s : ℝ, (d : ℝ) / 2 < s →
    ∃ r : ℝ, 0 < r ∧ ∀ v : Torus d → ℝ,
      InSobolev s v → InCriticalSobolev v → MeanZero v →
      InSobolev s (fun x => v x - u x) →
      sobolevNorm s (fun x => v x - u x) < r → dualFunctional β v ≤ dualFunctional β u

/-- Full content of the translation-orbit and uniform Sobolev profile assertions.
The same family works for every s, but the O constants and neighborhoods may
depend on s, as the source specifies for every fixed Sobolev index. -/
def FullBranchOnset (d : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ U : ℝ → Torus d → ℝ,
    (∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
      FullModeMorseBott β (U β) ∧
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ ↔
        ∃ x₀ : Torus d, ρ.value =ᵐ[torusMeasure d] normalizedGibbs (translate (U β) x₀))) ∧
    (∀ s : ℝ, 0 ≤ s → ∃ η C : ℝ, 0 < η ∧ η ≤ ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + η →
        ∀ x₀ : Torus d,
          InSobolev s (branchRemainder β (U β) x₀) ∧
          sobolevNorm s (branchRemainder β (U β) x₀) ≤ C * onsetDelta d β)

end BecknerOnofri.HighDim

namespace BecknerOnofri.Target
open HighDim MeasureTheory Set
open scoped ENNReal BigOperators ContDiff ComplexConjugate

/-- Manuscript claim registered as `BecknerOnofri.Target.density_endpoint`. -/
theorem density_endpoint (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.density_rigidity`. -/
theorem density_rigidity (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.potential_endpoint`. -/
theorem potential_endpoint (d : ℕ) (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.potential_rigidity`. -/
theorem potential_rigidity (d : ℕ) (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] (fun _ => c) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.pressure_threshold`. -/
theorem pressure_threshold (d : ℕ) (hd : 12 ≤ d) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.coefficient_threshold`. -/
theorem coefficient_threshold (d : ℕ) (hd : 12 ≤ d) :
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.kappa_positive`. -/
theorem kappa_positive (d : ℕ) (hd : 12 ≤ d) : 0 < kappa d := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.full_branch_onset`. -/
theorem full_branch_onset (d : ℕ) (hd : 12 ≤ d) : FullBranchOnset d := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.pressure_onset`. -/
theorem pressure_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.coefficient_onset`. -/
theorem coefficient_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 := by
  sorry

end BecknerOnofri.Target
