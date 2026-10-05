module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The first-order transition in dimension eleven

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

/-- The explicit dimension-eleven Euclidean trial density, with scale five and unit mass. -/
def euclideanProfile (x : Fin 11 → ℝ) : ℝ :=
  (5 : ℝ)^11 * (122880 / Real.pi^6) *
    (1 + 25 * ∑ i : Fin 11, (x i)^2)^(-11 : ℤ)

/-- Exactly the periodized profile in (1.20)/(Section 4), not an arbitrary witness. -/
def periodizedProfile (x : Torus 11) : ℝ :=
  ∑' n : Frequency 11, euclideanProfile (fun i => representative (x i) + (n i : ℝ))

/-- The degree-five polynomial in the closed-form Fourier transform of the trial profile. -/
def fourierPolynomial (z : ℝ) : ℝ :=
  z^5 + 15*z^4 + 105*z^3 + 420*z^2 + 945*z + 945

/-- The exponential-polynomial expression for that radial Fourier transform. -/
def fourierProfile (z : ℝ) : ℝ := Real.exp (-z) * fourierPolynomial z / 945

/-- The global zero-pressure threshold is determined by the actual pressure. -/
def globalTransition : ℝ := sSup {β : ℝ | 0 ≤ β ∧ pressure 11 β = 0}

/-- The reciprocal parameter corresponding to the global transition in dimension eleven. -/
def zeroDefectCoefficient : ℝ :=
  spectralThreshold 11 / (2 * globalTransition * (2 * Real.pi)^11)

/-- Real projection of the extended pressure; the corner theorem separately establishes finiteness. -/
def pressureReal (β : ℝ) : ℝ := (pressure 11 β).toReal
/-- Real projection of the extended defect; the corner theorem separately establishes finiteness. -/
def defectReal (A : ℝ) : ℝ := (coefficientDefect 11 A).toReal

/-- Raw free energy, used only for smooth positive perturbations when taking
derivatives. The relevant theorems must establish those analytic conditions. -/
def rawFreeEnergy (β : ℝ) (f : Torus 11 → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂torusMeasure 11) -
    β / (2 * spectralThreshold 11) *
      ∑' k : NonzeroFrequency 11,
        (frequencyLength k.val^11)⁻¹ * ‖fourierCoeff f k.val‖^2

/-- The actual second derivative of free energy along rho = 1 + t*h at t = 0. -/
def uniformHessian (β : ℝ) (h : Torus 11 → ℝ) : ℝ :=
  deriv (deriv (fun t : ℝ => rawFreeEnergy β (fun x => 1 + t * h x))) 0

end BecknerOnofri.HighDim.Eleven

namespace BecknerOnofri.Target
open HighDim MeasureTheory Set
open scoped ENNReal BigOperators ContDiff ComplexConjugate

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_profile_regular`. -/
theorem eleven_profile_regular :
    ∃ ρ : ProbabilityDensity 11, ρ.value = Eleven.periodizedProfile ∧
      ρ.FiniteEntropy ∧ SmoothOnTorus ρ.value ∧ ∀ x, 0 < ρ.value x := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_competitor_entropy`. -/
theorem eleven_competitor_entropy (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = Eleven.periodizedProfile) :
    entropy ρ < (8653 : ℝ)/600 := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_competitor_energy`. -/
theorem eleven_competitor_energy (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = Eleven.periodizedProfile) :
    ENNReal.ofReal (2*((14475384292906 : ℝ)/10^12)) < spectralEnergy ρ := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_spectral_pressure`. -/
theorem eleven_spectral_pressure :
    (1/30 : EReal) < pressure 11 (spectralThreshold 11) ∧
      coefficientDefect 11 (spectralCoefficient 11) = pressure 11 (spectralThreshold 11) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_transition_interval`. -/
theorem eleven_transition_interval :
    (3543 : ℝ)/200 < Eleven.globalTransition ∧
    Eleven.globalTransition < 2063/100 ∧
    (2063 : ℝ)/100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_uniform_unique`. -/
theorem eleven_uniform_unique (β : ℝ) (hβ : 0 ≤ β) (hβ₀ : β ≤ 3543/200)
    (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) :
    IsGlobalMinimizer β ρ ↔ ρ.value =ᵐ[torusMeasure 11] (fun _ => 1) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_coexistence`. -/
theorem eleven_coexistence :
    IsGlobalMinimizer Eleven.globalTransition (uniformDensity 11) ∧
    ∃ ρ : ProbabilityDensity 11, IsGlobalMinimizer Eleven.globalTransition ρ ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
      ¬ (ρ.value =ᵐ[torusMeasure 11] (fun _ => 1)) := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_uniform_hessian`. -/
theorem eleven_uniform_hessian :
    0 < 1 - Eleven.globalTransition / spectralThreshold 11 ∧
    ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
      (1 - Eleven.globalTransition / spectralThreshold 11) *
          (∫ x, (h x)^2 ∂torusMeasure 11) ≤ Eleven.uniformHessian Eleven.globalTransition h := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_pressure_corner`. -/
theorem eleven_pressure_corner :
    (∀ β : ℝ, 0 < β → β < 22 → pressure 11 β = (Eleven.pressureReal β : EReal)) ∧
    ¬ DifferentiableAt ℝ Eleven.pressureReal Eleven.globalTransition := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_defect_corner`. -/
theorem eleven_defect_corner :
    (∃ ε : ℝ, 0 < ε ∧ ε < Eleven.zeroDefectCoefficient ∧
      ∀ A : ℝ, |A - Eleven.zeroDefectCoefficient| < ε →
        coefficientDefect 11 A = (Eleven.defectReal A : EReal)) ∧
    ¬ DifferentiableAt ℝ Eleven.defectReal Eleven.zeroDefectCoefficient := by
  sorry

/-- Manuscript claim registered as `BecknerOnofri.Target.eleven_spectral_constants`. -/
theorem eleven_spectral_constants :
    spectralThreshold 11 = 64 * Real.pi^5 / 945 ∧
      (2063 : ℝ)/100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 := by
  sorry

end BecknerOnofri.Target
