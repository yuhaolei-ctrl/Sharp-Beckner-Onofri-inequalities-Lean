import BecknerOnofri.Definitions
import BecknerOnofri.Constants
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic

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

def sobolevTerm {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (k : Frequency d) : ℝ :=
  (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ s * ‖fourierCoeff u k‖ ^ 2

def InSobolev {d : ℕ} (s : ℝ) (u : Torus d → ℝ) : Prop :=
  MemLp u 2 (torusMeasure d) ∧ Summable (sobolevTerm s u)

def sobolevNorm {d : ℕ} (s : ℝ) (u : Torus d → ℝ) : ℝ :=
  Real.sqrt (∑' k : Frequency d, sobolevTerm s u k)

def MeanZero {d : ℕ} (u : Torus d → ℝ) : Prop :=
  (∫ x, u x ∂torusMeasure d) = 0

def SmoothOnTorus {d : ℕ} (u : Torus d → ℝ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : Fin d → ℝ => u (fun j => (x j : UnitAddCircle)))

def translate {d : ℕ} (u : Torus d → ℝ) (x₀ : Torus d) : Torus d → ℝ :=
  fun x => u (x - x₀)

def axisFrequency {d : ℕ} (j : Fin d) : Frequency d :=
  fun i => if i = j then 1 else 0

def coordinateDerivative {d : ℕ} (u : Torus d → ℝ) (j : Fin d) (x : Torus d) : ℝ :=
  deriv (fun t : ℝ => u (x + fun i => if i = j then (t : UnitAddCircle) else 0)) 0

def tangentCombination {d : ℕ} (u : Torus d → ℝ) (a : Fin d → ℝ) : Torus d → ℝ :=
  fun x => ∑ j : Fin d, a j * coordinateDerivative u j x

def normalizedGibbs {d : ℕ} (u : Torus d → ℝ) : Torus d → ℝ :=
  fun x => Real.exp (u x) / (∫ y, Real.exp (u y) ∂torusMeasure d)

def normalizedPotentialEnergy {d : ℕ} (u : Torus d → ℝ) : ℝ :=
  potentialEnergy u / (2 * Real.pi) ^ d

def dualFunctional {d : ℕ} (β : ℝ) (u : Torus d → ℝ) : EReal :=
  logPartition u - ((spectralThreshold d / (2 * β) * normalizedPotentialEnergy u : ℝ) : EReal)

/-- The quadratic Hessian of the actual log-partition minus Fourier energy. -/
def secondVariation {d : ℕ} (β : ℝ) (u h : Torus d → ℝ) : ℝ :=
  (∫ x, normalizedGibbs u x * (h x) ^ 2 ∂torusMeasure d) -
    (∫ x, normalizedGibbs u x * h x ∂torusMeasure d) ^ 2 -
      spectralThreshold d / β * normalizedPotentialEnergy h

def pressureValue {d : ℕ} (β : ℝ) (ρ : ProbabilityDensity d) : EReal :=
  (β / (2 * spectralThreshold d) : ℝ) * (spectralEnergy ρ).toEReal -
    (entropy ρ : EReal)

def IsGlobalMinimizer {d : ℕ} (β : ℝ) (ρ : ProbabilityDensity d) : Prop :=
  ρ.FiniteEntropy ∧ ∀ σ : ProbabilityDensity d, σ.FiniteEntropy →
    pressureValue β σ ≤ pressureValue β ρ

def firstShellProfile {d : ℕ} (x₀ x : Torus d) : ℝ :=
  ∑ j : Fin d, (fourier (1 : ℤ) (x j - x₀ j)).re

def onsetDelta (d : ℕ) (β : ℝ) : ℝ := 1 - spectralThreshold d / β

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
