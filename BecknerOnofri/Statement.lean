/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Statement vocabulary

The definitions used by the statements of `Challenge.lean`. The block between the
`BEGIN VOCABULARY` and `END VOCABULARY` markers is a verbatim copy of the same block of
`Challenge.lean`, with the same imports (`scripts/check_vocabulary.py` enforces this), so
the challenge and the proof development elaborate exactly the same constants, including
the auxiliary proofs that the module system abstracts out of definition bodies.
-/

@[expose] public section

-- BEGIN VOCABULARY
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.HighDim

/-- The flat torus `𝕋ᵈ = ℝᵈ/ℤᵈ`. -/
abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)
/-- Integer frequencies `k ∈ ℤᵈ`. -/
abbrev Frequency (d : ℕ) := Fin d → ℤ
/-- Nonzero integer frequencies `k ∈ ℤᵈ \ {0}`. -/
abbrev NonzeroFrequency (d : ℕ) := {k : Frequency d // k ≠ 0}

/-- Normalized Haar measure `m_d` on `𝕋ᵈ`, the product of the normalized Haar
measures on the unit circle. -/
def torusMeasure (d : ℕ) : Measure (Torus d) :=
  Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)

instance (d : ℕ) : IsProbabilityMeasure (torusMeasure d) := by
  unfold torusMeasure
  infer_instance

/-- The Fourier coefficient `f̂(k) = ∫ f(x) e^{-2πik·x} dm_d(x)`. -/
def fourierCoeff {d : ℕ} (f : Torus d → ℝ) (k : Frequency d) : ℂ :=
  ∫ x, UnitAddTorus.mFourier (-k) x * (f x : ℂ) ∂torusMeasure d

/-- The Euclidean length `|k|` of a frequency. -/
def frequencyLength {d : ℕ} (k : Frequency d) : ℝ :=
  Real.sqrt (∑ i : Fin d, (k i : ℝ) ^ 2)

/-- A probability density with respect to `m_d`: an a.e. nonnegative integrable
function of total mass one. -/
structure ProbabilityDensity (d : ℕ) where
  /-- The density function. -/
  value : Torus d → ℝ
  nonneg : ∀ᵐ x ∂torusMeasure d, 0 ≤ value x
  integrable : Integrable value (torusMeasure d)
  mass : (∫ x, value x ∂torusMeasure d) = 1

/-- The uniform density `ρ ≡ 1`. -/
def uniformDensity (d : ℕ) : ProbabilityDensity d where
  value := fun _ => 1
  nonneg := Filter.Eventually.of_forall (fun _ => zero_le_one)
  integrable := integrable_const 1
  mass := by simp

/-- Finite entropy: `ρ log ρ` is integrable. -/
def ProbabilityDensity.FiniteEntropy {d : ℕ} (ρ : ProbabilityDensity d) : Prop :=
  Integrable (fun x => ρ.value x * Real.log (ρ.value x)) (torusMeasure d)

/-- The entropy `Ent(ρ) = ∫ ρ log ρ dm_d` (meaningful under `FiniteEntropy`). -/
def entropy {d : ℕ} (ρ : ProbabilityDensity d) : ℝ :=
  ∫ x, ρ.value x * Real.log (ρ.value x) ∂torusMeasure d

/-- The term `|k|^{-d} |ρ̂(k)|²`. -/
def spectralTerm {d : ℕ} (ρ : ProbabilityDensity d)
    (k : NonzeroFrequency d) : ℝ :=
  (frequencyLength k.val ^ d)⁻¹ * ‖fourierCoeff ρ.value k.val‖ ^ 2

/-- The energy `Σ_{k ≠ 0} |k|^{-d} |ρ̂(k)|² = (2π)^d ‖ρ‖²_{Ḣ^{-d/2}}`, as an
extended nonnegative sum (a divergent series has value `∞`). -/
def spectralEnergy {d : ℕ} (ρ : ProbabilityDensity d) : ℝ≥0∞ :=
  ∑' k : NonzeroFrequency d, ENNReal.ofReal (spectralTerm ρ k)

/-- The term `(2π|k|)^d |û(k)|²`. -/
def potentialTerm {d : ℕ} (u : Torus d → ℝ)
    (k : NonzeroFrequency d) : ℝ :=
  (2 * Real.pi * frequencyLength k.val) ^ d * ‖fourierCoeff u k.val‖ ^ 2

/-- Membership in the real critical Sobolev space `H^{d/2}(𝕋ᵈ)`, by Fourier series. -/
def InCriticalSobolev {d : ℕ} (u : Torus d → ℝ) : Prop :=
  MemLp u 2 (torusMeasure d) ∧ Summable (potentialTerm u)

/-- The seminorm `‖u‖²_{Ḣ^{d/2}} = Σ_{k ≠ 0} (2π|k|)^d |û(k)|²`. -/
def potentialEnergy {d : ℕ} (u : Torus d → ℝ) : ℝ :=
  ∑' k : NonzeroFrequency d, potentialTerm u k

/-- `u - ū`, where `ū` is the mean of `u`. -/
def centered {d : ℕ} (u : Torus d → ℝ) (x : Torus d) : ℝ :=
  u x - ∫ y, u y ∂torusMeasure d

/-- `log ∫ e^{u - ū} dm_d`, in the extended reals. -/
def logPartition {d : ℕ} (u : Torus d → ℝ) : EReal :=
  ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (centered u x)) ∂torusMeasure d)

/-- The first-shell coefficient `A_s(d) = 1/(2(2π)^d)`. -/
def spectralCoefficient (d : ℕ) : ℝ := 1 / (2 * (2 * Real.pi) ^ d)

/-- The spectral threshold `β_s(d) = (2π)^d / c_d = 2π^{d/2}/Γ(d/2)`. -/
def spectralThreshold (d : ℕ) : ℝ :=
  2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)

/-- The macroscopic pressure
`P_d(β) = sup_ρ (β c_d/2 ‖ρ‖²_{Ḣ^{-d/2}} - Ent ρ)` over finite-entropy densities,
in the extended reals. Since `c_d ‖ρ‖²_{Ḣ^{-d/2}} = spectralEnergy ρ / β_s(d)`,
the interaction term is `β/(2β_s) · spectralEnergy ρ`. -/
def pressure (d : ℕ) (β : ℝ) : EReal :=
  ⨆ ρ : ProbabilityDensity d, ⨆ (_ : ρ.FiniteEntropy),
    (β / (2 * spectralThreshold d) : ℝ) * (spectralEnergy ρ).toEReal -
      (entropy ρ : EReal)

/-- The optimal additive defect
`C_d(A) = sup_{u ∈ H^{d/2}} (log ∫ e^{u - ū} dm_d - A ‖u‖²_{Ḣ^{d/2}})`. -/
def coefficientDefect (d : ℕ) (A : ℝ) : EReal :=
  ⨆ u : Torus d → ℝ, ⨆ (_ : InCriticalSobolev u),
    logPartition u - (A * potentialEnergy u : ℝ)

/-- The concentration coefficient `A_c(d) = 1/(4 d c_d)`, written with
`c_d = (2π)^d / β_s(d)`. -/
def collapseCoefficient (d : ℕ) : ℝ :=
  spectralThreshold d / (4 * (d : ℝ) * (2 * Real.pi)^d)

/-- Entropy extended to every density: `∫ (ρ log ρ + 1) - 1 ∈ (-∞, ∞]`; it equals
`Ent ρ` for finite entropy and `⊤` otherwise. -/
def extendedEntropy {d : ℕ} (ρ : ProbabilityDensity d) : EReal :=
  (∫⁻ x, ENNReal.ofReal (ρ.value x*Real.log (ρ.value x)+1) ∂torusMeasure d).toEReal - 1

/-- The quartic coefficient `a_d = -1/4 + 1/(4(2^d - 1))`. -/
def quarticA (d : ℕ) : ℝ :=
  -(1 / 4 : ℝ) + 1 / (4 * ((2 : ℝ) ^ d - 1))

/-- The quartic coefficient `b_d = 2/(2^{d/2} - 1)`. -/
def quarticB (d : ℕ) : ℝ :=
  2 / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1)

/-- `κ_d = -(2a_d + (d - 1) b_d)`. -/
def kappa (d : ℕ) : ℝ :=
  -(2 * quarticA d + ((d : ℝ) - 1) * quarticB d)

/-- The Sobolev weight `(1 + (2π|k|)²)^s |û(k)|²`. -/
def sobolevTerm {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (k : Frequency d) : ℝ :=
  (1 + (2 * Real.pi * frequencyLength k) ^ 2) ^ s * ‖fourierCoeff u k‖ ^ 2

/-- Membership in `H^s(𝕋ᵈ)`. -/
def InSobolev {d : ℕ} (s : ℝ) (u : Torus d → ℝ) : Prop :=
  MemLp u 2 (torusMeasure d) ∧ Summable (sobolevTerm s u)

/-- The `H^s` norm (meaningful under `InSobolev s`). -/
def sobolevNorm {d : ℕ} (s : ℝ) (u : Torus d → ℝ) : ℝ :=
  Real.sqrt (∑' k : Frequency d, sobolevTerm s u k)

/-- `∫ u dm_d = 0`. -/
def MeanZero {d : ℕ} (u : Torus d → ℝ) : Prop :=
  (∫ x, u x ∂torusMeasure d) = 0

/-- `u` is `C^∞` as a `ℤᵈ`-periodic function on `ℝᵈ`. -/
def SmoothOnTorus {d : ℕ} (u : Torus d → ℝ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : Fin d → ℝ => u (fun j => (x j : UnitAddCircle)))

/-- The translate `x ↦ u(x - x₀)`. -/
def translate {d : ℕ} (u : Torus d → ℝ) (x₀ : Torus d) : Torus d → ℝ :=
  fun x => u (x - x₀)

/-- The coordinate frequency `e_j`. -/
def axisFrequency {d : ℕ} (j : Fin d) : Frequency d :=
  fun i => if i = j then 1 else 0

/-- The partial derivative `∂_j u(x)`. -/
def coordinateDerivative {d : ℕ} (u : Torus d → ℝ) (j : Fin d) (x : Torus d) : ℝ :=
  deriv (fun t : ℝ => u (x + fun i => if i = j then (t : UnitAddCircle) else 0)) 0

/-- The infinitesimal translation `Σ_j a_j ∂_j u`. -/
def tangentCombination {d : ℕ} (u : Torus d → ℝ) (a : Fin d → ℝ) : Torus d → ℝ :=
  fun x => ∑ j : Fin d, a j * coordinateDerivative u j x

/-- The Gibbs density `e^u / ∫ e^u dm_d`. -/
def normalizedGibbs {d : ℕ} (u : Torus d → ℝ) : Torus d → ℝ :=
  fun x => Real.exp (u x) / (∫ y, Real.exp (u y) ∂torusMeasure d)

/-- `‖u‖²_{Ḣ^{d/2}} / (2π)^d = Σ_{k ≠ 0} |k|^d |û(k)|²`. -/
def normalizedPotentialEnergy {d : ℕ} (u : Torus d → ℝ) : ℝ :=
  potentialEnergy u / (2 * Real.pi) ^ d

/-- The potential functional `log ∫ e^{u-ū} - (β_s/(2β)) Σ |k|^d |û(k)|²`, whose
maximizers correspond to the minimizers of the free energy at coupling `β`. -/
def dualFunctional {d : ℕ} (β : ℝ) (u : Torus d → ℝ) : EReal :=
  logPartition u - ((spectralThreshold d / (2 * β) * normalizedPotentialEnergy u : ℝ) : EReal)

/-- The second variation of `dualFunctional β` at `u` in the direction `h`. -/
def secondVariation {d : ℕ} (β : ℝ) (u h : Torus d → ℝ) : ℝ :=
  (∫ x, normalizedGibbs u x * (h x) ^ 2 ∂torusMeasure d) -
    (∫ x, normalizedGibbs u x * h x ∂torusMeasure d) ^ 2 -
      spectralThreshold d / β * normalizedPotentialEnergy h

/-- The value `β c_d/2 ‖ρ‖²_{Ḣ^{-d/2}} - Ent ρ = -𝓔_β(ρ)` whose supremum is the pressure. -/
def pressureValue {d : ℕ} (β : ℝ) (ρ : ProbabilityDensity d) : EReal :=
  (β / (2 * spectralThreshold d) : ℝ) * (spectralEnergy ρ).toEReal -
    (entropy ρ : EReal)

/-- `ρ` is a global minimizer of the free energy `𝓔_β` among finite-entropy densities. -/
def IsGlobalMinimizer {d : ℕ} (β : ℝ) (ρ : ProbabilityDensity d) : Prop :=
  ρ.FiniteEntropy ∧ ∀ σ : ProbabilityDensity d, σ.FiniteEntropy →
    pressureValue β σ ≤ pressureValue β ρ

/-- The first-shell profile `Σ_j cos(2π(x_j - x₀_j))`. -/
def firstShellProfile {d : ℕ} (x₀ x : Torus d) : ℝ :=
  ∑ j : Fin d, (fourier (1 : ℤ) (x j - x₀ j)).re

/-- `δ = 1 - β_s(d)/β`. -/
def onsetDelta (d : ℕ) (β : ℝ) : ℝ := 1 - spectralThreshold d / β

/-- `u(· - x₀) - 2√(δ/κ_d) Σ_j cos(2π(x_j - x₀_j))`. -/
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

namespace BecknerOnofri.HighDim.VariationalCurves

/-- The global-minimization threshold `β_gm(d) = sup {β ≥ 0 : P_d(β) = 0}`. -/
def globalTransition (d : ℕ) : ℝ := sSup {β : ℝ | 0 ≤ β ∧ pressure d β = 0}

/-- The zero-defect coefficient `A_gm(d) = 1/(2 c_d β_gm(d))`. -/
def zeroDefectCoefficient (d : ℕ) : ℝ :=
  spectralThreshold d/(2*globalTransition d*(2*Real.pi)^d)

end BecknerOnofri.HighDim.VariationalCurves

namespace BecknerOnofri.HighDim.Eleven

/-- Representative in the half-open interval `[-1/2, 1/2)`. -/
def representative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (p := (1 : ℝ)) (-(1 / 2 : ℝ)) x).val

/-- The Euclidean profile `5¹¹ · 122880/π⁶ · (1 + 25|x|²)^{-11}` on `ℝ¹¹`. -/
def euclideanProfile (x : Fin 11 → ℝ) : ℝ :=
  (5 : ℝ)^11 * (122880 / Real.pi^6) *
    (1 + 25 * ∑ i : Fin 11, (x i)^2)^(-11 : ℤ)

/-- The periodized profile `ρ_*(x) = Σ_{n ∈ ℤ¹¹} η(x + n)`. -/
def periodizedProfile (x : Torus 11) : ℝ :=
  ∑' n : Frequency 11, euclideanProfile (fun i => representative (x i) + (n i : ℝ))

/-- The free energy `∫ f log f - (β/(2β_s)) Σ_{k ≠ 0} |k|^{-11} |f̂(k)|²` of a
function `f`, used for second derivatives along smooth perturbations of `1`. -/
def rawFreeEnergy (β : ℝ) (f : Torus 11 → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂torusMeasure 11) -
    β / (2 * spectralThreshold 11) *
      ∑' k : NonzeroFrequency 11,
        (frequencyLength k.val^11)⁻¹ * ‖fourierCoeff f k.val‖^2

/-- The Hessian `d²/dt² 𝓔_β(1 + t h)|_{t=0}` of the free energy at the uniform density. -/
def uniformHessian (β : ℝ) (h : Torus 11 → ℝ) : ℝ :=
  deriv (deriv (fun t : ℝ => rawFreeEnergy β (fun x => 1 + t * h x))) 0

end BecknerOnofri.HighDim.Eleven
-- END VOCABULARY
