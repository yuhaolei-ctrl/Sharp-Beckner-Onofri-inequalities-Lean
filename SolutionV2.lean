/-
Copyright (c) 2026 Yuhao Lei, Matthew Rosenzweig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei, Matthew Rosenzweig
-/
module

public import BecknerOnofri.V2.Final.All
public import BecknerOnofri.V2.Assembly.All
public import BecknerOnofri.V2.Eleven.All
public import BecknerOnofri.V2.Transfer.WrittenTransfer
public import BecknerOnofri.V2.Mixture.Countable
public import BecknerOnofri.V2.Channel.Prop512
public import BecknerOnofri.V2.Channel.CountLaw
public import BecknerOnofri.V2.Circle.ExplicitCorrection
public import BecknerOnofri.V2.ThetaTail.RouteM.Unconditional
public import BecknerOnofri.V2.FiniteState.FamilyComparison
public import BecknerOnofri.V2.Interval.FamilyScalar
public import BecknerOnofri.V2.IntervalKernel.Cells1
public import BecknerOnofri.V2.IntervalKernel.Cells2
public import BecknerOnofri.V2.IntervalKernel.Cells3
public import BecknerOnofri.V2.Vocab.Normalization

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Solution: the v2 auxiliary statements

The statements of `ChallengeV2.lean`, each proved by a direct application of the corresponding
declaration of the v2 development (`V2.Final.Unconditional.*`, `V2.Assembly.*`, `V2.Eleven.*`,
`V2.Transfer.*`, `V2.Mixture.*`, `V2.Channel.*`, `V2.ThetaTail.RouteM.*`, `V2.Circle.*`,
`V2.FiniteState.*`, `V2.Interval.family_scalar_bounds` with `V2.IntervalKernel.hc1/2/3`).

The vocabulary of `Challenge.lean` is the library's own (`BecknerOnofri.HighDim.*`).  The block
`BecknerOnofri.V2Vocab` is the same text as in `ChallengeV2.lean`; the development's definitions
(`HighDim.Spin.channelLaw`, `V2.ThetaTail.Tn`, `V2.FiniteState.famF`, …) are definitionally equal
to these copies, and the proofs below apply the development's theorems at the copies (the
unifier unfolds the definitions).  The only auxiliary lemma is `energy_gt_of_negSobolev`, which
converts the `(2π)^11/2 ‖·‖²` form of `V2.Eleven.prop41` to `spectralEnergy`.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal ContDiff

/-! ## Vocabulary of the auxiliary statements

Every definition below is the definition of the same name in the development, copied from the
module named in its heading, with `BecknerOnofri.V2Vocab.` prepended to its namespace.  The
copy is *not* shared with `SolutionV2.lean`: both files contain this block verbatim, as the
first declarations after their imports, so that Comparator sees the same constants in both
environments; `SolutionV2.lean` proves that each equals the development's own definition (by
`exact` up to definitional unfolding in the proofs below). -/

namespace BecknerOnofri.V2Vocab

/-! ### Cosine-power mixtures and cosine-cube derivatives
(`CosineMixtureStatementDefinitions`, `ConditionalProfileDefinitions`, `CosineShapeDefinitions`) -/

namespace Mixture

def cosinePowerShape (n : ℕ) (x : UnitAddCircle) : ℝ :=
  Complex.normSq (1 + fourier 1 x)^n / ((2*n).choose n:ℝ)

def countableCosineMixture {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (x : HighDim.Torus d) : ℝ :=
  ∑' n, w n * ∏ i, cosinePowerShape (N n i) (x i)

def IsCountableCosineMixture {d : ℕ} (ρ : HighDim.ProbabilityDensity d) : Prop :=
  ∃ (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ),
    (∀ n, 0 ≤ w n) ∧ HasSum w 1 ∧
      ρ.value =ᵐ[HighDim.torusMeasure d] countableCosineMixture w N

def cosineCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.Icc (fun _ => -1) (fun _ => 1)

def cosineVector {d : ℕ} (x : HighDim.Torus d) : Fin d → ℝ :=
  fun j => (fourier 1 (x j)).re

def cosinePartial {d : ℕ} (i : Fin d) (V : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  fderivWithin ℝ V (cosineCube d) x (Pi.single i 1)

end Mixture

/-! ### The thirteen-state model and the binary-spin channel
(`SpinDefinitions`, `SpinDifferentialDefinitions`, `SpinCountDefinitions`, `SpinChannelDefinitions`,
`SpinProductDefinitions`) -/

namespace Spin

abbrev Count := Fin 13
abbrev Order := Fin 12

def referenceQ (j : Count) : ℚ := ((12:ℕ).choose j.val : ℚ)/4096
def meanCoordinateQ (j : Count) : ℚ := (2*(j.val:ℚ)-12)/12

/-- The range of `l` enforces the convention that negative binomial indices
contribute zero; ordinary `Nat.choose` handles the other out-of-range indices. -/
def momentQ (s : Order) (j : Count) : ℚ :=
  (∑ l ∈ Finset.range (s.val+2),
    (-1:ℚ)^l * ((12-j.val).choose l : ℚ) * (j.val.choose (s.val+1-l) : ℚ)) /
      ((12:ℕ).choose (s.val+1) : ℚ)

def weightQ (s : Order) : ℚ :=
  ((12:ℕ).choose (s.val+1) : ℚ)*2^s.val/(s.val+1:ℚ)^6

def interactionQ (i j : Count) : ℚ :=
  ∑ s : Order, weightQ s * momentQ s i * momentQ s j

def reference (j : Count) : ℝ := referenceQ j
def meanCoordinate (j : Count) : ℝ := meanCoordinateQ j
def moment (s : Order) (j : Count) : ℝ := momentQ s j
def weight (s : Order) : ℝ := weightQ s
def interaction (i j : Count) : ℝ := interactionQ i j
def quadratic (q : Count → ℝ) : ℝ :=
  ∑ i : Count, ∑ j : Count, q i * interaction i j * q j
def relativeEntropy (p q : Count → ℝ) : ℝ :=
  ∑ j : Count, p j * Real.log (p j/q j)
def functional (p : Count → ℝ) : ℝ := 2*relativeEntropy p reference-quadratic p
def mean (p : Count → ℝ) : ℝ := ∑ j : Count, meanCoordinate j*p j
def Feasible (p : Count → ℝ) : Prop :=
  (∀ j, 0≤p j) ∧ (∑ j : Count,p j)=1 ∧ p 0≤1/4096
def FeasibleAt (t : ℝ) (p : Count → ℝ) : Prop := Feasible p ∧ mean p=t

def gradient (p : Count → ℝ) (j : Count) : ℝ :=
  2*Real.log (p j/reference j)+2-2*(∑ k : Count,interaction j k*p k)

abbrev Configuration := Finset (Fin 12)

def Exchangeable (ν : Configuration → ℝ) : Prop :=
  ∀ (π : Equiv.Perm (Fin 12)) (σ : Configuration),ν (σ.map π.toEmbedding)=ν σ

def channel (c : Fin 12 → ℝ) (σ : Configuration) : ℝ :=
  (∏ i ∈ σ,(1+c i)/2)*(∏ i ∈ σᶜ,(1-c i)/2)

/-- The product of spins in S: plus coordinates contribute one, and every
minus coordinate belonging to S contributes minus one. -/
def jointSpin (S : Finset (Fin 12)) (σ : Configuration) : ℝ :=
  ∏ i ∈ σᶜ,if i∈S then (-1:ℝ) else 1

def torusCosines (x : HighDim.Torus 12) (i : Fin 12) : ℝ := (fourier 1 (x i)).re
def channelLaw (ρ : HighDim.ProbabilityDensity 12) (σ : Configuration) : ℝ :=
  ∫ x,ρ.value x*channel (torusCosines x) σ ∂HighDim.torusMeasure 12

def binaryCost (t : ℝ) : ℝ :=
  ((1+t)*Real.log (1+t)+(1-t)*Real.log (1-t))/2

end Spin

/-! ### Cosine moments of a density on the circle (`CircleDeficitDefinitions`), `ψ`
(`V2/Circle/Psi`), the first Fourier coefficient and the spin relative entropy
(`V2/Channel/Prop512`) -/

namespace Circle

def moment (p : HighDim.Torus 1 → ℝ) (n : ℕ) : ℝ :=
  (@UnitAddTorus.mFourierCoeff (Fin 1) _ ℂ Complex.instNormedAddCommGroup NormedField.toNormedSpace
    (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re

/-- `ψ(t) = t⁴/(14-10t²)` (Lemma 5.16). -/
def psi (t : ℝ) : ℝ := t ^ 4 / (14 - 10 * t ^ 2)

end Circle

namespace Channel

/-- The relative entropy `Hr(ν | μ_spin)` of a spin law with respect to the uniform measure. -/
def spinRelEntropy (ν : Spin.Configuration → ℝ) : ℝ :=
  ∑ σ : Spin.Configuration, ν σ * Real.log (ν σ / (1 / 4096))

/-- The common spin mean `t = ρ̂(e_1)`: the real part of the first Fourier coefficient. -/
def firstCoefficient (ρ : HighDim.ProbabilityDensity 12) : ℝ :=
  (HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re

end Channel

/-! ### The scalar Fourier tail (`V2/ThetaTail/Defs`) -/

namespace ThetaTail

/-- `θ(q) = ∑_{k∈ℤ} q^{k²}`. -/
def theta (q : ℝ) : ℝ := ∑' k : ℤ, q ^ (k ^ 2)

/-- `σ₅(m) = ∑_{d∣m} d⁵` as a real number. -/
def sigma5 (m : ℕ) : ℝ := ((ArithmeticFunction.sigma 5 m : ℕ) : ℝ)

/-- the cube `{-1,0,1}^12` -/
def cube12 : Set (Fin 12 → ℤ) := Set.pi Set.univ fun _ => ({-1, 0, 1} : Set ℤ)

/-- `|k|²` -/
def latticeNormSq (k : Fin 12 → ℤ) : ℝ := ∑ i, ((k i : ℤ) : ℝ) ^ 2

/-- `|k|` (Euclidean length) -/
def latticeNorm (k : Fin 12 → ℤ) : ℝ := Real.sqrt (latticeNormSq k)

/-- `a_n(j) = C(2n, n+j)/C(2n, n)` (`eq:scalar-def`), written with `|j|` (the binomial
coefficient is symmetric); `Nat.choose (2n) m = 0` for `m > 2n` gives the convention that
binomial coefficients vanish outside their support. -/
def aCoef (n : ℕ) (j : ℤ) : ℝ :=
  ((2 * n).choose (n + j.natAbs) : ℝ) / ((2 * n).choose n : ℝ)

/-- `H_n = ∑_{j=1}^n 1/j` -/
def Hn (n : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 n, 1 / (j : ℝ)

/-- `T_n = ∑_{k ∉ {-1,0,1}^{12}} |k|^{-12} ∏ a_n(k_i)` (`eq:section5-global-tail-definitions`). -/
def Tn (n : ℕ) : ℝ :=
  ∑' k : Fin 12 → ℤ, (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef n (k i)) k

/-- `R_n = 81/10 H_n − 81/5 a_n(1) − 15/2 a_n(2) − 11/5 a_n(3)`. -/
def Rn (n : ℕ) : ℝ :=
  81 / 10 * Hn n - 81 / 5 * aCoef n 1 - 15 / 2 * aCoef n 2 - 11 / 5 * aCoef n 3

end ThetaTail

/-! ### The explicit reference family of Section 5.2.5
(`V2/FiniteState/FamilyBounds`, `Regression`, `VarianceComparison`, `FamilyDefs`) -/

namespace Family

def famL (t : ℝ) : ℝ := 9 / 2 * t ^ 10
def famLam (t : ℝ) : ℝ := famL t / (1 + famL t)
def famBias (t : ℝ) : ℝ := t - famL t * (1 - t)
def famChi (t : ℝ) : ℝ := 31 / t ^ 2 - 32 + 12 * t ^ 4 + t ^ 2 / (10 * (1 - t))
def famP (u : ℝ) : ℝ := 31 - 32 * u + 12 * u ^ 3
def famOmega (t : ℝ) : ℝ := t ^ 2 * (1 - t) / (famP (t ^ 2) * (1 - t) + t ^ 4 / 10)

variable {ι : Type*} [Fintype ι]

/-- `σ_x^2(t) = ∑ p_j (x_j - t)^2`. -/
def regVar (p x : ι → ℝ) (t : ℝ) : ℝ := ∑ j, p j * (x j - t) ^ 2
/-- `ḡ = ∑ p_j g_j`. -/
def regMean (p g : ι → ℝ) : ℝ := ∑ j, p j * g j
/-- `η = ∑ p_j (x_j - t) g_j / σ_x^2`. -/
def regSlope (p x g : ι → ℝ) (t : ℝ) : ℝ := (∑ j, p j * (x j - t) * g j) / regVar p x t
/-- `e_j = g_j - ḡ - η (x_j - t)`. -/
def regResid (p x g : ι → ℝ) (t : ℝ) (j : ι) : ℝ :=
  g j - regMean p g - regSlope p x g t * (x j - t)

open Spin

/-- Residual of the Count-gradient, with the manuscript's `x_j = meanCoordinate j`. -/
def gradResid (t : ℝ) (p : Count → ℝ) (j : Count) : ℝ :=
  regResid p meanCoordinate (gradient p) t j

/-- Source correction `ψ(t) = t^4/(14 - 10 t^2)`. -/
def psiV2 (t : ℝ) : ℝ := t ^ 4 / (14 - 10 * t ^ 2)

/-- Rational product form `d12-spin-eq:rationalfamily` (regular at `t = 0`).
Empty products are `1`; the `-` factors number `12 - j`, the `+` factors number `j`. -/
def famNu (t : ℝ) (j : Count) : ℝ :=
  ((12 : ℕ).choose j.val : ℝ) *
    (∏ k ∈ Finset.range j.val, ((1 + famBias t) / 2 + (k : ℝ) * famOmega t)) *
    (∏ k ∈ Finset.range (12 - j.val), ((1 - famBias t) / 2 + (k : ℝ) * famOmega t)) /
    (∏ k ∈ Finset.range 12, (1 + (k : ℝ) * famOmega t))

/-- The mixed law `p(t)`: with the all-plus state (`j = 12`). -/
def famLaw (t : ℝ) (j : Count) : ℝ :=
  (1 - famLam t) * famNu t j + famLam t * (if j.val = 12 then 1 else 0)

/-- `e_j(t)`, `𝒱(t)`, `f(t)` of `d12-spin-eq:residual`. -/
def famResid (t : ℝ) (j : Count) : ℝ := gradResid t (famLaw t) j
def famResidVar (t : ℝ) : ℝ := ∑ j : Count, famLaw t j * famResid t j ^ 2
def famF (t : ℝ) : ℝ := functional (famLaw t) + 12 * psiV2 t

end Family

end BecknerOnofri.V2Vocab

namespace BecknerOnofri.V2Surface

open BecknerOnofri.HighDim

open BecknerOnofri.V2.Vocab in
/-- `spectralEnergy ρ = (2π)^11 ‖ρ‖²` turns the `prop41` energy bound into the `spectralEnergy` form. -/
theorem energy_gt_of_negSobolev (ρ : ProbabilityDensity 11)
    (hb : (14475384292906 : ℝ) / 10 ^ 12 <
      (2 * Real.pi) ^ 11 / 2 * (negSobolevEnergy ρ.value).toReal) :
    ENNReal.ofReal (2 * ((14475384292906 : ℝ) / 10 ^ 12)) < spectralEnergy ρ := by
  have hN : negSobolevEnergy ρ.value ≠ ⊤ := by
    intro htop
    rw [htop] at hb
    norm_num at hb
  rw [spectralEnergy_eq_mul_negSobolevEnergy, ← ENNReal.ofReal_toReal hN,
    ← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by
    have : (0 : ℝ) < 14475384292906 / 10 ^ 12 := by norm_num
    nlinarith)).2 ?_
  linarith


/-! ## Section 4: dimension eleven -/

/-- **Proposition 4.1 (`d11:thm:interval`).** `3543/200 < β_gm(11) < 2063/100`; for every
`0 ≤ β ≤ 3543/200` the uniform density is the unique global minimizer of `𝓔_β`; and
`ρ_*` (`Eleven.periodizedProfile`) satisfies `(2π)^{11}/2 ‖ρ_*‖²_{Ḣ^{-11/2}} > 14475384292906/10^{12}`,
written with `spectralEnergy ρ_* = (2π)^{11} ‖ρ_*‖²_{Ḣ^{-11/2}}`. -/
theorem prop_4_1 :
    ((3543 : ℝ) / 200 < VariationalCurves.globalTransition 11 ∧
      VariationalCurves.globalTransition 11 < 2063 / 100) ∧
    (∀ β : ℝ, 0 ≤ β → β ≤ 3543 / 200 →
      IsGlobalMinimizer β (uniformDensity 11) ∧
        ∀ ρ : ProbabilityDensity 11, IsGlobalMinimizer β ρ →
          ρ.value =ᵐ[torusMeasure 11] fun _ => 1) ∧
    (∀ ρ : ProbabilityDensity 11, ρ.value = Eleven.periodizedProfile →
      ENNReal.ofReal (2 * ((14475384292906 : ℝ) / 10 ^ 12)) < spectralEnergy ρ) := by
  obtain ⟨h1, h2, h3⟩ := BecknerOnofri.V2.Eleven.prop41
  refine ⟨h1, fun β hβ hβ' => ?_, fun ρ hρ => ?_⟩
  · have hfin : (uniformDensity 11).FiniteEntropy := by
      simp [ProbabilityDensity.FiniteEntropy, uniformDensity]
    exact ⟨(h2 β hβ hβ' _ hfin).2 Filter.EventuallyEq.rfl,
      fun ρ hρ => (h2 β hβ hβ' ρ hρ.1).1 hρ⟩
  · exact energy_gt_of_negSobolev ρ (h3 ρ hρ)

/-- **Theorem 1.2 certificate with the manuscript's entropy bound (Proposition 4.2,
`prop:section4-entropy-bound`, `eq:intro-d11-certificate`).**  The periodized profile
`ρ_* = Σ_{n ∈ ℤ¹¹} η(· + n)` is a smooth, strictly positive probability density with
`Ent(ρ_*) < 8653/600` and `(2π)¹¹/2 ‖ρ_*‖²_{Ḣ^{-11/2}} > 14.4753`
(`spectralEnergy ρ_* = (2π)¹¹ ‖ρ_*‖²_{Ḣ^{-11/2}}`).  (`Challenge.eleven_competitor` states the
repository's stronger entropy bound `18011/1250`; this theorem states the printed `8653/600`.) -/
theorem eleven_competitor_written :
    ∃ ρ : ProbabilityDensity 11, ρ.value = Eleven.periodizedProfile ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧ ρ.FiniteEntropy ∧
      entropy ρ < (8653 : ℝ) / 600 ∧
      ENNReal.ofReal (2 * ((144753 : ℝ) / 10000)) < spectralEnergy ρ := by
  exact BecknerOnofri.V2.Final.eleven_competitor_written

/-- **Proposition 4.9 (`prop:section4-first-order-coexistence`).** At `β = β_gm(11)` the uniform
density and at least one nonuniform smooth strictly positive density are global minimizers of
`𝓔_{β_gm}`; the Hessian at the uniform density is strictly positive,
`D²𝓔_{β_gm}(1)[h,h] ≥ (1 - β_gm/β_s) ∫ h²` for every smooth mean-zero `h`; `P_11` is not
differentiable at `β_gm` and `C_11` is not differentiable at `A_gm(11)`. -/
theorem prop_4_9 :
    (IsGlobalMinimizer (VariationalCurves.globalTransition 11) (uniformDensity 11) ∧
      ∃ ρ : ProbabilityDensity 11,
        IsGlobalMinimizer (VariationalCurves.globalTransition 11) ρ ∧
        SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
        ¬ (ρ.value =ᵐ[torusMeasure 11] fun _ => 1)) ∧
    (0 < 1 - VariationalCurves.globalTransition 11 / spectralThreshold 11 ∧
      ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
        (1 - VariationalCurves.globalTransition 11 / spectralThreshold 11) *
            (∫ x, h x ^ 2 ∂torusMeasure 11) ≤
          Eleven.uniformHessian (VariationalCurves.globalTransition 11) h) ∧
    ¬ DifferentiableAt ℝ (fun β => (pressure 11 β).toReal)
        (VariationalCurves.globalTransition 11) ∧
    ¬ DifferentiableAt ℝ (fun A => (coefficientDefect 11 A).toReal)
        (VariationalCurves.zeroDefectCoefficient 11) := by
  exact ⟨BecknerOnofri.V2.Final.eleven_coexistence,
    BecknerOnofri.V2.Final.eleven_uniform_hessian_pos,
    BecknerOnofri.V2.Final.eleven_pressure_corner.2,
    BecknerOnofri.V2.Final.eleven_defect_corner.2⟩

/-! ## Section 5: the spectral inequality in dimensions `d ≥ 12` -/

/-- **Proposition 5.1 (`prop:spectral-d12-base`).** For every finite-entropy probability density
`ρ` on `𝕋¹²`, `Ent(ρ) ≥ (2π)^{12}/2 ‖ρ‖²_{Ḣ^{-6}}`, with equality exactly for `ρ = 1` a.e.
(`spectralEnergy ρ = (2π)^{12} ‖ρ‖²_{Ḣ^{-6}}`). -/
theorem prop_5_1 (ρ : ProbabilityDensity 12) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
      (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
        ρ.value =ᵐ[torusMeasure 12] fun _ => 1) := by
  exact BecknerOnofri.V2.Assembly.spectral_d12_base
    BecknerOnofri.V2.Final.Unconditional.scalarBounds ρ hρ

/-- **Proposition 5.7 (`prop:spectral-dimension-transfer`).** Assume the dimension-twelve inequality
and that equality in dimension twelve holds only for the uniform density.  Then for every `d ≥ 12`
and every finite-entropy density `ρ` on `𝕋^d`, `Ent(ρ) ≥ (2π)^d/2 ‖ρ‖²_{Ḣ^{-d/2}}`, with equality
exactly for `ρ = 1` a.e. -/
theorem prop_5_7
    (h12 : ∀ ρ : ProbabilityDensity 12, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ))
    (hEq : ∀ ρ : ProbabilityDensity 12, ρ.FiniteEntropy →
      spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) →
        ρ.value =ᵐ[torusMeasure 12] fun _ => 1)
    (d : ℕ) (hd : 12 ≤ d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
      (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
        ρ.value =ᵐ[torusMeasure d] fun _ => 1) := by
  exact BecknerOnofri.V2.Transfer.spectral_dimension_transfer_written h12 hEq hd ρ hρ

/-- **Corollary 5.8 (`cor:section5-high-endpoint`).** For every `d ≥ 12` and every finite-entropy
density, `Ent(ρ) ≥ (2π)^d/2 ‖ρ‖²_{Ḣ^{-d/2}}` with equality exactly for `ρ = 1`; the dual potential
inequality has coefficient `A_s(d)` with equality exactly for constants; and `β_gm(d) = β_s(d)`. -/
theorem cor_5_8 (d : ℕ) (hd : 12 ≤ d) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
        (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
          ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ∧
        (logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
          ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) ∧
    VariationalCurves.globalTransition d = spectralThreshold d := by
  have h := BecknerOnofri.V2.Final.Unconditional.high_endpoint d hd
  exact ⟨fun ρ hρ => h.1 ρ hρ, h.2.1, h.2.2.2.1⟩

/-- **Proposition 5.10 (`prop:section5-global-entropy-gap`).** Let `ρ` be a smooth strictly positive
probability density on `𝕋¹²`, invariant under coordinate permutations and of the form
(eq:mixture), with `log ρ(x) = V(cos 2πx₁, …, cos 2πx₁₂)`, `V ∈ C^∞([-1,1]¹²)`, `∂_iV ≥ 0` and
`∂_i²V ≥ 0`.  Then `Ent(ρ) - (2π)^{12}/2 ‖ρ‖²_{Ḣ^{-6}} ≥ ρ̂(e₁)⁴/250` (the energy is finite and
`spectralEnergy ρ = (2π)^{12} ‖ρ‖²_{Ḣ^{-6}}`); moreover `ρ̂(e₁) ≥ 0`, and `ρ̂(e₁) = 0` implies
`ρ = 1`. -/
theorem prop_5_10 (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hp : ∀ x, 0 < ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    (hmix : V2Vocab.Mixture.IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (V2Vocab.Mixture.cosineCube 12))
    (hlog : ∀ x, Real.log (ρ.value x) = V (V2Vocab.Mixture.cosineVector x))
    (h1 : ∀ v ∈ V2Vocab.Mixture.cosineCube 12, ∀ i : Fin 12, 0 ≤ V2Vocab.Mixture.cosinePartial i V v)
    (h2 : ∀ v ∈ V2Vocab.Mixture.cosineCube 12, ∀ i : Fin 12,
      0 ≤ V2Vocab.Mixture.cosinePartial i (V2Vocab.Mixture.cosinePartial i V) v) :
    ((((V2Vocab.Channel.firstCoefficient ρ) ^ 4 / 250 : ℝ) : EReal) +
        ((1 / 2 : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ (entropy ρ : EReal)) ∧
      0 ≤ V2Vocab.Channel.firstCoefficient ρ ∧
      (V2Vocab.Channel.firstCoefficient ρ = 0 → ρ.value = fun _ => 1) := by
  have hc : Continuous ρ.value := BecknerOnofri.HighDim.UniformFourier.smooth_continuous hs
  obtain ⟨h1', h2', h3'⟩ := BecknerOnofri.V2.Assembly.global_entropy_gap
    BecknerOnofri.V2.Final.Unconditional.scalarBounds ρ hs hp hperm hmix V hV hlog h1 h2
  refine ⟨?_, h2', h3'⟩
  have hnn : 0 ≤ BecknerOnofri.HighDim.EntropyTail.fullFourierEnergy ρ.value :=
    tsum_nonneg (fun k => by positivity)
  rw [BecknerOnofri.HighDim.EntropyTail.spectralEnergy_eq_fullFourierEnergy ρ hc,
    EReal.coe_ennreal_ofReal, max_eq_left hnn]
  exact_mod_cast (by linarith : BecknerOnofri.V2.Channel.firstCoefficient ρ ^ 4 / 250 +
    1 / 2 * BecknerOnofri.HighDim.EntropyTail.fullFourierEnergy ρ.value ≤ entropy ρ)

/-- **Proposition 5.11 (`prop:section5-singular-fourier-tail`, eq:section5-global-tail-energy).**
Every smooth probability density of the form (eq:mixture) on `𝕋¹²` satisfies
`½ Σ_{k ∉ {-1,0,1}¹²} |k|^{-12} |ρ̂(k)|² ≤ Σ_{i=1}^{12} [|ρ̂(2e_i)|²/40 + 2|ρ̂(3e_i)|²/15
+ (27/40) Σ_{n ≥ 4} |ρ̂(ne_i)|²/n]`. -/
theorem prop_5_11 (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hρ : V2Vocab.Mixture.IsCountableCosineMixture ρ) :
    (1 / 2 : ℝ) * ∑' k : Fin 12 → ℤ, (V2Vocab.ThetaTail.cube12ᶜ).indicator
        (fun k => (V2Vocab.ThetaTail.latticeNorm k ^ 12)⁻¹ *
          ‖fourierCoeff ρ.value k‖ ^ 2) k ≤
      ∑ i : Fin 12,
        (1 / 40 * ‖fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 +
          2 / 15 * ‖fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 +
          27 / 40 * ∑' j : ℕ,
            ‖fourierCoeff ρ.value (Pi.single i ((j : ℤ) + 4))‖ ^ 2 / ((j : ℝ) + 4)) := by
  exact BecknerOnofri.V2.Mixture.singular_fourier_tail ρ hs hρ

/-- **Proposition 5.12(i) (`prop:section5-spin-entropy`).**  If `ρ` satisfies the hypotheses of
Proposition 5.10, then the channel law `ν_ρ` is an exchangeable probability measure on `{-1,1}¹²`
(a spin configuration is the finset of its `+1` coordinates) with common spin mean
`t = ρ̂(e₁)`, `ν_ρ(σ₁ = ⋯ = σ₁₂ = -1) ≤ 2^{-12}`, and
`Ent(ρ) ≥ 2 Hr(ν_ρ | μ_spin) + 12 ψ(t) + Σ_i [|ρ̂(2e_i)|²/40 + 2|ρ̂(3e_i)|²/15
+ (27/40) Σ_{n ≥ 4} |ρ̂(ne_i)|²/n]` (eq:section5-global-channel-entropy). -/
theorem prop_5_12_i (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hp : ∀ x, 0 < ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    (hmix : V2Vocab.Mixture.IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (V2Vocab.Mixture.cosineCube 12))
    (hlog : ∀ x, Real.log (ρ.value x) = V (V2Vocab.Mixture.cosineVector x))
    (h1 : ∀ v ∈ V2Vocab.Mixture.cosineCube 12, ∀ i : Fin 12, 0 ≤ V2Vocab.Mixture.cosinePartial i V v)
    (h2 : ∀ v ∈ V2Vocab.Mixture.cosineCube 12, ∀ i : Fin 12,
      0 ≤ V2Vocab.Mixture.cosinePartial i (V2Vocab.Mixture.cosinePartial i V) v) :
    (V2Vocab.Spin.Exchangeable (V2Vocab.Spin.channelLaw ρ) ∧
      (∀ σ, 0 ≤ V2Vocab.Spin.channelLaw ρ σ) ∧
      (∑ σ, V2Vocab.Spin.channelLaw ρ σ) = 1 ∧
      (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).im = 0 ∧
      ∀ i : Fin 12, (∑ σ, V2Vocab.Spin.channelLaw ρ σ *
        V2Vocab.Spin.jointSpin {i} σ) =
          V2Vocab.Channel.firstCoefficient ρ) ∧
    V2Vocab.Spin.channelLaw ρ ∅ ≤ 1 / 4096 ∧
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      ‖fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4))) ∧
    2 * V2Vocab.Channel.spinRelEntropy (V2Vocab.Spin.channelLaw ρ) +
        12 * V2Vocab.Circle.psi (V2Vocab.Channel.firstCoefficient ρ) +
      ∑ i : Fin 12, ((1 / 40) * ‖fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 +
        (2 / 15) * ‖fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 +
        (27 / 40) * ∑' n : ℕ,
          ‖fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4)) ≤
      entropy ρ := by
  exact BecknerOnofri.V2.Channel.spin_entropy_comparison_i ρ hs hp hperm hmix V hV hlog h1 h2

/-- **Proposition 5.12(ii) (`prop:section5-spin-entropy`, eq:section5-global-spin-final).**  Every
exchangeable probability measure `ν` on `{-1,1}¹²` with common spin mean `t ∈ [0,1]` and
`ν(σ₁ = ⋯ = σ₁₂ = -1) ≤ 2^{-12}` satisfies
`2 Hr(ν | μ_spin) - Σ_{r=1}^{12} C(12,r) 2^{r-1}/r⁶ (E_ν[σ₁⋯σ_r])² + 12 ψ(t) ≥ t⁴/250`,
with `μ_spin` uniform (`1/4096` on each configuration). -/
theorem prop_5_12_ii {ν : V2Vocab.Spin.Configuration → ℝ}
    (hν : V2Vocab.Spin.Exchangeable ν) (hnn : ∀ σ, 0 ≤ ν σ)
    (hmass : (∑ σ, ν σ) = 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i : Fin 12,
      (∑ σ : V2Vocab.Spin.Configuration,
        ν σ * V2Vocab.Spin.jointSpin {i} σ) = t)
    (hcap : ν ∅ ≤ 1 / 4096) :
    t ^ 4 / 250 ≤
      2 * (∑ σ : V2Vocab.Spin.Configuration, ν σ * Real.log (ν σ / (1 / 4096))) -
        (∑ r ∈ Finset.Icc 1 12, ((12 : ℕ).choose r : ℝ) * 2 ^ (r - 1) / (r : ℝ) ^ 6 *
          (∑ σ : V2Vocab.Spin.Configuration, ν σ *
            V2Vocab.Spin.jointSpin
              (Finset.univ.filter (fun i : Fin 12 => i.val < r)) σ) ^ 2) +
        12 * V2Vocab.Circle.psi t := by
  exact BecknerOnofri.V2.Channel.spin_final_of_count_form
    (BecknerOnofri.V2.Assembly.count_form_public
      BecknerOnofri.V2.Final.Unconditional.scalarBounds) hν hnn hmass ht hmean hcap

/-! ## Appendix A: the scalar tail -/

/-- **Lemma 5.13 (`lem:section5-global-scalar-tail`).** For every integer `n ≥ 0`, `T_n ≤ R_n`. -/
theorem lemma_5_13 (n : ℕ) : V2Vocab.ThetaTail.Tn n ≤ V2Vocab.ThetaTail.Rn n := by
  exact BecknerOnofri.V2.ThetaTail.RouteM.Tn_le_Rn n

/-- **The twelve-square identity (d12-tail-eq:theta12, Appendix A.1).** For `0 < q < 1`,
`θ(q)¹² = 1 + 8 Σ_{m ≥ 1} σ₅(m) q^m - 512 Σ_{m ≥ 1} σ₅(m) q^{4m} + 16 q ∏_{m ≥ 1} (1 - q^{2m})¹²`. -/
theorem twelve_square_identity (q : ℝ) (h0 : 0 < q) (h1 : q < 1) :
    V2Vocab.ThetaTail.theta q ^ 12 =
      1 + 8 * ∑' m : ℕ+, V2Vocab.ThetaTail.sigma5 m * q ^ (m : ℕ)
        - 512 * ∑' m : ℕ+, V2Vocab.ThetaTail.sigma5 m * q ^ (4 * (m : ℕ))
        + 16 * q * ∏' m : ℕ+, (1 - q ^ (2 * (m : ℕ))) ^ 12 := by
  exact BecknerOnofri.V2.ThetaTail.RouteM.twelve_square_routeM q h0 h1

/-! ## Appendix: the circle estimate and the finite-state inequality -/

/-- **Lemma 5.16 (`lem:section5-circle-explicit-bound`).** Let `p` be a strictly positive even `C³`
probability density on the circle, with cosine moments `r_n` and `t = r₁ ∈ [0,1)`.  Then
`Ent(p) ≥ 2 I_B(t) + ψ(t) + r₂²/40 + 2r₃²/15 + (27/40) Σ_{n≥4} r_n²/n`.  (`Continuous p` is
implied by `C³`; it is kept as the hypothesis under which the integrals are formed.) -/
theorem lemma_5_16 (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (he : ∀ x, p (-x) = p x) (hm : (∫ x, p x ∂torusMeasure 1) = 1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x : UnitAddCircle))))
    (ht : V2Vocab.Circle.moment p 1 ∈ Set.Ico (0 : ℝ) 1) :
    2 * V2Vocab.Spin.binaryCost (V2Vocab.Circle.moment p 1) +
      V2Vocab.Circle.psi (V2Vocab.Circle.moment p 1) +
      (1 / 40) * (V2Vocab.Circle.moment p 2) ^ 2 +
      (2 / 15) * (V2Vocab.Circle.moment p 3) ^ 2 +
      (27 / 40) * (∑' n : ℕ,
        (V2Vocab.Circle.moment p (n + 4)) ^ 2 / (n + 4 : ℝ)) ≤
        ∫ x, p x * Real.log (p x) ∂torusMeasure 1 := by
  exact BecknerOnofri.V2.Circle.circle_entropy_explicit p hp hpos he hm hsmooth ht.1

/-- **Lemma 5.20 (`d12-spin-lem:perturb`).** Fix `0 ≤ t < 1`.  If `e_j(t) ≥ -1/4` for every `j`,
then every `q ∈ 𝒫_t` satisfies `F(q) + 12 ψ(t) ≥ f(t) - (30/7) 𝒱(t)`. -/
theorem lemma_5_20 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {q : V2Vocab.Spin.Count → ℝ} (hq : V2Vocab.Spin.FeasibleAt t q)
    (he : ∀ j : V2Vocab.Spin.Count,
      -(1 / 4 : ℝ) ≤ V2Vocab.Family.famResid t j) :
    V2Vocab.Family.famF t -
        (30 / 7 : ℝ) * V2Vocab.Family.famResidVar t ≤
      V2Vocab.Spin.functional q + 12 * V2Vocab.Circle.psi t := by
  exact BecknerOnofri.V2.FiniteState.family_variance_comparison ht0 ht1 hq he

/-- **Lemma 5.21 (`d12-spin-lem:scalar`, computer-assisted scalar bounds).** For the explicit
family and its residual, `f(t) ≥ t⁴/10` (strict for `t > 0`), `𝒱(t) ≤ t⁴/50` and
`e_j(t) ≥ -1/4` for `0 ≤ j ≤ 12`, for all `0 ≤ t ≤ 99/100`. -/
theorem lemma_5_21 (t : ℝ) (h0 : 0 ≤ t) (h99 : t ≤ 99 / 100) :
    (t ^ 4 / 10 ≤ V2Vocab.Family.famF t ∧
      (0 < t → t ^ 4 / 10 < V2Vocab.Family.famF t)) ∧
    V2Vocab.Family.famResidVar t ≤ t ^ 4 / 50 ∧
    ∀ j : V2Vocab.Spin.Count,
      -(1 / 4 : ℝ) ≤ V2Vocab.Family.famResid t j := by
  obtain ⟨hF, hV, he⟩ := BecknerOnofri.V2.Interval.family_scalar_bounds
    BecknerOnofri.V2.IntervalKernel.hc1 BecknerOnofri.V2.IntervalKernel.hc2
    BecknerOnofri.V2.IntervalKernel.hc3 t h0 h99
  exact ⟨hF, hV.1, he⟩

end BecknerOnofri.V2Surface
