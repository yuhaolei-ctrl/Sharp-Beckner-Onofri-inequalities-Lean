module

public import BecknerOnofri.PrescribedSelectionDefinitions
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs

@[expose] public section

/-! The manuscript's general smooth monotone Euler-pair assertion. Derivatives
are actual iterated Frechet derivatives within the closed cosine cube [-1,1]^d. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.HighDim.SmoothEulerStatement

def cosineCube (d : ℕ) : Set (Fin d → ℝ) := Icc (-1) 1

def coordinateDerivative {d : ℕ} (i : Fin d) (U : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) : ℝ :=
  fderivWithin ℝ U (cosineCube d) z (Pi.single i 1)

def mixedPartial {d : ℕ} : List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], U => U
  | i::is, U => mixedPartial is (coordinateDerivative i U)

def CosineRepresentation (d : ℕ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (u : Torus d → ℝ) (ρ : ProbabilityDensity d),
    SmoothOnTorus u → MeanZero u → PrescribedSelection.CoordinateSteiner u →
    ρ.value=normalizedGibbs u →
    (∀ k : NonzeroFrequency d, (frequencyLength k.val^d : ℂ)*fourierCoeff u k.val =
      (β/spectralThreshold d : ℝ)*fourierCoeff ρ.value k.val) →
    ∃ U : (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ ∞ U (cosineCube d) ∧
      (∀ x : Fin d → ℝ, u (fun i => (x i : UnitAddCircle)) =
        U (fun i => Real.cos (2*Real.pi*x i))) ∧
      (∀ is : List (Fin d), is≠[] → ∀ z ∈ cosineCube d, 0 ≤ mixedPartial is U z) ∧
      IsCountableCosineMixture ρ

end BecknerOnofri.HighDim.SmoothEulerStatement
