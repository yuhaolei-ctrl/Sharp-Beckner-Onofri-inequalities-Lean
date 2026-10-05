import BecknerOnofri.Friedrichs.MixedSpectralPowers
import BecknerOnofri.SmoothEulerStatementDefinitions
import BecknerOnofri.SmoothAngularPower

/-! Trusted manuscript Lemma fractional: arbitrary closed-cube smooth profile,
all nonzero multi-indices, actual mixed Lebesgue space and its spectral power.
The angle in UnitAddCircle coordinates is 2*pi*x. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def derivativeList {d : ℕ} (α : MultiIndex d) : List (Fin d) :=
  (List.ofFn (fun i => List.replicate (α i) i)).flatten

def cosineLift {d : ℕ} (U : (Fin d → ℝ) → ℝ) (x : HighDim.Torus d) : ℝ :=
  U (fun i => (fourier 1 (x i)).re)

def FractionalIntertwining (d : ℕ) : Prop :=
  ∀ U : (Fin d → ℝ) → ℝ,
    ContDiffOn ℝ ∞ U (HighDim.SmoothEulerStatement.cosineCube d) →
    ∀ (α : MultiIndex d),α≠0 → ∀ s : ℝ,0<s →
      ∃ Us : (Fin d → ℝ) → ℝ,
        ContDiffOn ℝ ∞ Us (HighDim.SmoothEulerStatement.cosineCube d) ∧
        (∀ x : Fin d → ℝ,SmoothTorus.angularPower s (cosineLift U) (fun i => (x i : UnitAddCircle))=
          Us (fun i => Real.cos (2*Real.pi*x i))) ∧
        (∀ k : HighDim.Frequency d,HighDim.fourierCoeff (SmoothTorus.angularPower s (cosineLift U)) k=
          ((HighDim.frequencyLength k^(2*s):ℝ):ℂ)*HighDim.fourierCoeff (cosineLift U) k) ∧
        ∃ f g : H α,
          (f : Space d → ℝ)=ᵐ[spatialMeasure α]
            (fun x => (∏ i,Real.sin (x i)^(α i))*
              HighDim.SmoothEulerStatement.mixedPartial (derivativeList α) U (fun i => Real.cos (x i))) ∧
          (g : Space d → ℝ)=ᵐ[spatialMeasure α]
            (fun x => (∏ i,Real.sin (x i)^(α i))*
              HighDim.SmoothEulerStatement.mixedPartial (derivativeList α) Us (fun i => Real.cos (x i))) ∧
          SpectralPowerGraph α s f g

end BecknerOnofri.Friedrichs.MixedSpatial
