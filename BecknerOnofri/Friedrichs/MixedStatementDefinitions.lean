import BecknerOnofri.Friedrichs.MixedSpatialDefinitions

/-! Trusted actual mixed-space tensor form-domain statement. This is the
finite-eigenfunction domain step of the source fractional-intertwining proof,
not the full fractional-power theorem. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def TensorFormDomain (d : ℕ) : Prop :=
  ∀ α : MultiIndex d,∀ f : Fin d → ℝ → ℝ,(∀ i,ContDiff ℝ ∞ (f i)) →
    let F : Space d → ℝ := fun x => ∏ i,Real.sin (x i)^(α i)*f i (Real.cos (x i))
    ∃ v : EnergySpace α,v∈formClosure α ∧
      (v.1 : Space d → ℝ)=ᵐ[spatialMeasure α] F ∧
      (∀ i,(v.2.1 i : Space d → ℝ)=ᵐ[spatialMeasure α] partialDerivative i F) ∧
      (∀ i,(v.2.2 i : Space d → ℝ)=ᵐ[spatialMeasure α]
        (fun x => SpatialForm.potentialFactor (α i) (x i)*F x))

end BecknerOnofri.Friedrichs.MixedSpatial
