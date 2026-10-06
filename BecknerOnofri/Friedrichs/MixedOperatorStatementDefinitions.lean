module

public import BecknerOnofri.Friedrichs.MixedSpatialDefinitions

@[expose] public section

/-! Trusted tensor conjugation statement in the actual mixed spatial
closed-form graph. Its hypotheses include no spectral or form-domain premise. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def TensorOperatorConjugation (d : ℕ) : Prop :=
  ∀ α : MultiIndex d,∀ f : Fin d → ℝ → ℝ,(∀ i,ContDiff ℝ ∞ (f i)) →
    let F : Space d → ℝ := fun x => ∏ i,Real.sin (x i)^(α i)*f i (Real.cos (x i))
    let G : Space d → ℝ := fun x => ∑ i,
      (∏ j∈Finset.univ.erase i,Real.sin (x j)^(α j)*f j (Real.cos (x j)))*
        (Real.sin (x i)^(α i)*
          (-(1-(Real.cos (x i))^2)*deriv (deriv (f i)) (Real.cos (x i))+
            (2*(α i:ℝ)+1)*Real.cos (x i)*deriv (f i) (Real.cos (x i))+
            (α i:ℝ)^2*f i (Real.cos (x i))))
    ∃ v : EnergySpace α,∃ g : H α,
      (v.1 : Space d → ℝ)=ᵐ[spatialMeasure α] F ∧
      (∀ i,(v.2.1 i : Space d → ℝ)=ᵐ[spatialMeasure α] partialDerivative i F) ∧
      (∀ i,(v.2.2 i : Space d → ℝ)=ᵐ[spatialMeasure α]
        (fun x => SpatialForm.potentialFactor (α i) (x i)*F x)) ∧
      (g : Space d → ℝ)=ᵐ[spatialMeasure α] G ∧
      v∈formClosure α ∧ ∀ w∈formClosure α,formPairing v w=inner ℝ g w.1

end BecknerOnofri.Friedrichs.MixedSpatial
