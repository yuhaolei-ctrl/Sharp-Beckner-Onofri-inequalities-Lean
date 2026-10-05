import BecknerOnofri.Friedrichs.SpatialFormDefinitions

/-! Trusted spatial statements for the one-dimensional domain argument in
Lemma `fractional`. Profiles here are globally smooth representatives; the
multidimensional mixed-boundary and fractional-power statements are separate. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm

def AngularClosedFormConjugation (m : ℕ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → ∃ v : EnergySpace, ∃ g : H,
    (v.1 : ℝ → ℝ)=ᵐ[intervalMeasure] (fun t => Real.sin t^m*f (Real.cos t)) ∧
    (v.2.1 : ℝ → ℝ)=ᵐ[intervalMeasure] deriv (fun t => Real.sin t^m*f (Real.cos t)) ∧
    (v.2.2 : ℝ → ℝ)=ᵐ[intervalMeasure]
      (fun t => potentialFactor m t*(Real.sin t^m*f (Real.cos t))) ∧
    (g : ℝ → ℝ)=ᵐ[intervalMeasure] (fun t => Real.sin t^m*
      (-(1-(Real.cos t)^2)*deriv (deriv f) (Real.cos t)+
        (2*(m:ℝ)+1)*Real.cos t*deriv f (Real.cos t)+(m:ℝ)^2*f (Real.cos t))) ∧
    v∈formClosure m ∧ ∀ w∈formClosure m,
      inner ℝ v.2.1 w.2.1+inner ℝ v.2.2 w.2.2=inner ℝ g w.1

end BecknerOnofri.Friedrichs.SpatialForm
