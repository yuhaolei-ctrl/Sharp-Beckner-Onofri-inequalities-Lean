module

public import BecknerOnofri.Friedrichs.MixedFractionalIntertwining
public import BecknerOnofri.Friedrichs.MixedDerivativeList

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace BecknerOnofri.Friedrichs.MixedSpatial

/-- Manuscript Lemma fractional, with its original smooth closed-cube input
and every nonzero multi-index on the original mixed spatial measure. -/
theorem fractional_intertwining (d : ℕ) : FractionalIntertwining d := by
  intro U hU α hα s hs
  have hrep : ∀ x : Fin d → ℝ,cosineLift U (Legacy.BecknerOnofri.SmoothFourier.quotient x)=
      U (Legacy.BecknerOnofri.ChebyshevProfile.cosinePoint x) := by
    intro x
    apply congrArg U
    ext i
    exact Legacy.BecknerOnofri.CosineMomentWeight.circleCos_coe (x i)
  have h := MixedFractional.smooth_profile_intertwining hU hrep s hs (derivativeList α)
  rw [countIndex_derivativeList] at h
  simp only [Legacy.BecknerOnofri.AngularMixedTerms.weight,
    derivativeList_count] at h
  obtain ⟨Us,hUs,hrepUs,f,g,hf,hg,hG⟩ := h
  refine ⟨Us,hUs,hrepUs,?_,f,g,hf,hg,hG⟩
  exact SmoothTorus.angularPower_fourier (SmoothCosine.smooth_of_representation hU hrep) s hs.le

#print axioms fractional_intertwining
end BecknerOnofri.Friedrichs.MixedSpatial
