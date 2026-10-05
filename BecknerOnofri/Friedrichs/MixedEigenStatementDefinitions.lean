import BecknerOnofri.Friedrichs.MixedSpatialDefinitions
import Mathlib.RingTheory.Polynomial.Chebyshev

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

/-- Finite cosine modes after the sine-weighted differentiated Chebyshev
transform lie in the actual mixed spatial graph with eigenvalue |n|^2. -/
def ChebyshevSpatialEigenvectors (d : ℕ) : Prop :=
  ∀ α n : MultiIndex d,∃ v : H α,
    (v : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => ∏ i,Real.sin (x i)^(α i)*
        (Polynomial.derivative^[α i] (Polynomial.Chebyshev.T ℝ (n i:ℤ))).eval (Real.cos (x i))) ∧
      operatorGraph α v ((∑ i,(n i:ℝ)^2) • v)

end BecknerOnofri.Friedrichs.MixedSpatial
