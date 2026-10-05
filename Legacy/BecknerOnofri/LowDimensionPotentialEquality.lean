import Legacy.BecknerOnofri.EndpointEqualityL2
import Legacy.BecknerOnofri.EndpointPotentialEquality

/-! Unconditional equality classification for every real critical Sobolev
potential in dimensions two through ten, in the manuscript normalization. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment EndpointPotential

theorem onofri_equality_iff_zero {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    {u : TorusL2 d} (hu : Admissible u) :
    Real.log (partition u) = coefficient d*criticalEnergy u ↔ u = 0 :=
  equality_iff_zero_of_L2 (by omega) (endpoint_through_ten d (by omega) hd10)
    (fun r hr he => EndpointEqualityL2.uniform_of_equality hd2 hd10 r hr he) hu

theorem onofri_equality_iff_constant {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    {u : TorusL2 d} (hr : RealPotential u)
    (hs : Summable (weightedSquare (fourierIsometry d u))) :
    Real.log (centeredPartition u) =
      (1/(4*(d:ℝ)*endpointSymbolConstant d))*manuscriptEnergy u ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => (c : ℂ) :=
  manuscript_equality_iff_constant_of_L2 (by omega) (endpoint_through_ten d (by omega) hd10)
    (fun r hr he => EndpointEqualityL2.uniform_of_equality hd2 hd10 r hr he) hr hs

#print axioms onofri_equality_iff_zero
#print axioms onofri_equality_iff_constant
end Legacy.BecknerOnofri
