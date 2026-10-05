import BecknerOnofri.ReducedQuarticAnalytic
import BecknerOnofri.AnalyticEvenOrder
import BecknerOnofri.FirstShellOrbits
import BecknerOnofri.ReducedPhysicalEnergy

/-! The actual critical reduced pressure has a sixth-order remainder.
The improvement follows from analyticity and genuine half-period translation symmetry. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.ReducedQuarticExpansion
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry QuadraticModes

theorem graphExpression_even {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), graphExpression hd (-z) = graphExpression hd z := by
  filter_upwards [graphExpression_translation hd] with z hz
  simpa only [phase_allHalfTranslation] using hz (allHalfTranslation d)

theorem quarticValue_even {d : ℕ} (z : Coordinates d) : quarticValue (-z) = quarticValue z := by
  simp only [quarticValue, mixedAmplitudeSum, Pi.neg_apply, norm_neg]

/-- The exact quartic expansion of the genuine critical graph expression. -/
theorem graphExpression_quartic_sixth {d : ℕ} (hd : 12 ≤ d) :
    (fun z => graphExpression hd z - quarticValue z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^6) := by
  apply analytic_even_fifth_order
    ((graphExpression_analytic hd).sub (quarticValue_analytic hd)) (graphExpression_quartic hd)
  filter_upwards [graphExpression_even hd] with z hz
  change graphExpression hd (-z) - quarticValue (-z) = graphExpression hd z - quarticValue z
  rw [hz, quarticValue_even]

end BecknerOnofri.HighDim.ReducedQuarticExpansion

namespace BecknerOnofri.HighDim.ReducedPhysicalEnergy
open ContinuousFirstShell ReducedQuarticExpansion

/-- This remainder estimate is for the original trusted physical dual functional. -/
theorem criticalReducedEnergy_quartic_sixth {d : ℕ} (hd : 12 ≤ d) :
    (fun z => criticalReducedEnergy hd z - quarticValue z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^6) := by
  exact (graphExpression_quartic_sixth hd).congr'
    ((criticalReducedEnergy_eq hd).sub (Filter.EventuallyEq.rfl)).symm Filter.EventuallyEq.rfl

#print axioms criticalReducedEnergy_quartic_sixth
end BecknerOnofri.HighDim.ReducedPhysicalEnergy
