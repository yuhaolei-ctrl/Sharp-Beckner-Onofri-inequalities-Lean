import BecknerOnofri.PhysicalBranchProperties

/-! Actual continuous representatives of each spatial translation tangent of
the physical branch, for the raw L² orthogonality in the trusted statement. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.PhysicalTranslationTangents
open ContinuousGibbs ContinuousFirstShell GraphTranslationTangents DiagonalScalarBranch

def physicalTangent {d : ℕ} (hd : 12 ≤ d) (β : ℝ) (j : Fin d) : Space d :=
  tangent hd (parameter hd (amplitude hd (β/spectralThreshold d)),
    ReducedCubicExpansion.realDiagonal d (amplitude hd (β/spectralThreshold d))) j

theorem coordinateDerivative_eq {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ j : Fin d,
      coordinateDerivative (physicalPotential hd β) j = (physicalTangent hd β j : Torus d → ℝ) := by
  filter_upwards [(PhysicalBranchProperties.physical_graph_tendsto hd).eventually
    (tangent_eq_coordinateDerivative hd)] with β hb j
  funext x
  exact (hb j x).symm

theorem coordinateDerivative_memLp {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ j : Fin d,
      MemLp (coordinateDerivative (physicalPotential hd β) j) 2 (torusMeasure d) := by
  filter_upwards [coordinateDerivative_eq hd] with β hb j
  rw [hb j]
  exact (physicalTangent hd β j).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

#print axioms coordinateDerivative_memLp
end BecknerOnofri.HighDim.PhysicalTranslationTangents
