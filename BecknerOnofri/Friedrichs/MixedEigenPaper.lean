import BecknerOnofri.Friedrichs.MixedEigenStatementDefinitions
import BecknerOnofri.Friedrichs.MixedChebyshevEigenvectors

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.Friedrichs.MixedSpatial

theorem chebyshev_spatial_eigenvectors (d : ℕ) : ChebyshevSpatialEigenvectors d := by
  intro α n
  exact ⟨chebyshevVector α n,
    (angular_memLp α (chebyshevProfiles α n) (chebyshevProfiles_smooth α n)).coeFn_toLp,
    chebyshevVector_operatorGraph α n⟩

#print axioms chebyshev_spatial_eigenvectors
end BecknerOnofri.Friedrichs.MixedSpatial
