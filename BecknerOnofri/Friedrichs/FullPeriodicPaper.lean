module

public import BecknerOnofri.Friedrichs.FullPeriodicStatementDefinitions
public import BecknerOnofri.Friedrichs.PeriodicHilbertBasis

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.Friedrichs.MixedSpatial

theorem full_spatial_eigenvectors (d : ℕ) : FullSpatialEigenvectors d := by
  intro α n odd
  refine ⟨fullEigenvector α n odd,?_,fullEigenvector_operatorGraph α n odd⟩
  have h := (profile_memLp α (fullEigenprofiles α n odd) (fullEigenprofiles_smooth α n odd)).coeFn_toLp
  filter_upwards [h] with x hx
  change fullEigenvector α n odd x=productProfile (fullEigenprofiles α n odd) x at hx
  rw [hx]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hm : α i=0 <;>
    simp [fullEigenprofiles,fullEigenprofile,hm,periodicMode,
      Legacy.BecknerOnofri.JacobiAngular.angular]

theorem full_coordinate_totality : FullCoordinateTotality := by
  intro m f h
  apply coordinate_fullEigenprofile_total m f
  intro odd n
  by_cases hm : m=0 <;>
    simpa [fullEigenprofile,hm,periodicMode,Legacy.BecknerOnofri.JacobiAngular.angular] using h odd n

theorem full_periodic_hilbert_basis : FullPeriodicHilbertBasis := by
  refine ⟨PeriodicBasis.hilbertBasis,?_,?_⟩
  · intro n
    filter_upwards [Lp.coeFn_smul (Real.sqrt (PeriodicBasis.normSquared (.inl n)))⁻¹
        (PeriodicBasis.rawVector (.inl n)),(PeriodicBasis.rawFunction_memLp (.inl n)).coeFn_toLp] with t hs hr
    change PeriodicBasis.rawVector (.inl n) t=PeriodicBasis.rawFunction (.inl n) t at hr
    simp only [Pi.smul_apply,smul_eq_mul,hr] at hs
    simpa [PeriodicBasis.hilbertBasis_apply,PeriodicBasis.normalizedVector,PeriodicBasis.normSquared,
      PeriodicBasis.rawVector,PeriodicBasis.rawFunction,periodicMode,hr] using hs
  · intro n
    filter_upwards [Lp.coeFn_smul (Real.sqrt (PeriodicBasis.normSquared (.inr n)))⁻¹
        (PeriodicBasis.rawVector (.inr n)),(PeriodicBasis.rawFunction_memLp (.inr n)).coeFn_toLp] with t hs hr
    change PeriodicBasis.rawVector (.inr n) t=PeriodicBasis.rawFunction (.inr n) t at hr
    simp only [Pi.smul_apply,smul_eq_mul,hr] at hs
    simpa [PeriodicBasis.hilbertBasis_apply,PeriodicBasis.normalizedVector,PeriodicBasis.normSquared,
      PeriodicBasis.rawVector,PeriodicBasis.rawFunction,periodicMode,hr] using hs

#print axioms full_spatial_eigenvectors
#print axioms full_coordinate_totality
#print axioms full_periodic_hilbert_basis
end BecknerOnofri.Friedrichs.MixedSpatial
