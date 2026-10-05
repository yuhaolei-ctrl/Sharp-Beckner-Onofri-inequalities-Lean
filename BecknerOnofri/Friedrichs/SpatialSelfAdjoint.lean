import BecknerOnofri.Friedrichs.SpatialSpectralIdentification

/-! Self-adjointness is stated as equality of the actual graph with its adjoint
graph, rather than as symmetry alone. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.Friedrichs.SpatialForm
open Legacy.BecknerOnofri.JacobiEigenfunctions (eigenvalue normalizedVector hilbertBasis hilbertBasis_apply)

theorem operatorGraph_iff_normalized_coefficients {m : ℕ} (hm : 0<m) (f g : H) :
    operatorGraph m f g ↔ ∀ n,inner ℝ g (normalizedVector m n)=
      eigenvalue m n*inner ℝ f (normalizedVector m n) := by
  simpa only [HilbertBasis.repr_apply_apply,hilbertBasis_apply,real_inner_comm] using
    operatorGraph_iff_repr hm f g

theorem operatorGraph_selfAdjoint {m : ℕ} (hm : 0<m) (h k : H) :
    operatorGraph m h k ↔ ∀ f g : H,operatorGraph m f g → inner ℝ g h=inner ℝ f k := by
  constructor
  · exact fun hh f g hfg => operatorGraph_symmetric hfg hh
  · intro ht
    apply (operatorGraph_iff_normalized_coefficients hm h k).mpr
    intro n
    have he := ht _ _ (normalizedVector_operatorGraph hm n)
    simpa only [inner_smul_left,conj_trivial,real_inner_comm] using he.symm

theorem operatorGraph_domain_total {m : ℕ} (hm : 0<m) (h : H)
    (hh : ∀ f g : H,operatorGraph m f g → inner ℝ h f=0) : h=0 := by
  apply Legacy.BecknerOnofri.JacobiEigenfunctions.eq_zero_of_orthogonal_normalizedVector h m
  intro n
  exact hh _ _ (normalizedVector_operatorGraph hm n)

#print axioms operatorGraph_selfAdjoint
#print axioms operatorGraph_domain_total
end BecknerOnofri.Friedrichs.SpatialForm
