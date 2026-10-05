module

public import BecknerOnofri.Friedrichs.ActiveSpatialSpectrum

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace BecknerOnofri.Friedrichs.MixedSpatial.Active
open Legacy.BecknerOnofri

theorem operatorGraph_iff_coefficients {d : ℕ} (a : MultiIndex d) (f g : H (index a)) :
    operatorGraph (index a) f g ↔ ∀ n,inner ℝ g (JacobiTensor.tensorVector (index a) n)=
      JacobiTensor.tensorEigenvalue (index a) n*inner ℝ f (JacobiTensor.tensorVector (index a) n) := by
  simpa only [HilbertBasis.repr_apply_apply,JacobiTensor.hilbertBasis_apply,real_inner_comm] using
    operatorGraph_iff_repr a f g

theorem operatorGraph_selfAdjoint {d : ℕ} (a : MultiIndex d) (h k : H (index a)) :
    operatorGraph (index a) h k ↔ ∀ f g : H (index a),operatorGraph (index a) f g →
      inner ℝ g h=inner ℝ f k := by
  constructor
  · exact fun hh f g hfg => operatorGraph_symmetric hfg hh
  · intro ht
    apply (operatorGraph_iff_coefficients a h k).mpr
    intro n
    have he := ht _ _ (tensorVector_operatorGraph a n)
    simpa only [inner_smul_left,conj_trivial,real_inner_comm] using he.symm

#print axioms operatorGraph_selfAdjoint
end BecknerOnofri.Friedrichs.MixedSpatial.Active
