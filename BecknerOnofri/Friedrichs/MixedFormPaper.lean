import BecknerOnofri.Friedrichs.MixedStatementDefinitions
import BecknerOnofri.Friedrichs.MixedAngularFormDomain

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.MixedSpatial

theorem tensor_form_domain (d : ℕ) : TensorFormDomain d := by
  intro α f hf
  refine ⟨angularLift α f hf,angular_mem_formClosure α f hf,?_,?_,?_⟩
  · exact (angular_memLp α f hf).coeFn_toLp
  · intro i
    exact (angular_partial_memLp α f hf i).coeFn_toLp
  · intro i
    exact (angular_potential_memLp α f hf i).coeFn_toLp

#print axioms tensor_form_domain
end BecknerOnofri.Friedrichs.MixedSpatial
