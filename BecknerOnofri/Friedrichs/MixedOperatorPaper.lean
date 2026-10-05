import BecknerOnofri.Friedrichs.MixedOperatorStatementDefinitions
import BecknerOnofri.Friedrichs.MixedAngularOperator

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

theorem tensor_operator_conjugation (d : ℕ) : TensorOperatorConjugation d := by
  intro α f hf
  refine ⟨angularLift α f hf,angularOperatorImageLp α f hf,?_,?_,?_,?_,
    angular_mem_formClosure α f hf,core_test_extends (angular_core_equation α f hf)⟩
  · exact (angular_memLp α f hf).coeFn_toLp
  · intro i
    exact (angular_partial_memLp α f hf i).coeFn_toLp
  · intro i
    exact (angular_potential_memLp α f hf i).coeFn_toLp
  · exact (continuous_memLp α (angularOperatorImage_continuous α f hf)).coeFn_toLp

#print axioms tensor_operator_conjugation
end BecknerOnofri.Friedrichs.MixedSpatial
