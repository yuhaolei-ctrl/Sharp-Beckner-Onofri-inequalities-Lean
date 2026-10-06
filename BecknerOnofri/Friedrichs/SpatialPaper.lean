module

public import BecknerOnofri.Friedrichs.SpatialStatementDefinitions
public import BecknerOnofri.Friedrichs.SpatialOperatorProperties

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm
open Legacy.BecknerOnofri.JacobiAngular

theorem angular_closed_form_conjugation {m : ℕ} (hm : 0<m) :
    AngularClosedFormConjugation m := by
  intro f hf
  refine ⟨angularLift hm hf,angularImageLp m hf,?_,?_,?_,?_,angular_mem_formClosure hm hf,?_⟩
  · exact (continuous_memLp (angular_smooth m hf).continuous).coeFn_toLp
  · exact (continuous_memLp (contDiff_infty_iff_deriv.mp (angular_smooth m hf)).2.continuous).coeFn_toLp
  · exact (potential_memLp (angular_smooth m hf).continuous m (angular_potential_integrable hm hf)).coeFn_toLp
  · have he := (continuous_memLp (angularImage_continuous m hf)).coeFn_toLp
    exact he
  · apply core_test_extends
    intro w hw
    obtain ⟨p,v,hc,ht⟩ := angular_operatorGraph hm hf
    have hp := derivative_component_unique hc (angular_mem_formClosure hm hf) rfl
    have hv := potential_component_unique hc (angular_mem_formClosure hm hf) rfl
    change p=(angularLift hm hf).2.1 at hp
    change v=(angularLift hm hf).2.2 at hv
    subst p
    subst v
    exact ht w hw

#print axioms angular_closed_form_conjugation
end BecknerOnofri.Friedrichs.SpatialForm
