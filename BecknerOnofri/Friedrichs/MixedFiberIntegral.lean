module

public import BecknerOnofri.Friedrichs.MixedSpatialDefinitions
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace BecknerOnofri.Friedrichs.MixedSpatial

/-- Equality of all one-coordinate fiber integrals implies equality of the
actual mixed spatial integrals. Integrability is required on both sides. -/
lemma integral_eq_of_fiber_eq {d : ℕ} (α : MultiIndex d) (i : Fin d)
    {F G : Space d → ℝ} (hF : Integrable F (spatialMeasure α))
    (hG : Integrable G (spatialMeasure α))
    (he : ∀ x : Space d,
      (∫ t,F (Function.update x i t) ∂coordinateMeasure (α i))=
        ∫ t,G (Function.update x i t) ∂coordinateMeasure (α i)) :
    (∫ x,F x ∂spatialMeasure α)=∫ x,G x ∂spatialMeasure α := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
    have hp := (measurePreserving_piFinSuccAbove (fun j => coordinateMeasure (α j)) i).symm
    have hFi := hp.integrable_comp_of_integrable hF
    have hGi := hp.integrable_comp_of_integrable hG
    unfold spatialMeasure
    rw [← hp.integral_comp' F,← hp.integral_comp' G]
    simp only [Function.comp_def] at hFi hGi
    rw [integral_prod_symm _ hFi,integral_prod_symm _ hGi]
    apply integral_congr_ae
    apply ae_of_all
    intro y
    simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Equiv.coe_fn_mk,Fin.update_insertNth] using he (i.insertNth 0 y)

#print axioms integral_eq_of_fiber_eq
end BecknerOnofri.Friedrichs.MixedSpatial
