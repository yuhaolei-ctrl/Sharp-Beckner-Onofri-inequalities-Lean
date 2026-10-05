import BecknerOnofri.CoordinateRearrangementDefinitions
import BecknerOnofri.EntropyShearer.L1Marginal

/-! Canonical coordinate rearrangement is well defined on almost-everywhere
classes. Null exceptional sets are enclosed in measurable null sets before
Fubini; no pointwise measurability assumption is imposed on representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CoordinateRearrangementStatement

lemma circleFiber_congr_ae {d : ℕ} (i : Fin d) {f g : Torus d → ℝ}
    (he : f =ᵐ[torusMeasure d] g) :
    ∀ᵐ x ∂torusMeasure d, circleFiber i f x =ᵐ[torusMeasure 1] circleFiber i g x := by
  classical
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp he)
  have hn : ∀ᵐ y ∂torusMeasure d, y ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not,Set.setOf_mem_eq] using hN0
  have hmix := (EntropyShearer.mix_measurePreserving {i}).quasiMeasurePreserving.ae hn
  filter_upwards [Measure.ae_ae_of_ae_prod hmix] with x hx
  have hu : ∀ᵐ y ∂torusMeasure d, Function.update x i (y i) ∉ N := by
    have heq (y : Torus d) : EntropyShearer.mix {i} (x,y)=Function.update x i (y i) := by
      funext j
      by_cases hj : j=i
      · subst j; simp [EntropyShearer.mix]
      · simp [EntropyShearer.mix,Function.update_apply,hj]
    simpa only [heq] using hx
  have hm : Measurable (fun z : UnitAddCircle => Function.update x i z) :=
    measurable_update x
  have hp := measurePreserving_eval (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) i
  have hc : ∀ᵐ z ∂AddCircle.haarAddCircle, Function.update x i z ∉ N := by
    rw [← hp.map_eq]
    exact (ae_map_iff hp.measurable.aemeasurable (hm hNm.compl)).mpr hu
  have h0 := (measurePreserving_eval (fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) 0).quasiMeasurePreserving.ae hc
  filter_upwards [h0] with z hz
  exact Classical.byContradiction (fun hh => hz (hN hh))

lemma realRearrange_congr_ae {f g : Torus 1 → ℝ}
    (he : f =ᵐ[torusMeasure 1] g) : Circle.realRearrange f = Circle.realRearrange g := by
  have hm (t : ℝ) : Legacy.TorusEndpoint.torusMeasure 1 {y | t < f y}=Legacy.TorusEndpoint.torusMeasure 1 {y | t < g y} :=
    measure_congr (he.mono (fun y h => by
      change (t < f y) = (t < g y)
      rw [h]))
  funext x
  simp only [Circle.realRearrange,Circle.rearrange,hm]

#print axioms circleFiber_congr_ae
#print axioms realRearrange_congr_ae
end BecknerOnofri.HighDim.CoordinateRearrangementStatement
