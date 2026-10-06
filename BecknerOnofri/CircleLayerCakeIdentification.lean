module

public import BecknerOnofri.CircleLayerCake
public import BecknerOnofri.CircleRearrangementL1Properties

@[expose] public section

noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory Filter Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open DistributionLimit

theorem IsRearrangementLimit.layer_ae {f F : Torus 1 → ℝ}
    (hF : IsRearrangementLimit f F) (hf : Integrable f (torusMeasure 1)) :
    layerRearrangement f=ᵐ[torusMeasure 1] (fun x => ENNReal.ofReal (F x)) := by
  let hM := hF.integrable.aestronglyMeasurable
  have he : F=ᵐ[torusMeasure 1] hM.mk F := hM.ae_eq_mk
  have hD : IdentDistrib (hM.mk F) f (torusMeasure 1) (torusMeasure 1) :=
    (IdentDistrib.of_ae_eq hF.integrable.aemeasurable he).symm.trans (hF.identDistrib hf)
  have hR := AntitoneRadiusAE.congr hF.radial he
  exact (layerRearrangement_eq_ofReal_of_measurable hM.measurable_mk hD hR).trans
    (he.symm.fun_comp ENNReal.ofReal)

theorem IsRearrangementLimit.layer_toReal_ae {f F : Torus 1 → ℝ}
    (hF : IsRearrangementLimit f F) (hf : Integrable f (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1,0≤f x) :
    (fun x => (layerRearrangement f x).toReal)=ᵐ[torusMeasure 1] F := by
  filter_upwards [hF.layer_ae hf,hF.nonneg hf hf0] with x hx hx0
  rw [hx,ENNReal.toReal_ofReal hx0]

theorem layerRearrangement_ae_ne_top {f : Torus 1 → ℝ} (hf : Integrable f (torusMeasure 1)) :
    ∀ᵐ x ∂torusMeasure 1,layerRearrangement f x≠∞ := by
  filter_upwards [(rearrangeL1_spec f hf).layer_ae hf] with x hx
  rw [hx]
  exact ENNReal.ofReal_ne_top

theorem layer_toReal_isRearrangementLimit {f : Torus 1 → ℝ}
    (hf : Integrable f (torusMeasure 1)) (hf0 : ∀ᵐ x ∂torusMeasure 1,0≤f x) :
    IsRearrangementLimit f (fun x => (layerRearrangement f x).toReal) :=
  (rearrangeL1_spec f hf).congr ((rearrangeL1_spec f hf).layer_toReal_ae hf hf0).symm

#print axioms IsRearrangementLimit.layer_ae
#print axioms IsRearrangementLimit.layer_toReal_ae
#print axioms layerRearrangement_ae_ne_top
#print axioms layer_toReal_isRearrangementLimit
end BecknerOnofri.PolarizationL1
