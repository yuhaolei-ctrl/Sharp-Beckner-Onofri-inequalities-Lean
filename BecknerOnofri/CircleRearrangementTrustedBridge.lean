module

public import BecknerOnofri.CircleRearrangementDefinitions
public import BecknerOnofri.CircleRearrangementPaper

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Legacy.TorusEndpoint
open scoped ENNReal
namespace BecknerOnofri.Circle

theorem circle_rearrangement (f g : Torus 1 → ℝ)
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1,0≤f x) (hg0 : ∀ᵐ x ∂torusMeasure 1,0≤g x)
    (q : UnitAddCircle → ℝ) {C : ℝ} (hq0 : ∀ z,0≤q z) (hqC : ∀ z,q z≤C)
    (hq : ∀ x y,‖x‖≤‖y‖ → q y≤q x) :
    (∀ᵐ x ∂torusMeasure 1,rearrange f x≠∞) ∧
    (∀ᵐ x ∂torusMeasure 1,rearrange g x≠∞) ∧
    Integrable (realRearrange f) (torusMeasure 1) ∧
    Integrable (realRearrange g) (torusMeasure 1) ∧
    IdentDistrib (realRearrange f) f (torusMeasure 1) (torusMeasure 1) ∧
    IdentDistrib (realRearrange g) g (torusMeasure 1) (torusMeasure 1) ∧
    (∀ x y : Torus 1,‖x 0‖≤‖y 0‖ → rearrange f y≤rearrange f x) ∧
    (∀ x y : Torus 1,‖x 0‖≤‖y 0‖ → rearrange g y≤rearrange g x) ∧
    interaction q f g ≤ interaction q (realRearrange f) (realRearrange g) ∧
    (∫ x,|realRearrange f x-realRearrange g x| ∂torusMeasure 1)≤
      ∫ x,|f x-g x| ∂torusMeasure 1 ∧
    ((∀ x,f x≤g x) → ∀ x,rearrange f x≤rearrange g x) := by
  obtain ⟨hfFin,hgFin,hFi,hGi,hFD,hGD,_,_,hpair,hcontract,horder⟩ :=
    PolarizationL1.circle_rearrangement f g hf hg hf0 hg0 q hq0 hqC hq
  exact ⟨hfFin,hgFin,hFi,hGi,hFD,hGD,
    fun x y hxy => PolarizationL1.layerRearrangement_radial f hxy,
    fun x y hxy => PolarizationL1.layerRearrangement_radial g hxy,
    hpair,hcontract,horder⟩

#print axioms circle_rearrangement
end BecknerOnofri.Circle
