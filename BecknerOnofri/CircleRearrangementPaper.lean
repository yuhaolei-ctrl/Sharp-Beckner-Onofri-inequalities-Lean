module

public import BecknerOnofri.CircleLayerCakeIdentification

@[expose] public section

/-! The circle rearrangement lemma on the complete nonnegative L1 domain.
The layer-cake functions are genuine extended-nonnegative canonical
representatives; their real versions agree with them outside a null set. -/
noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory Filter Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open DistributionLimit BilinearPolarization

theorem circle_rearrangement (f g : Torus 1 → ℝ)
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1,0≤f x) (hg0 : ∀ᵐ x ∂torusMeasure 1,0≤g x)
    (q : UnitAddCircle → ℝ) {C : ℝ} (hq0 : ∀ z,0≤q z) (hqC : ∀ z,q z≤C)
    (hq : ∀ x y,‖x‖≤‖y‖ → q y≤q x) :
    let F := fun x => (layerRearrangement f x).toReal
    let G := fun x => (layerRearrangement g x).toReal
    (∀ᵐ x ∂torusMeasure 1,layerRearrangement f x≠∞) ∧
    (∀ᵐ x ∂torusMeasure 1,layerRearrangement g x≠∞) ∧
    Integrable F (torusMeasure 1) ∧ Integrable G (torusMeasure 1) ∧
    IdentDistrib F f (torusMeasure 1) (torusMeasure 1) ∧
    IdentDistrib G g (torusMeasure 1) (torusMeasure 1) ∧
    AntitoneRadiusAE (torusMeasure 1) (fun x : Torus 1 => ‖x 0‖) F ∧
    AntitoneRadiusAE (torusMeasure 1) (fun x : Torus 1 => ‖x 0‖) G ∧
    pairing (fun x y : Torus 1 => q (x 0-y 0)) f g≤
      pairing (fun x y : Torus 1 => q (x 0-y 0)) F G ∧
    (∫ x,|F x-G x| ∂torusMeasure 1)≤∫ x,|f x-g x| ∂torusMeasure 1 ∧
    ((∀ x,f x≤g x) → ∀ x,layerRearrangement f x≤layerRearrangement g x) := by
  dsimp only
  have hF := layer_toReal_isRearrangementLimit hf hf0
  have hG := layer_toReal_isRearrangementLimit hg hg0
  have hC : ∀ z,‖q z‖≤C := fun z => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hq0 z)] using hqC z
  refine ⟨layerRearrangement_ae_ne_top hf,layerRearrangement_ae_ne_top hg,
    hF.integrable,hG.integrable,hF.identDistrib hf,hG.identDistrib hg,hF.radial,hG.radial,
    hF.circle_pairing_le hG hf hg q hC hq,?_,?_⟩
  · simpa only [Real.norm_eq_abs] using hF.l1_contraction hG hf hg
  · intro hfg
    exact layerRearrangement_mono (Filter.Eventually.of_forall hfg)

#print axioms circle_rearrangement
end BecknerOnofri.PolarizationL1
