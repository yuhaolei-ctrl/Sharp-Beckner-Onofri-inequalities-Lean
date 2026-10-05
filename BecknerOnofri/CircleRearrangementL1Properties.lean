module

public import BecknerOnofri.CircleRearrangementL1Limit
public import BecknerOnofri.CircleRadialKernel

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.PolarizationL1
open RearrangementApproximation DistributionLimit BilinearPolarization

theorem IsRearrangementLimit.congr {f F G : Torus 1 → ℝ}
    (hF : IsRearrangementLimit f F) (he : F=ᵐ[torusMeasure 1] G) : IsRearrangementLimit f G := by
  obtain ⟨u,K,hK,hu,hFu⟩ := hF.approximation
  refine ⟨hF.integrable.congr he,⟨u,K,hK,hu,?_⟩⟩
  apply hFu.congr'
  exact Filter.Eventually.of_forall (fun n => integral_congr_ae
    (he.mono (fun x hx => by dsimp only; rw [hx])))

theorem IsRearrangementLimit.nonneg {f F : Torus 1 → ℝ}
    (hF : IsRearrangementLimit f F) (hf : Integrable f (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1,0≤f x) : ∀ᵐ x ∂torusMeasure 1,0≤F x :=
  (hF.identDistrib hf).symm.ae_snd measurableSet_Ici hf0

lemma ae_le_of_l1_distance_le_integral_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G : α → ℝ} (hF : Integrable F μ) (hG : Integrable G μ)
    (h : (∫ x,‖F x-G x‖ ∂μ)≤(∫ x,G x ∂μ)-(∫ x,F x ∂μ)) : F≤ᵐ[μ] G := by
  have hle : (fun x => G x-F x)≤ᵐ[μ] (fun x => ‖G x-F x‖) :=
    Filter.Eventually.of_forall (fun x => le_abs_self (G x-F x))
  have hi := integral_mono_ae (hG.sub hF) (hG.sub hF).norm hle
  have he : (∫ x,G x-F x ∂μ)=(∫ x,‖G x-F x‖ ∂μ) := by
    apply le_antisymm hi
    change (∫ x,‖G x-F x‖ ∂μ)≤∫ x,G x-F x ∂μ
    rw [integral_sub hG hF]
    simpa only [norm_sub_rev] using h
  have hae := (integral_eq_iff_of_ae_le (hG.sub hF) (hG.sub hF).norm hle).mp he
  filter_upwards [hae] with x hx
  have hn := norm_nonneg (G x-F x)
  change G x-F x=‖G x-F x‖ at hx
  linarith

theorem IsRearrangementLimit.mono {f g F G : Torus 1 → ℝ}
    (hF : IsRearrangementLimit f F) (hG : IsRearrangementLimit g G)
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1))
    (hfg : f≤ᵐ[torusMeasure 1] g) : F≤ᵐ[torusMeasure 1] G := by
  apply ae_le_of_l1_distance_le_integral_sub hF.integrable hG.integrable
  have hi : (∫ x,‖f x-g x‖ ∂torusMeasure 1)=
      (∫ x,g x ∂torusMeasure 1)-(∫ x,f x ∂torusMeasure 1) := by
    rw [← integral_sub hg hf]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  have h := hF.l1_contraction hG hf hg
  rw [hi,← (hF.identDistrib hf).integral_eq,← (hG.identDistrib hg).integral_eq] at h
  exact h

theorem IsRearrangementLimit.circle_pairing_le {f g F G : Torus 1 → ℝ}
    (hF : IsRearrangementLimit f F) (hG : IsRearrangementLimit g G)
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1))
    (q : UnitAddCircle → ℝ) {C : ℝ} (hC : ∀ z,‖q z‖≤C)
    (hq : ∀ x y,‖x‖≤‖y‖ → q y≤q x) :
    pairing (fun x y : Torus 1 => q (x 0-y 0)) f g≤
      pairing (fun x y : Torus 1 => q (x 0-y 0)) F G := by
  obtain ⟨u,K,hK,hu,hFu⟩ := hF.approximation
  obtain ⟨v,L,hL,hv,hGv⟩ := hG.approximation
  have hm := circle_radial_kernel_measurable hq
  have hqm : Measurable (Function.uncurry (fun x y : Torus 1 => q (x 0-y 0))) := by
    have hs : Continuous (fun p : Torus 1 × Torus 1 => p.1 0-p.2 0) := by fun_prop
    exact hm.comp hs.measurable
  have hi := pairing_l1_limit atTop (fun x y : Torus 1 => q (x 0-y 0)) hqm
    (fun x y => hC (x 0-y 0)) (fun n => u n) (fun n => v n) f g
    (fun n => (u n).integrable _) (fun n => (v n).integrable _) hf hg hu hv
  have ho := pairing_l1_limit atTop (fun x y : Torus 1 => q (x 0-y 0)) hqm
    (fun x y => hC (x 0-y 0))
    (fun n => rearrangeLipschitz (u n) (hK n)) (fun n => rearrangeLipschitz (v n) (hL n)) F G
    (fun n => (rearrangeLipschitz (u n) (hK n)).integrable _)
    (fun n => (rearrangeLipschitz (v n) (hL n)).integrable _) hF.integrable hG.integrable hFu hGv
  exact le_of_tendsto_of_tendsto hi ho (Filter.Eventually.of_forall (fun n =>
    rearrangeLipschitz_circle_pairing q hm hC hq (u n) (v n) (hK n) (hL n)))

#print axioms IsRearrangementLimit.mono
#print axioms IsRearrangementLimit.circle_pairing_le
end BecknerOnofri.PolarizationL1
