import BecknerOnofri.CircleLipschitzRearrangement
import BecknerOnofri.LipschitzL1Sequence
import BecknerOnofri.L1DistanceLimits
import BecknerOnofri.DistributionJointL1Limit
import BecknerOnofri.DistributionAERadialUniqueness

/-! The unique L1 extension of the genuine Lipschitz circle rearrangement.
Its distribution and radial antitonicity are proved from actual limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.PolarizationL1
open RearrangementApproximation DistributionLimit

structure IsRearrangementLimit (f F : Torus 1 → ℝ) : Prop where
  integrable : Integrable F (torusMeasure 1)
  approximation : ∃ u : ℕ → Torus 1 →ᵇ ℝ,∃ K : ℕ → ℝ≥0,
    ∃ hK : ∀ n,LipschitzWith (K n) (u n),
      Tendsto (fun n => ∫ x,‖u n x-f x‖ ∂torusMeasure 1) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x,‖rearrangeLipschitz (u n) (hK n) x-F x‖ ∂torusMeasure 1) atTop (𝓝 0)

theorem exists_rearrangement_limit {f : Torus 1 → ℝ} (hf : Integrable f (torusMeasure 1)) :
    ∃ F : Torus 1 → ℝ,IsRearrangementLimit f F := by
  obtain ⟨u,K,hK,hu⟩ := exists_lipschitz_l1_sequence hf
  obtain ⟨F,hF,hlim⟩ := exists_l1_limit_of_contractive_sequence
    (fun n => (u n).integrable _)
    (fun n => (rearrangeLipschitz (u n) (hK n)).integrable _) hf hu
    (fun n m => rearrangeLipschitz_l1_contraction (u n) (u m) (hK n) (hK m))
  exact ⟨F,hF,⟨u,K,hK,hu,hlim⟩⟩

theorem IsRearrangementLimit.l1_contraction {f g F G : Torus 1 → ℝ}
    (hF : IsRearrangementLimit f F) (hG : IsRearrangementLimit g G)
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1)) :
    (∫ x,‖F x-G x‖ ∂torusMeasure 1)≤∫ x,‖f x-g x‖ ∂torusMeasure 1 := by
  obtain ⟨u,K,hK,hu,hFu⟩ := hF.approximation
  obtain ⟨v,L,hL,hv,hGv⟩ := hG.approximation
  have hi := integral_distance_tendsto (fun n => (u n).integrable _)
    (fun n => (v n).integrable _) hf hg hu hv
  have ho := integral_distance_tendsto
    (fun n => (rearrangeLipschitz (u n) (hK n)).integrable _)
    (fun n => (rearrangeLipschitz (v n) (hL n)).integrable _)
    hF.integrable hG.integrable hFu hGv
  exact le_of_tendsto_of_tendsto ho hi (Filter.Eventually.of_forall
    (fun n => rearrangeLipschitz_l1_contraction (u n) (v n) (hK n) (hL n)))

theorem IsRearrangementLimit.unique {f F G : Torus 1 → ℝ}
    (hF : IsRearrangementLimit f F) (hG : IsRearrangementLimit f G)
    (hf : Integrable f (torusMeasure 1)) : F=ᵐ[torusMeasure 1] G := by
  apply ae_eq_of_l1_distance_zero hF.integrable hG.integrable
  apply le_antisymm _ (integral_nonneg (fun x => norm_nonneg _))
  simpa using hF.l1_contraction hG hf hf

theorem IsRearrangementLimit.identDistrib {f F : Torus 1 → ℝ}
    (hF : IsRearrangementLimit f F) (hf : Integrable f (torusMeasure 1)) :
    IdentDistrib F f (torusMeasure 1) (torusMeasure 1) := by
  obtain ⟨u,K,hK,hu,hFu⟩ := hF.approximation
  exact identDistrib_of_joint_l1
    (fun n => (rearrangeLipschitz (u n) (hK n)).integrable _)
    (fun n => (u n).integrable _) hF.integrable hf
    (fun n => (rearrangeLipschitz_spec (u n) (hK n)).2.2.1) hFu hu

theorem IsRearrangementLimit.radial {f F : Torus 1 → ℝ} (hF : IsRearrangementLimit f F) :
    AntitoneRadiusAE (torusMeasure 1) (fun x : Torus 1 => ‖x 0‖) F := by
  obtain ⟨u,K,hK,hu,hFu⟩ := hF.approximation
  have hi := inMeasure_of_l1
    (fun n => (rearrangeLipschitz (u n) (hK n)).integrable _) hF.integrable hFu
  obtain ⟨ns,_,hns⟩ := hi.exists_seq_tendsto_ae
  let s := {x : Torus 1 | Tendsto (fun n => rearrangeLipschitz (u (ns n)) (hK (ns n)) x)
    atTop (𝓝 (F x))}
  refine ⟨s,hns,?_⟩
  intro x hx y hy hxy
  exact le_of_tendsto_of_tendsto hy hx (Filter.Eventually.of_forall (fun n =>
    steiner_antitone_radius (rearrangeLipschitz_spec (u (ns n)) (hK (ns n))).2.2.2 x y hxy))

def rearrangeL1 (f : Torus 1 → ℝ) (hf : Integrable f (torusMeasure 1)) : Torus 1 → ℝ :=
  Classical.choose (exists_rearrangement_limit hf)

theorem rearrangeL1_spec (f : Torus 1 → ℝ) (hf : Integrable f (torusMeasure 1)) :
    IsRearrangementLimit f (rearrangeL1 f hf) := Classical.choose_spec (exists_rearrangement_limit hf)

/-- This identifies the limit construction with every equimeasurable radial
decreasing representative, rather than merely assigning it that name. -/
theorem rearrangeL1_eq_of_radial_identDistrib {f F : Torus 1 → ℝ}
    (hf : Integrable f (torusMeasure 1))
    (hD : IdentDistrib F f (torusMeasure 1) (torusMeasure 1))
    (hR : AntitoneRadiusAE (torusMeasure 1) (fun x : Torus 1 => ‖x 0‖) F) :
    rearrangeL1 f hf=ᵐ[torusMeasure 1] F :=
  ae_eq_of_identDistrib_antitoneRadiusAE
    (((rearrangeL1_spec f hf).identDistrib hf).trans hD.symm)
    (rearrangeL1_spec f hf).radial hR

#print axioms exists_rearrangement_limit
#print axioms IsRearrangementLimit.l1_contraction
#print axioms IsRearrangementLimit.identDistrib
#print axioms IsRearrangementLimit.radial
#print axioms rearrangeL1_eq_of_radial_identDistrib
end BecknerOnofri.PolarizationL1
