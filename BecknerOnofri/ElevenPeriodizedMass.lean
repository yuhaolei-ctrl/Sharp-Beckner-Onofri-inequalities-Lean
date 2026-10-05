import BecknerOnofri.ElevenPeriodizedSummability
import BecknerOnofri.PeriodizationCube
import BecknerOnofri.LegacyBridge
import Legacy.TorusEndpoint.PhysicalGreenL2

/-! The explicitly periodized competitor is a genuine probability density.
Its mass is obtained by unfolding the fundamental cube, not by renormalizing. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BecknerOnofri.HighDim.Eleven

lemma representative_measurable : Measurable representative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1:ℝ) (-(1/2:ℝ))).measurable

lemma periodizedProfile_measurable : Measurable periodizedProfile := by
  apply Measurable.tsum
  intro n
  apply euclideanProfile_continuous.measurable.comp
  apply measurable_pi_lambda
  intro i
  exact (representative_measurable.comp (measurable_pi_apply i)).add_const (n i : ℝ)

lemma periodizedProfile_on_cube {x : Fin 11 → ℝ} (hx : x ∈ PeriodizationCube.cube 11) :
    periodizedProfile (fun i => (x i : UnitAddCircle)) =
      ∑' n : Frequency 11, euclideanProfile (fun i => x i+(n i:ℝ)) := by
  apply tsum_congr
  intro n
  congr 1
  funext i
  congr 1
  unfold representative
  rw [AddCircle.equivIco_coe_eq (by
    simpa only [show -(1/2:ℝ)+1 = 1/2 by norm_num] using hx i (mem_univ i))]

lemma periodizedProfile_lintegral :
    (∫⁻ x, ENNReal.ofReal (periodizedProfile x) ∂torusMeasure 11) = 1 := by
  rw [← (PeriodizationCube.quotient_measurePreserving 11).lintegral_comp
    periodizedProfile_measurable.ennreal_ofReal]
  calc
    _ = ∫⁻ x in PeriodizationCube.cube 11, ∑' n : Frequency 11,
        ENNReal.ofReal (euclideanProfile (fun i => x i+(n i:ℝ))) := by
      apply setLIntegral_congr_fun (PeriodizationCube.cube_measurable 11)
      intro x hx
      dsimp only
      rw [periodizedProfile_on_cube hx]
      exact ENNReal.ofReal_tsum_of_nonneg (fun n => (euclideanProfile_pos _).le)
        (translated_profile_summable x)
    _ = ∫⁻ x : Fin 11 → ℝ, ENNReal.ofReal (euclideanProfile x) :=
      PeriodizationCube.unfold_lintegral 11 _ euclideanProfile_continuous.measurable.ennreal_ofReal
    _ = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal euclideanProfile_integrable
        (ae_of_all _ (fun x => (euclideanProfile_pos x).le)), euclideanProfile_integral,
        ENNReal.ofReal_one]

lemma periodizedProfile_integral : (∫ x, periodizedProfile x ∂torusMeasure 11) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => (periodizedProfile_pos x).le))
    periodizedProfile_measurable.aestronglyMeasurable, periodizedProfile_lintegral]
  rfl

lemma periodizedProfile_integrable : Integrable periodizedProfile (torusMeasure 11) := by
  apply Integrable.of_integral_ne_zero
  rw [periodizedProfile_integral]
  norm_num

/-- The value is exactly the specified profile, without a scaling correction. -/
def competitorDensity : ProbabilityDensity 11 where
  value := periodizedProfile
  nonneg := ae_of_all _ (fun x => (periodizedProfile_pos x).le)
  integrable := periodizedProfile_integrable
  mass := periodizedProfile_integral

lemma representative_abs_le (x : UnitAddCircle) : |representative x| ≤ 1/2 := by
  have h := (AddCircle.equivIco (1:ℝ) (-(1/2:ℝ)) x).property
  change -(1/2:ℝ) ≤ representative x ∧ representative x < -(1/2:ℝ)+1 at h
  exact abs_le.mpr ⟨h.1, by linarith [h.2]⟩

lemma periodizedProfile_bounded : ∃ M : ℝ, ∀ x, ‖periodizedProfile x‖ ≤ M := by
  let b : Frequency 11 → ℝ := fun n =>
    ((5:ℝ)^11 * (122880 / Real.pi^6) * (2+22*(1/2:ℝ)^2)^11) *
      Legacy.TorusEndpoint.GreenMultiplierSummability.productMajorant n
  have hb : Summable b :=
    (Legacy.TorusEndpoint.GreenMultiplierSummability.summable_productMajorant 11).mul_left _
  refine ⟨∑' n, b n, fun x => ?_⟩
  rw [Real.norm_eq_abs, abs_of_pos (periodizedProfile_pos x)]
  apply (periodizedProfile_summable x).tsum_le_tsum _ hb
  intro n
  exact translated_profile_majorant _ n (by norm_num) (fun i => representative_abs_le (x i))

lemma competitorDensity_finiteEntropy : competitorDensity.FiniteEntropy := by
  obtain ⟨M, hM⟩ := periodizedProfile_bounded
  have hL2 : MemLp periodizedProfile 2 (torusMeasure 11) :=
    MemLp.of_bound periodizedProfile_measurable.aestronglyMeasurable M (ae_of_all _ hM)
  exact Legacy.TorusEndpoint.PhysicalGreenL2.finiteEntropy_of_memLp
    (Bridge.density competitorDensity) hL2

#print axioms competitorDensity_finiteEntropy

#print axioms periodizedProfile_integral
end BecknerOnofri.HighDim.Eleven
