import BecknerOnofri.RadialMeasureSpherical
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! The source's exact twelve-dimensional Haar radial-measure estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace BecknerOnofri.HighDim.RadialMeasure

/-- The interior sine-square radial estimate, for arbitrary nonnegative measurable data. -/
theorem haar_radial_twelve (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x in {x : Torus 12 | ArcsineProductBins.radialSum x < 1},
      F (ArcsineProductBins.radialSum x) ∂torusMeasure 12) ≤
    ENNReal.ofReal ((Real.pi^6/120) / Real.pi^12) *
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (s^5 / Real.sqrt (1-s)) * F s := by
  refine (haar_radial_le_ball F hF).trans_eq ?_
  rw [pi_ball_squared_radius (fun s => ENNReal.ofReal (1/(Real.pi^12*Real.sqrt (1-s)))*F s) (by fun_prop)]
  have he : ∀ s : ℝ, ENNReal.ofReal (s^5) *
      (ENNReal.ofReal (1 / (Real.pi^12*Real.sqrt (1-s)))*F s) =
      (ENNReal.ofReal (Real.pi^12))⁻¹ * (ENNReal.ofReal (s^5 / Real.sqrt (1-s))*F s) := by
    intro s
    rw [← mul_assoc,← ENNReal.ofReal_mul' (by positivity : 0 ≤ 1 / (Real.pi^12*Real.sqrt (1-s)))]
    rw [show s^5 * (1/(Real.pi^12*Real.sqrt (1-s))) =
      (1/Real.pi^12)*(s^5/Real.sqrt (1-s)) by ring]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1/Real.pi^12),ENNReal.ofReal_div_of_pos (by positivity)]
    simp [mul_assoc]
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop),← mul_assoc]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < Real.pi^12)]
  simp only [div_eq_mul_inv]

/-- Real-valued version, including the integrability furnished by the estimate. -/
theorem haar_radial_twelve_real (F : ℝ → ℝ) (hF : Measurable F)
    (hn : ∀ s, 0 ≤ F s)
    (hI : IntegrableOn (fun s => (s^5 / Real.sqrt (1-s))*F s) (Ioo (0 : ℝ) 1)) :
    IntegrableOn (fun x : Torus 12 => F (ArcsineProductBins.radialSum x))
      {x | ArcsineProductBins.radialSum x < 1} (torusMeasure 12) ∧
    (∫ x in {x : Torus 12 | ArcsineProductBins.radialSum x < 1},
      F (ArcsineProductBins.radialSum x) ∂torusMeasure 12) ≤
      ((Real.pi^6/120)/Real.pi^12) *
        ∫ s in Ioo (0 : ℝ) 1, (s^5/Real.sqrt (1-s))*F s := by
  have hb := haar_radial_twelve (fun s => ENNReal.ofReal (F s)) (by fun_prop)
  have he : (∫⁻ s in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (s^5/Real.sqrt (1-s))*ENNReal.ofReal (F s)) =
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal ((s^5/Real.sqrt (1-s))*F s) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro s hs
    exact (ENNReal.ofReal_mul' (hn s)).symm
  rw [he] at hb
  have hright : ENNReal.ofReal ((Real.pi^6/120)/Real.pi^12) *
      (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal ((s^5/Real.sqrt (1-s))*F s)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI.lintegral_lt_top
  have hm : AEStronglyMeasurable (fun x : Torus 12 => F (ArcsineProductBins.radialSum x))
      ((torusMeasure 12).restrict {x | ArcsineProductBins.radialSum x < 1}) :=
    (hF.comp (ArcsineProductBins.radialSum_continuous 12).measurable).aestronglyMeasurable
  have hp : 0 ≤ᵐ[(torusMeasure 12).restrict {x : Torus 12 | ArcsineProductBins.radialSum x < 1}]
      (fun x => F (ArcsineProductBins.radialSum x)) := Filter.Eventually.of_forall fun x => hn _
  refine ⟨⟨hm,(hasFiniteIntegral_iff_ofReal hp).mpr (lt_of_le_of_lt hb hright)⟩,?_⟩
  have hpn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun s => (s^5/Real.sqrt (1-s))*F s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg (div_nonneg (pow_nonneg hs.1.le _) (Real.sqrt_nonneg _)) (hn s)
  have ht := ENNReal.toReal_mono hright.ne hb
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),
    ← integral_eq_lintegral_of_nonneg_ae hp hm,
    ← integral_eq_lintegral_of_nonneg_ae hpn hI.aestronglyMeasurable] at ht
  exact ht

#print axioms haar_radial_twelve_real

#print axioms haar_radial_twelve
end BecknerOnofri.HighDim.RadialMeasure
