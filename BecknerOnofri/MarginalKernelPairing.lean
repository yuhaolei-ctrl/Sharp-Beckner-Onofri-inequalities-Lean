import BecknerOnofri.MarginalIntegrablePairing
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! A singular integrable circle kernel pairs with a joint density only
through its actual one-coordinate marginal. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace BecknerOnofri.AdamsEndpoint
open Legacy.BecknerOnofri.TorusMarginals

local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [he]
  infer_instance

theorem torus_sub_left_measurePreserving {d : ℕ} (x : Torus d) :
    MeasurePreserving (fun y => x-y) (torusMeasure d) (torusMeasure d) := by
  letI : (torusMeasure d).IsAddLeftInvariant := by rw [torusMeasure_explicit]; infer_instance
  letI : (torusMeasure d).IsNegInvariant := by
    rw [torusMeasure_explicit]
    infer_instance
  exact Measure.measurePreserving_sub_left _ x

theorem torusMarginalDensity_kernel_pairing {n : ℕ}
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1))
    (K : Torus 1 → ℝ) (hK : Measurable K) (hKi : Integrable K (torusMeasure 1)) :
    (∫ x, ∫ y, K (coordinateCircle i x-coordinateCircle i y) * rho.value x * rho.value y
      ∂torusMeasure (n+1) ∂torusMeasure (n+1)) =
    ∫ x, ∫ y, K (x-y) * (torusMarginalDensity rho hr hpos i).value x *
      (torusMarginalDensity rho hr hpos i).value y ∂torusMeasure 1 ∂torusMeasure 1 := by
  let m := torusMarginalDensity rho hr hpos i
  let V := fun x : Torus 1 => ∫ y, K (x-y) * m.value y ∂torusMeasure 1
  obtain ⟨B,hB⟩ := continuous_norm_bound hr
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hm := torusMarginalDensity_measurable rho hr hpos i
  have hmb (y : Torus 1) : ‖m.value y‖ ≤ B := torusMarginalDensity_norm_bound rho hr hpos i hB y
  have ht (x : Torus 1) : Integrable (fun y => K (x-y)) (torusMeasure 1) :=
    (torus_sub_left_measurePreserving x).integrable_comp_of_integrable hKi
  have hv : Measurable V :=
    ((hK.comp (measurable_fst.sub measurable_snd)).mul (hm.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hvB (x : Torus 1) : ‖V x‖ ≤ B * ∫ y, ‖K y‖ ∂torusMeasure 1 := by
    have hprod := (ht x).mul_bdd hm.aestronglyMeasurable (ae_of_all _ hmb)
    calc
      _ ≤ ∫ y, ‖K (x-y) * m.value y‖ ∂torusMeasure 1 := norm_integral_le_integral_norm _
      _ ≤ ∫ y, ‖K (x-y)‖ * B ∂torusMeasure 1 := by
        apply integral_mono_ae hprod.norm ((ht x).norm.mul_const B)
        exact ae_of_all _ (fun y => by
          change ‖K (x-y) * m.value y‖ ≤ ‖K (x-y)‖ * B
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hmb y) (norm_nonneg _))
      _ = B * ∫ y, ‖K y‖ ∂torusMeasure 1 := by
        rw [integral_mul_const]
        have hh := (torus_sub_left_measurePreserving x).integral_comp
          (measurableEmbedding_subLeft x) (fun y => ‖K y‖)
        change (∫ y, ‖K (x-y)‖ ∂torusMeasure 1) = ∫ y, ‖K y‖ ∂torusMeasure 1 at hh
        rw [hh,mul_comm]
  have hinner (x : Torus (n+1)) :
      (∫ y, K (coordinateCircle i x-coordinateCircle i y) * rho.value x * rho.value y
        ∂torusMeasure (n+1)) = rho.value x * V (coordinateCircle i x) := by
    have hp := torusMarginalDensity_pairing_integrable rho hr hpos i
      (fun z => K (coordinateCircle i x-z))
      (hK.comp (measurable_const.sub measurable_id)) (ht (coordinateCircle i x))
    calc
      _ = rho.value x * ∫ y, rho.value y * K (coordinateCircle i x-coordinateCircle i y)
          ∂torusMeasure (n+1) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun y => by ring)
      _ = rho.value x * V (coordinateCircle i x) := by
        rw [hp]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ (fun y => mul_comm _ _)
  simp_rw [hinner]
  change (∫ x, rho.value x * V (fun _ : Fin 1 => x i) ∂torusMeasure (n+1)) = _
  rw [torusMarginalDensity_pairing rho hr hpos i hv hvB]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only [V]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by dsimp only [m]; ring)

#print axioms torusMarginalDensity_kernel_pairing
end BecknerOnofri.AdamsEndpoint
