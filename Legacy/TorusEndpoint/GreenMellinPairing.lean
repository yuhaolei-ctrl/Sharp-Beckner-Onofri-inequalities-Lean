module

public import Legacy.TorusEndpoint.GreenMellinSeries
public import Legacy.TorusEndpoint.TorusHeatPairing
public import Legacy.TorusEndpoint.IntegrableSeries

@[expose] public section

/-!
# The actual Mellin--heat representation of L2 Green pairings

This representation is proved at the level of integrable test pairings.
It does not require a pointwise Mellin representation of the singular Green
function. The time integrand, its integrability, and its integral are all
identified with the actual heat and Green functions.
-/

open MeasureTheory Set Filter

namespace Legacy.TorusEndpoint.GreenMellinPairing

open GreenMellinSeries TorusHeatPositivity TorusHeatBounds TorusHeatPairing

theorem real_mellinSeries_eq_heat_pairing {d : ℕ} {t : ℝ} (ht : 0 < t)
    {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) :
    (∑' k, mellinTerm (fun k => (densityFourier f k).re) k t) =
      t ^ ((d : ℝ) / 2 - 1) *
        ∫ x, ((torusTheta t x).re - 1) * f x ∂torusMeasure d := by
  simp only [mellinTerm, mul_assoc, tsum_mul_left]
  rw [(hasSum_real_heat_pairing ht hf).tsum_eq]

theorem mellin_heat_pairing_integrable {d : ℕ} (hd : 0 < d)
    {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1) *
      ∫ x, ((torusTheta t x).re - 1) * f x ∂torusMeasure d) (Ioi 0) := by
  have hi := IntegrableSeries.integrable_tsum_of_summable_integral_norm
    (mellinTerm_integrable hd (fun k => (densityFourier f k).re))
    (summable_integral_norm_mellinTerm hd _ (summable_realGreen_pairing_abs hf))
  apply hi.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact real_mellinSeries_eq_heat_pairing ht hf

theorem realGreen_mellin_heat_pairing {d : ℕ} (hd : 0 < d)
    {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) :
    (∫ t in Ioi 0, t ^ ((d : ℝ) / 2 - 1) *
      ∫ x, ((torusTheta t x).re - 1) * f x ∂torusMeasure d) =
      2 * ∫ x, GreenKernelReal.realGreen d x * f x ∂torusMeasure d := by
  rw [← realGreen_mellinSeries hd hf]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (real_mellinSeries_eq_heat_pairing ht hf).symm

end Legacy.TorusEndpoint.GreenMellinPairing
