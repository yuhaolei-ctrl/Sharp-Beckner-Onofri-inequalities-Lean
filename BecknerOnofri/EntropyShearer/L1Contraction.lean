import BecknerOnofri.EntropyShearer.L1Marginal
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.EntropyShearer

lemma fullAvg_l1_contraction {d : ℕ} (s : Finset (Fin d)) {f g : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d)) :
    (∫ x, ‖fullAvg s f x - fullAvg s g x‖ ∂torusMeasure d) ≤
      ∫ x, ‖f x-g x‖ ∂torusMeasure d := by
  have hpoint : (fun x => ‖fullAvg s f x-fullAvg s g x‖) ≤ᵐ[torusMeasure d]
      fullAvg s (fun x => ‖f x-g x‖) := by
    filter_upwards [(mix_integrable s hf).prod_right_ae, (mix_integrable s hg).prod_right_ae] with x hfx hgx
    unfold fullAvg
    rw [← integral_sub hfx hgx]
    exact norm_integral_le_integral_norm _
  calc
    _ ≤ ∫ x, fullAvg s (fun x => ‖f x-g x‖) x ∂torusMeasure d :=
      integral_mono_ae ((fullAvg_integrable s hf).sub (fullAvg_integrable s hg)).norm
        (fullAvg_integrable s (hf.sub hg).norm) hpoint
    _ = _ := integral_fullAvg s (hf.sub hg).norm

def fullMarginalDensity {d : ℕ} (s : Finset (Fin d)) (ρ : ProbabilityDensity d) : ProbabilityDensity d where
  value := fullAvg s ρ.value
  nonneg := fullAvg_nonneg s ρ.nonneg
  integrable := fullAvg_integrable s ρ.integrable
  mass := (integral_fullAvg s ρ.integrable).trans ρ.mass

lemma fullAvg_tendstoInMeasure {d : ℕ} (s : Finset (Fin d))
    (ρ : ProbabilityDensity d) (r : ℕ → ProbabilityDensity d)
    (hlim : Tendsto (fun n => ∫ x, ‖(r n).value x-ρ.value x‖ ∂torusMeasure d) atTop (𝓝 0)) :
    TendstoInMeasure (torusMeasure d) (fun n => (fullMarginalDensity s (r n)).value) atTop
      (fullMarginalDensity s ρ).value := by
  have hl : Tendsto (fun n => ∫ x,
      ‖fullAvg s (r n).value x-fullAvg s ρ.value x‖ ∂torusMeasure d) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => fullAvg_l1_contraction s (r n).integrable ρ.integrable) hlim
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
    (fun n => (fullMarginalDensity s (r n)).integrable.aestronglyMeasurable)
    (fullMarginalDensity s ρ).integrable.aestronglyMeasurable
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl
  have he (n : ℕ) :
      ENNReal.ofReal (∫ x, ‖fullAvg s (r n).value x-fullAvg s ρ.value x‖ ∂torusMeasure d) =
      eLpNorm ((fullMarginalDensity s (r n)).value-(fullMarginalDensity s ρ).value) 1 (torusMeasure d) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact ofReal_integral_norm_eq_lintegral_enorm
      ((fullMarginalDensity s (r n)).integrable.sub (fullMarginalDensity s ρ).integrable)
  simpa only [Function.comp_def, he, ENNReal.ofReal_zero] using! h

#print axioms fullAvg_l1_contraction
#print axioms fullAvg_tendstoInMeasure
end BecknerOnofri.HighDim.EntropyShearer
