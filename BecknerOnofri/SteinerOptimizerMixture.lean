import BecknerOnofri.PrescribedSelectionDefinitions
import BecknerOnofri.OptimizerEulerPaper
import BecknerOnofri.GenericCosineRepresentation
import BecknerOnofri.MixtureEnergyStatementBridge

/-! Transfer the proved Hilbert-space cosine representation to a specified
actual continuous Steiner optimizer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.PrescribedSelection
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SubcriticalEuler Legacy.BecknerOnofri.WienerFourier
open Legacy.BecknerOnofri.SmoothFourier

theorem continuous_steiner_optimizer_mixture {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : ContinuousGibbs.Space d) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u)
    (hStR : CoordinateSteiner (normalizedGibbs u)) (hStU : CoordinateSteiner u) :
    IsCountableCosineMixture (continuousGibbsDensity u) := by
  have hσ := spectralThreshold_pos hd
  have hA : 0 < spectralThreshold d/(2*β) := by positivity
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d := div_pos (Nat.cast_pos.mpr hd) hσ
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d/2)
    (by linarith : Legacy.BecknerOnofri.endpointConstant d/2 < Legacy.BecknerOnofri.endpointConstant d)
  have hU := OnsetContinuous.toL2_admissible hd u hu hm
  have hUmax := toL2_optimizer hd β u hu hm hmax
  have hs := maximizer_fourier_summable hd hR hA hU hUmax
  haveI : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
  haveI : (Legacy.TorusEndpoint.torusMeasure d).IsOpenPosMeasure := by
    rw [Legacy.TorusEndpoint.torusMeasure_explicit]
    infer_instance
  have he : representative (toL2 d u) = fun x => (u x : ℂ) :=
    Measure.eq_of_ae_eq ((representative_ae_eq (toL2 d u) hs).trans (toL2_ae u))
      (representative_continuous (toL2 d u) hs) (Complex.continuous_ofReal.comp u.continuous)
  have hg : smoothGibbsValue (toL2 d u) = normalizedGibbs u := by
    funext x
    simp only [smoothGibbsValue,he,Complex.ofReal_re,partition_toL2,
      normalizedGibbs,ContinuousGibbs.partition,mean_apply,exponential_apply]
  have hStR' : Legacy.BecknerOnofri.SteinerSelection.Steiner (smoothGibbsValue (toL2 d u)) := by
    rw [hg]; exact hStR
  have hStU' : Legacy.BecknerOnofri.SteinerSelection.Steiner
      (fun x => (representative (toL2 d u) x).re) := by
    rw [he]; exact hStU
  obtain ⟨w,N,hw,hsw,_,hEq⟩ := GenericCosineRepresentation.steiner_maximizer_mixture
    hd hA hU hUmax hStR' hStU'
  rw [hg] at hEq
  exact ⟨w,N,hw,hsw,Filter.Eventually.of_forall (congrFun hEq)⟩

#print axioms continuous_steiner_optimizer_mixture
end BecknerOnofri.HighDim.PrescribedSelection
