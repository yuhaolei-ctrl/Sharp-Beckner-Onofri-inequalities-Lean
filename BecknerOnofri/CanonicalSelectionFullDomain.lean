import BecknerOnofri.CanonicalSelectionDefinitions
import BecknerOnofri.CanonicalSelectionPaper
import BecknerOnofri.CanonicalRearrangementClasses
import BecknerOnofri.CanonicalSelectionFourier

/-! Remove the smooth-representative restriction using actual optimizer
regularity, Fubini, and invariance of the literal layer-cake rearrangement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace BecknerOnofri.HighDim.PrescribedSelection
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open CoordinateRearrangementStatement

theorem canonical_selection {d : ℕ} (hd : 0 < d) : CanonicalSelection d := by
  intro β hβ hβd ρ hρ
  obtain ⟨v,hv,hm,hvs,_,hvmax,he⟩ := continuous_optimizer_of_minimizer hd hβ ρ hρ
  let ρ₀ := continuousGibbsDensity v
  have he₀ : ρ.value =ᵐ[torusMeasure d] ρ₀.value := he
  have hρ₀ : IsGlobalMinimizer β ρ₀ := (minimizer_congr_ae he₀ β).mp hρ
  obtain ⟨η,u,hchain,hη,hD,hE,hP,heη,hηs,hηpos,hu,hm,hus,huS,hG,hst,hstu,hM,hn⟩ :=
    smooth_canonical_selection hd hβ hβd ρ₀ hρ₀ (normalizedGibbs_smooth v hvs)
  have hD₀ : IdentDistrib η.value ρ.value (torusMeasure d) (torusMeasure d) :=
    hD.trans (IdentDistrib.of_ae_eq ρ₀.integrable.aemeasurable he₀.symm)
  refine ⟨η,u,hchain.toAE.congr_left he₀,hη,hD₀,
    (hD₀.comp Real.continuous_mul_log.measurable).integral_eq,
    (minimizer_value_eq_pressure hη).trans (minimizer_value_eq_pressure hρ).symm,
    heη,hηs,hηpos,hus,hu,huS,hm,hG,hst,hstu,hM,
    minimizer_green_fourier_nonnegative hd hβ η hη hM u hm hG,?_⟩
  intro hnon hh
  exact hnon (hD₀.ae_snd (measurableSet_singleton 1) hh)

#print axioms canonical_selection
end BecknerOnofri.HighDim.PrescribedSelection
