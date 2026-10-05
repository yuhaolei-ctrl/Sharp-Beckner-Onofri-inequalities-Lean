import BecknerOnofri.CanonicalOptimizerSelection
import BecknerOnofri.ContinuousDensityOptimizer
import BecknerOnofri.SmoothTorusLipschitz

/-! Canonical successive rearrangement of the actual smooth representative
of a finite-entropy minimizer, preserving the variational and Gibbs data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace BecknerOnofri.HighDim.PrescribedSelection
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open CoordinateRearrangementStatement
open Legacy.BecknerOnofri.SubcriticalDensityCompactness

theorem smooth_canonical_selection {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : 0 < β) (hβd : β < 2*(d:ℝ)) (ρ : ProbabilityDensity d)
    (hρ : IsGlobalMinimizer β ρ) (hρs : SmoothOnTorus ρ.value) :
    ∃ η : ProbabilityDensity d, ∃ u : ContinuousGibbs.Space d,
      SuccessiveSteiner ρ.value η.value ∧ IsGlobalMinimizer β η ∧
      IdentDistrib η.value ρ.value (torusMeasure d) (torusMeasure d) ∧
      entropy η=entropy ρ ∧ pressureValue β η=pressureValue β ρ ∧
      η.value=normalizedGibbs u ∧ SmoothOnTorus η.value ∧ (∀ x,0<η.value x) ∧
      InCriticalSobolev u ∧ MeanZero u ∧ SmoothOnTorus u ∧ (∀ s : ℝ,InSobolev s u) ∧
      u=ᵐ[torusMeasure d] Gap.densityPotential β η.value ∧
      CoordinateSteiner η.value ∧ CoordinateSteiner u ∧ IsCountableCosineMixture η ∧
      (¬ ρ.value=ᵐ[torusMeasure d] (fun _ => 1) → ¬ η.value=ᵐ[torusMeasure d] (fun _ => 1)) := by
  obtain ⟨K,hK⟩ := hρs.exists_lipschitz
  let f : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨ρ.value,hK.continuous⟩
  have hr := minimizer_memLp hd hβ ρ hρ
  have hmax : BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ f ∈
      densityMaximizers d (spectralThreshold d/(2*β)) := by
    change BoundedContinuousFunction.toLp 2 (Legacy.TorusEndpoint.torusMeasure d) ℝ f ∈ _
    rw [PrescribedPolarization.bounded_toLp_eq f hr]
    exact ⟨Bridge.density ρ,hr,rfl,minimizer_legacy hd hβ ρ hρ⟩
  haveI : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
  have hnonneg : ∀ x,0≤f x := by
    have he : (fun x => max (ρ.value x) 0)=ᵐ[torusMeasure d] ρ.value :=
      ρ.nonneg.mono (fun _ h => max_eq_left h)
    have hh := Measure.eq_of_ae_eq he (hK.continuous.max continuous_const) hK.continuous
    intro x
    exact (le_max_right (ρ.value x) 0).trans_eq (congrFun hh x)
  obtain ⟨g,hchain,_,_,hgmax,hDist,hSt⟩ := CoordinateRearrangement.canonical_optimizer_selection
    hd (concentration_coefficient_lt hd hβ hβd) f hK hnonneg hmax
  obtain ⟨u,hgu,hu,hm,hus,huS,humax⟩ := continuous_density_optimizer hd hβ g hgmax
  let η := continuousGibbsDensity u
  have hη : IsGlobalMinimizer β η := gibbs_minimizer_of_continuous_optimizer hd hβ u hu hm humax
  have he : (g : Torus d → ℝ)=η.value := hgu
  have hD : IdentDistrib η.value ρ.value (torusMeasure d) (torusMeasure d) := by
    rw [← he]; exact hDist
  have hst : CoordinateSteiner (normalizedGibbs u) := by rw [← hgu]; exact hSt
  have hstu : CoordinateSteiner u := by
    exact Legacy.BecknerOnofri.SteinerSelection.steiner_of_normalized_exp
      (ContinuousGibbs.partition_pos u) (by
        change Legacy.BecknerOnofri.SteinerSelection.Steiner
          (fun x => Real.exp (u x)/(∫ y,Real.exp (u y) ∂torusMeasure d)) at hst
        simpa only [ContinuousGibbs.partition,mean_apply,exponential_apply] using hst)
  refine ⟨η,u,?_,hη,hD,(hD.comp Real.continuous_mul_log.measurable).integral_eq,
    (minimizer_value_eq_pressure hη).trans (minimizer_value_eq_pressure hρ).symm,
    rfl,normalizedGibbs_smooth u hus,?_,hu,hm,hus,huS,
    continuous_optimizer_green hd hβ u hu hm humax,hst,hstu,
    continuous_steiner_optimizer_mixture hd hβ u hu hm humax hst hstu,?_⟩
  · rw [← he]; exact hchain
  · intro x
    change 0<normalizedGibbs u x
    rw [← normalized_apply]
    exact normalized_pos u x
  · intro hn hh
    exact hn (hD.ae_snd (measurableSet_singleton 1) hh)

#print axioms smooth_canonical_selection
end BecknerOnofri.HighDim.PrescribedSelection
