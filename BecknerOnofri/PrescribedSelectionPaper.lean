module

public import BecknerOnofri.PrescribedSelectionDefinitions
public import BecknerOnofri.PrescribedSteinerSelection
public import BecknerOnofri.OptimizerEulerPaper
public import BecknerOnofri.SteinerOptimizerMixture

@[expose] public section

/-! Full finite-entropy-domain equimeasurable selection, via the closure of
finite polarizations of the given minimizer. Canonical successive-coordinate
identification remains a separate statement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
namespace BecknerOnofri.HighDim.PrescribedSelection
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SubcriticalEuler Legacy.BecknerOnofri.SubcriticalPrimalDual
open Legacy.BecknerOnofri.CoordinatePolarization

/-- Regularity of a specified minimizer supplies the needed L2 domain; it is
not an additional assumption on the raw finite-entropy input. -/
lemma minimizer_memLp {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) :
    MemLp ρ.value 2 (torusMeasure d) := by
  obtain ⟨u,_,_,_,_,_,he⟩ := continuous_optimizer_of_minimizer hd hβ ρ hρ
  have hn : MemLp (normalized u : Torus d → ℝ) 2 (torusMeasure d) :=
    (normalized u).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he' : (normalized u : Torus d → ℝ) =ᵐ[torusMeasure d] ρ.value := by
    filter_upwards [he] with x hx
    exact (normalized_apply u x).trans hx.symm
  exact hn.ae_eq he'

lemma minimizer_legacy {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) :
    ∀ s : Legacy.TorusEndpoint.ProbabilityDensity d, MemLp s.value 2 (torusMeasure d) →
      densityFunctional (spectralThreshold d/(2*β)) s ≤
        densityFunctional (spectralThreshold d/(2*β)) (Bridge.density ρ) := by
  intro s hs
  have hsf := Legacy.TorusEndpoint.PhysicalGreenL2.finiteEntropy_of_memLp s hs
  have hh := hρ.2 (Bridge.rawDensity s) hsf
  rw [pressureValue_eq_legacy hd hβ (Bridge.rawDensity s) hsf,pressureValue_eq_legacy hd hβ ρ hρ.1] at hh
  exact_mod_cast hh

theorem equimeasurable_selection {d : ℕ} (hd : 0 < d) : EquimeasurableSelection d := by
  intro β hβ hβd ρ hρ
  have hr := minimizer_memLp hd hβ ρ hρ
  have hA := concentration_coefficient_lt hd hβ hβd
  obtain ⟨q,hq,_,hD,hqm,hfixed⟩ :=
    BecknerOnofri.PrescribedPolarization.exists_fixed_prescribed_maximizer hd hA
      (Bridge.density ρ) hr (minimizer_legacy hd hβ ρ hρ)
  have hσ := spectralThreshold_pos hd
  have hA0 : 0 < spectralThreshold d/(2*β) := by positivity
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d := div_pos (Nat.cast_pos.mpr hd) hσ
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d/2)
    (by linarith : Legacy.BecknerOnofri.endpointConstant d/2 < Legacy.BecknerOnofri.endpointConstant d)
  let U := dualPotential (spectralThreshold d/(2*β)) q hq
  have hU : Admissible U := dualPotential_admissible hd _ q hq
  have hUmax := (density_maximizer_dual hd hR hA0 q hq hqm).2
  obtain ⟨u,huL,hu,hm,hus,huS,humax⟩ := continuous_optimizer_of_L2 hd hβ U hU hUmax
  have hqu : q.value =ᵐ[torusMeasure d] normalizedGibbs u := by
    have he := density_maximizer_gibbs hd hR hA0 q hq hqm
    change q.value =ᵐ[torusMeasure d] gibbsValue U at he
    rw [← huL] at he
    exact he.trans (gibbsValue_toL2_ae u)
  let η := continuousGibbsDensity u
  have hη : IsGlobalMinimizer β η := gibbs_minimizer_of_continuous_optimizer hd hβ u hu hm humax
  have hn : (normalized u : Torus d → ℝ) = normalizedGibbs u := funext (normalized_apply u)
  have hc : Continuous (normalizedGibbs u) := by rw [← hn]; exact (normalized u).continuous
  have hDist : IdentDistrib η.value ρ.value (torusMeasure d) (torusMeasure d) :=
    (IdentDistrib.of_ae_eq hc.aemeasurable hqu.symm).trans hD
  have hinv : OriginPolarizationInvariant (normalizedGibbs u) := by
    intro i a ha ha0
    exact (polarize_congr_ae i a hqu.symm).trans ((hfixed i a ha ha0).trans hqu)
  have hst := Legacy.BecknerOnofri.SteinerSelection.steiner_of_origin_invariant hc hinv
  have hstu : CoordinateSteiner u := by
    exact Legacy.BecknerOnofri.SteinerSelection.steiner_of_normalized_exp
      (ContinuousGibbs.partition_pos u) (by
        change Legacy.BecknerOnofri.SteinerSelection.Steiner
          (fun x => Real.exp (u x)/(∫ y,Real.exp (u y) ∂torusMeasure d)) at hst
        simpa only [ContinuousGibbs.partition,mean_apply,exponential_apply] using hst)
  refine ⟨η,u,hη,hDist,(hDist.comp Real.continuous_mul_log.measurable).integral_eq,
    (minimizer_value_eq_pressure hη).trans (minimizer_value_eq_pressure hρ).symm,
    rfl,normalizedGibbs_smooth u hus,?_,hus,hu,huS,hm,
    continuous_optimizer_green hd hβ u hu hm humax,hst,hstu,
    continuous_steiner_optimizer_mixture hd hβ u hu hm humax hst hstu,?_⟩
  · intro x
    change 0 < normalizedGibbs u x
    rw [← normalized_apply]
    exact normalized_pos u x
  · intro hn hh
    exact hn (hDist.ae_snd (measurableSet_singleton 1) hh)

#print axioms equimeasurable_selection
end BecknerOnofri.HighDim.PrescribedSelection
