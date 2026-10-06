module

public import BecknerOnofri.OptimizerPrescribedPotential
public import BecknerOnofri.ContinuousOptimizerFromL2

@[expose] public section

/-! Section 2 extremizer correspondence for the prescribed physical Green
potential, on the full critical-Sobolev and finite-entropy domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
namespace BecknerOnofri.HighDim.OptimizerDuality
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers
open Legacy.BecknerOnofri TorusSobolev SubcriticalAttainment SubcriticalEuler
open RawAttainment

lemma dualFunctional_congr_ae {d : ℕ} (β : ℝ) {u v : Torus d → ℝ}
    (he : u =ᵐ[torusMeasure d] v) : dualFunctional β u = dualFunctional β v := by
  have hi := integral_congr_ae he
  have hc : centered u =ᵐ[torusMeasure d] centered v := by
    filter_upwards [he] with x hx
    simp only [centered, hi, hx]
  have hl : logPartition u = logPartition v := by
    unfold logPartition
    congr 1
    exact lintegral_congr_ae (hc.fun_comp (fun t => ENNReal.ofReal (Real.exp t)))
  simp only [dualFunctional, normalizedPotentialEnergy, hl, Gap.potentialEnergy_congr he]

/-- Regularity of each specified raw mean-zero optimizer, preserving its a.e. class. -/
theorem continuous_optimizer_of_raw {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :
    ∃ v : Space d, u =ᵐ[torusMeasure d] v ∧ InCriticalSobolev v ∧ MeanZero v ∧
      SmoothOnTorus v ∧ (∀ s : ℝ, InSobolev s v) ∧
      (∀ w : Torus d → ℝ, InCriticalSobolev w → dualFunctional β w ≤ dualFunctional β v) := by
  let U := SobolevCentering.center (Bridge.potentialLp u hu.1)
  have hU : Admissible U := SobolevCentering.center_admissible hd
    (Bridge.potentialLp_real u hu.1) (Bridge.potentialLp_summable hd u hu)
  have hmaxU (V : TorusL2 d) (hV : Admissible V) :
      functional (spectralThreshold d/(2*β)) V ≤ functional (spectralThreshold d/(2*β)) U := by
    have hh := hmax (realValue V) (realValue_sobolev V hV)
    rw [OnsetRaw.dualFunctional_eq_normalized hd _ _ (realValue_sobolev V hV),
      OnsetRaw.dualFunctional_eq_normalized hd _ _ hu, center_potentialLp_realValue V hV] at hh
    exact_mod_cast hh
  obtain ⟨v,hvU,hv,hvm,hvs,hvS,hvmax⟩ := continuous_optimizer_of_L2 hd hβ U hU hmaxU
  have hUu : realValue U =ᵐ[torusMeasure d] u := by
    have hh := Bridge.centeredLp_ae u hu.1
    change realValue U =ᵐ[torusMeasure d] HighDim.centered u at hh
    have hc : HighDim.centered u = u := by
      funext x
      simp only [HighDim.centered, show (∫ x,u x ∂torusMeasure d)=0 from hm, sub_zero]
    rw [hc] at hh
    exact hh
  have hUv : realValue U =ᵐ[torusMeasure d] v := by
    rw [← hvU]
    filter_upwards [toL2_ae v] with x hx
    exact congrArg Complex.re hx
  exact ⟨v,hUu.symm.trans hUv,hv,hvm,hvs,hvS,hvmax⟩

theorem continuous_optimizer_green {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Space d) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :
    (u : Torus d → ℝ) =ᵐ[torusMeasure d] Gap.densityPotential β (normalizedGibbs u) := by
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (spectralThreshold_pos hd)
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < endpointConstant d/2)
    (by linarith : endpointConstant d/2 < endpointConstant d)
  have he := FiniteEntropyGreen.optimizer_physical_green hd hR hβ (toL2 d u)
    (OnsetContinuous.toL2_admissible hd u hu hm) (toL2_optimizer hd β u hu hm hmax)
  rw [Gap.densityPotential_congr β (gibbsValue_toL2_ae u)] at he
  have hr : realValue (toL2 d u) =ᵐ[torusMeasure d] u := by
    filter_upwards [toL2_ae u] with x hx
    exact congrArg Complex.re hx
  exact hr.symm.trans he

/-- The potential in the density-side iff is the prescribed convolution, not
an existentially selected potential. -/
theorem minimizer_iff_prescribed_optimizer {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    IsGlobalMinimizer β ρ ↔
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional β v ≤ dualFunctional β (Gap.densityPotential β ρ.value)) ∧
      ρ.value =ᵐ[torusMeasure d] normalizedGibbs (Gap.densityPotential β ρ.value) := by
  constructor
  · intro hmin
    obtain ⟨u,hu,hm,_,_,hmax,hg⟩ := continuous_optimizer_of_minimizer hd hβ ρ hmin
    have he := continuous_optimizer_green hd hβ u hu hm hmax
    rw [← Gap.densityPotential_congr β hg] at he
    exact ⟨fun v hv => (hmax v hv).trans_eq (dualFunctional_congr_ae β he),
      hg.trans (Gap.gibbs_congr he)⟩
  · rintro ⟨hmax,hg⟩
    have hr := Gap.densityPotential_regular hd hβ ρ hρ
    obtain ⟨u,he,hu,hm,_,_,humax⟩ := continuous_optimizer_of_raw hd hβ
      (Gap.densityPotential β ρ.value) hr.1 hr.2 hmax
    exact (minimizer_iff_continuous_optimizer hd hβ ρ).mpr
      ⟨u,hu,hm,humax,hg.trans (Gap.gibbs_congr he)⟩

/-- The potential-side iff, with actual Gibbs density and prescribed Green relation. -/
theorem raw_optimizer_iff_gibbs_and_green {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) (hm : MeanZero u) :
    (∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) ↔
      (∃ ρ : ProbabilityDensity d, ρ.value =ᵐ[torusMeasure d] normalizedGibbs u ∧
        IsGlobalMinimizer β ρ) ∧
      u =ᵐ[torusMeasure d] Gap.densityPotential β (normalizedGibbs u) := by
  constructor
  · intro hmax
    obtain ⟨v,he,hv,hvm,_,_,hvmax⟩ := continuous_optimizer_of_raw hd hβ u hu hm hmax
    have hg := Gap.gibbs_congr he
    have hvgreen := continuous_optimizer_green hd hβ v hv hvm hvmax
    rw [← Gap.densityPotential_congr β hg] at hvgreen
    exact ⟨⟨continuousGibbsDensity v,hg.symm,
      gibbs_minimizer_of_continuous_optimizer hd hβ v hv hvm hvmax⟩,he.trans hvgreen⟩
  · rintro ⟨⟨ρ,hg,hmin⟩,he⟩
    have hh := ((minimizer_iff_prescribed_optimizer hd hβ ρ hmin.1).mp hmin).1
    rw [Gap.densityPotential_congr β hg] at hh
    intro v hv
    exact (hh v hv).trans_eq (dualFunctional_congr_ae β he).symm

#print axioms continuous_optimizer_of_raw
#print axioms continuous_optimizer_green
#print axioms minimizer_iff_prescribed_optimizer
#print axioms raw_optimizer_iff_gibbs_and_green
end BecknerOnofri.HighDim.OptimizerDuality
