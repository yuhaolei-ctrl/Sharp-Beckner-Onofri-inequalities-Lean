module

public import BecknerOnofri.PrescribedSelectionPaper
public import BecknerOnofri.UniformPolarizationMaximizers

@[expose] public section

/-! Recover the actual smooth Gibbs potential of a specified continuous
representative in the L2 optimizer set, with pointwise density identification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BoundedContinuousFunction
namespace BecknerOnofri.HighDim.PrescribedSelection
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SubcriticalEuler Legacy.BecknerOnofri.SubcriticalPrimalDual
open Legacy.BecknerOnofri.SubcriticalDensityCompactness

theorem continuous_density_optimizer {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (g : Torus d →ᵇ ℝ)
    (hmax : BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ g ∈
      densityMaximizers d (spectralThreshold d/(2*β))) :
    ∃ u : ContinuousGibbs.Space d, (g : Torus d → ℝ)=normalizedGibbs u ∧
      InCriticalSobolev u ∧ MeanZero u ∧ SmoothOnTorus u ∧ (∀ s : ℝ,InSobolev s u) ∧
      (∀ v : Torus d → ℝ,InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) := by
  obtain ⟨q,hq,he,hqm⟩ := hmax
  have hgq : (g : Torus d → ℝ)=ᵐ[torusMeasure d] q.value := by
    have hgl := BoundedContinuousFunction.coeFn_toLp 2 (torusMeasure d) ℝ g
    rw [he] at hgl
    exact hgl.symm.trans hq.coeFn_toLp
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
    have h := density_maximizer_gibbs hd hR hA0 q hq hqm
    change q.value =ᵐ[torusMeasure d] gibbsValue U at h
    rw [← huL] at h
    exact h.trans (gibbsValue_toL2_ae u)
  have hn : (normalized u : Torus d → ℝ)=normalizedGibbs u := funext (normalized_apply u)
  have hc : Continuous (normalizedGibbs u) := by rw [← hn]; exact (normalized u).continuous
  haveI : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
  exact ⟨u,Measure.eq_of_ae_eq (hgq.trans hqu) g.continuous hc,hu,hm,hus,huS,humax⟩

#print axioms continuous_density_optimizer
end BecknerOnofri.HighDim.PrescribedSelection
