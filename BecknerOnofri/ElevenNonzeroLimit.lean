module

public import BecknerOnofri.ElevenTransitionSequence
public import BecknerOnofri.SubspectralLocalUniqueness

@[expose] public section

/-! The compact limit at the transition cannot be uniform: a zero L2 limit
upgrades to uniform convergence, contradicting local Euler uniqueness and
the strictly positive pressure at every approximating coupling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.Eleven
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OnsetContinuous
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

theorem exists_nonzero_limit_optimizer :
    ∃ U : TorusL2 11, Admissible U ∧ U ≠ 0 ∧
      ∀ V : TorusL2 11, Admissible V →
        functional (spectralThreshold 11/(2*globalTransition)) V ≤
          functional (spectralThreshold 11/(2*globalTransition)) U := by
  choose u hu hm hmax hfull hnz using exists_nonzero_optimizer
  let A : ℕ → ℝ := fun n => spectralThreshold 11/(2*transitionCoupling n)
  let A₀ := spectralThreshold 11/(2*globalTransition)
  have hσ := spectralThreshold_pos (d := 11) (by norm_num)
  have hA : Tendsto A atTop (𝓝 A₀) :=
    tendsto_const_nhds.div (tendsto_const_nhds.mul transitionCoupling_limit)
      (mul_ne_zero (by norm_num) transition_pos.ne')
  have hA₀ : (1/2:ℝ) < A₀ := normalized_coefficient_gt_half transition_pos
    (transition_upper.trans spectralThreshold_bounds.1)
  have hAn (n : ℕ) : (1/4:ℝ) ≤ A n := by
    have h := normalized_coefficient_gt_half (transitionCoupling_pos n) (transitionCoupling_bounds n).2
    dsimp [A]
    linarith
  have hU (n : ℕ) : Admissible (toL2 11 (u n)) := toL2_admissible (by norm_num) _ (hu n) (hm n)
  have hM (n : ℕ) (V : TorusL2 11) (hV : Admissible V) :
      functional (A n) V ≤ functional (A n) (toL2 11 (u n)) :=
    toL2_optimizer (by norm_num) _ _ (hu n) (hm n) (hmax n) V hV
  obtain ⟨b, Ab, hb, hR, hgap⟩ := eleven_rough_gap
  obtain ⟨B,hB,U,hUB,φ,hφ,hlim,hbound,hUM⟩ :=
    SubcriticalOptimizerCompactness.exists_subsequence_limit (by norm_num) hb hR
      (hgap.trans hA₀) hA (fun n => toL2 11 (u n)) hU hM
  refine ⟨U, ⟨hUB.2,hUB.1.1⟩, ?_, hUM⟩
  intro hz
  have hlim0 : Tendsto (fun n => toL2 11 (u (φ n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hz] using hlim
  have hC : Tendsto (fun n => u (φ n)) atTop (𝓝 0) :=
    SubcriticalOptimizerConvergence.continuous_tendsto_zero (by norm_num) hb hR hB
      (fun n => A (φ n)) (fun n => u (φ n)) (fun n => hU (φ n)) (fun n => hM (φ n))
      (Eventually.of_forall (fun n => hAn (φ n))) hbound hlim0
  have hμlim : Tendsto (fun n => transitionCoupling (φ n)/spectralThreshold 11) atTop
      (𝓝 (globalTransition/spectralThreshold 11)) :=
    (transitionCoupling_limit.comp hφ.tendsto_atTop).div_const _
  have hμ0 : 0 ≤ globalTransition/spectralThreshold 11 := div_nonneg transition_pos.le hσ.le
  have hμ1 : globalTransition/spectralThreshold 11 < 1 :=
    (div_lt_one hσ).mpr (transition_upper.trans spectralThreshold_bounds.1)
  have he := (hμlim.prodMk_nhds hC).eventually
    (SubspectralLocalUniqueness.local_unique (by norm_num) hμ0 hμ1)
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [he] with n hn
    exact hnz (φ n) (hn (hfull (φ n)))
  exact hfalse.exists.elim (fun _ h => h)

#print axioms exists_nonzero_limit_optimizer
end BecknerOnofri.HighDim.Eleven
