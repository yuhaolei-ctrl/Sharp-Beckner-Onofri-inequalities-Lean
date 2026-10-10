module

public import BecknerOnofri.V2.Reaudit.Compactness.TransitionLimit

@[expose] public section

/-! # Proposition 4.9, first sentence: coexistence at `β_gm(11)`, and U07

`coexistence` below is the first sentence of `prop:section4-first-order-coexistence`: *at `β = β_gm`,
the uniform density and at least one nonuniform smooth strictly positive density `ρ_tr` are global
minimizers of `ℰ_{β_gm}`*, together with the printed formula `ρ_tr = e^{u_0}/∫ e^{u_0}` and the
**strong critical-Sobolev convergence** `u_n → u_0` in `H^{11/2}`
(`eq:section4-strong-critical-Sobolev`) which the printed proof establishes on the way.

The logical order of the manuscript (decisions, X3 and U07) is: non-strict lower bound
(`Eleven.transition_lower`, used only through `Eleven.transition_pos`) -> competitor upper bound
(`Eleven.transition_upper`) -> local uniqueness in `H^{11}` (`Sobolev.local_uniqueness_raw`) ->
coexistence (here) -> **only afterwards** the strict lower bound `3543/200 < β_gm`
(`strict_lower_of_coexistence_manuscript`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace BecknerOnofri.V2.Reaudit.Compactness
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OnsetContinuous
open OptimizerDuality
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment (Admissible functional)

theorem gibbs_smooth {d : ℕ} (u : Space d) (hu : SmoothOnTorus u) :
    SmoothOnTorus (continuousGibbsDensity u).value := by
  change ContDiff ℝ ∞ (fun x : Fin d → ℝ =>
    Real.exp (u (fun i => (x i : UnitAddCircle))) / (∫ y, Real.exp (u y) ∂torusMeasure d))
  exact hu.exp.div_const _

/-- **Proposition 4.9, existence of the nonuniform minimizer, following the printed proof.**

There are couplings `β_n ↓ β_gm` (`β_gm < β_n < β_s`, `P_11(β_n) > 0`), mean-zero dual potentials
`u_n ≠ 0` of minimizers at `β_n`, and a nonzero admissible `U₀` such that along a subsequence
`u_n → U₀` strongly in the critical Sobolev space `H^{11/2}` (and in `L²`); and the density
`ρ_tr = e^{u_0}/∫ e^{u_0}` of the continuous smooth representative `u_0` of `U₀` is a smooth,
strictly positive, nonuniform global minimizer of `ℰ_{β_gm}`, while the uniform density is a global
minimizer too. -/
theorem coexistence_with_convergence :
    ∃ (β : ℕ → ℝ) (u : ℕ → Space 11) (u₀ : Space 11) (ψ : ℕ → ℕ),
      StrictMono ψ ∧
      (∀ n, Eleven.globalTransition < β n ∧ β n < spectralThreshold 11) ∧
      Tendsto β atTop (𝓝 Eleven.globalTransition) ∧
      (∀ n, 0 < pressure 11 (β n)) ∧
      (∀ n, InCriticalSobolev (u n) ∧ MeanZero (u n) ∧ u n ≠ 0 ∧
        ∀ v : Torus 11 → ℝ, InCriticalSobolev v → dualFunctional (β n) v ≤ dualFunctional (β n) (u n)) ∧
      InCriticalSobolev u₀ ∧ MeanZero u₀ ∧ SmoothOnTorus u₀ ∧ u₀ ≠ 0 ∧
      (∀ v : Torus 11 → ℝ, InCriticalSobolev v →
        dualFunctional Eleven.globalTransition v ≤ dualFunctional Eleven.globalTransition u₀) ∧
      -- strong convergence in the critical Sobolev space `H^{11/2}`: `eq:section4-strong-critical-Sobolev`
      Tendsto (fun n => criticalEnergy (toL2 11 (u (ψ n)) - toL2 11 u₀)) atTop (𝓝 0) ∧
      Tendsto (fun n => toL2 11 (u (ψ n))) atTop (𝓝 (toL2 11 u₀)) ∧
      -- coexistence: `eq:section4-transition-density`
      IsGlobalMinimizer Eleven.globalTransition (uniformDensity 11) ∧
      IsGlobalMinimizer Eleven.globalTransition (continuousGibbsDensity u₀) ∧
      SmoothOnTorus (continuousGibbsDensity u₀).value ∧
      (∀ x, 0 < (continuousGibbsDensity u₀).value x) ∧
      ¬ ((continuousGibbsDensity u₀).value =ᵐ[torusMeasure 11] fun _ => 1) := by
  obtain ⟨β, u, U₀, ψ, hψ, hβb, hβl, hpos, hprops, hU₀, hne, hmax, hlim, hstrong⟩ := transition_limit
  obtain ⟨w, hwL, hw, hm, hs, -, hwmax⟩ :=
    continuous_optimizer_of_L2 (by norm_num) Eleven.transition_pos U₀ hU₀ hmax
  have hnonuniform : ¬ ((continuousGibbsDensity w).value =ᵐ[torusMeasure 11] fun _ => 1) := by
    intro he
    have hg0 : normalizedGibbs (0 : Space 11) = fun _ => 1 := by
      funext x
      rw [← normalized_apply, normalized_zero]
      rfl
    have hz : w = 0 := meanZero_gibbs_injective hm (by simp [MeanZero]) (by
      rw [hg0]
      exact he)
    apply hne
    rw [← hwL, hz, map_zero]
  refine ⟨β, u, w, ψ, hψ, hβb, hβl, hpos, fun n => ?_, hw, hm, hs, ?_, hwmax,
    ?_, ?_, Eleven.uniform_at_transition,
    gibbs_minimizer_of_continuous_optimizer (by norm_num) Eleven.transition_pos w hw hm hwmax,
    gibbs_smooth w hs, ?_, hnonuniform⟩
  · obtain ⟨h1, h2, h3, -, h5⟩ := hprops n
    exact ⟨h1, h2, h3, h5⟩
  · intro hw0
    apply hne
    rw [← hwL, hw0, map_zero]
  · rw [hwL]; exact hstrong
  · rw [hwL]; exact hlim
  · intro x
    change 0 < normalizedGibbs w x
    rw [← normalized_apply]
    exact normalized_pos w x

/-- **Proposition 4.9, first sentence** (the exact conclusion of the printed statement): at
`β = β_gm(11)` the uniform density and at least one nonuniform smooth strictly positive density are
global minimizers. -/
theorem coexistence :
    IsGlobalMinimizer Eleven.globalTransition (uniformDensity 11) ∧
    ∃ ρ : ProbabilityDensity 11, IsGlobalMinimizer Eleven.globalTransition ρ ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
      ¬ (ρ.value =ᵐ[torusMeasure 11] (fun _ => 1)) := by
  obtain ⟨-, -, w, -, -, -, -, -, -, -, -, -, -, -, -, -, hun, hmin, hsm, hpos, hnon⟩ :=
    coexistence_with_convergence
  exact ⟨hun, continuousGibbsDensity w, hmin, hsm, hpos, hnon⟩

/-! ## U07: the strict lower bound, only after coexistence -/

/-- The strict lower bound `3543/200 < β_gm(11)` (`d11:thm:interval`), derived from the non-strict
lower bound (`Eleven.transition_lower`), the uniqueness of the uniform minimizer on
`[0, 3543/200]`, and the nonuniform minimizer at `β_gm` supplied by the coexistence argument above;
it is not used before. -/
theorem strict_lower_of_coexistence_manuscript :
    (3543 : ℝ) / 200 < Eleven.globalTransition := by
  by_contra hn
  have hb : Eleven.globalTransition ≤ (3543 : ℝ) / 200 := le_of_not_gt hn
  obtain ⟨ρ, hmin, -, -, hnon⟩ := coexistence.2
  exact hnon ((Eleven.uniform_unique Eleven.globalTransition Eleven.transition_pos.le hb ρ
    hmin.1).mp hmin)

end BecknerOnofri.V2.Reaudit.Compactness
