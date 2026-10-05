import BecknerOnofri.ElevenNonzeroLimit
import BecknerOnofri.ContinuousOptimizerFromL2

/-! Coexistence at the actual transition and the strict lower endpoint of its
certified interval. The nonuniform state is the Gibbs density of the nonzero
compact limit of above-transition optimizers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.HighDim.Eleven
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality

lemma gibbs_smooth {d : ℕ} (u : Space d) (hu : SmoothOnTorus u) :
    SmoothOnTorus (continuousGibbsDensity u).value := by
  change ContDiff ℝ ∞ (fun x : Fin d → ℝ =>
    Real.exp (u (fun i => (x i:UnitAddCircle)))/(∫ y, Real.exp (u y) ∂torusMeasure d))
  exact hu.exp.div_const _

theorem coexistence :
    IsGlobalMinimizer globalTransition (uniformDensity 11) ∧
    ∃ ρ : ProbabilityDensity 11, IsGlobalMinimizer globalTransition ρ ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
      ¬ (ρ.value =ᵐ[torusMeasure 11] (fun _ => 1)) := by
  obtain ⟨U,hU,hUnz,hM⟩ := exists_nonzero_limit_optimizer
  obtain ⟨u,huL,hu,hm,hs,_,hmax⟩ := continuous_optimizer_of_L2 (by norm_num) transition_pos U hU hM
  refine ⟨uniform_at_transition, continuousGibbsDensity u,
    gibbs_minimizer_of_continuous_optimizer (by norm_num) transition_pos u hu hm hmax,
    gibbs_smooth u hs, ?_, ?_⟩
  · intro x
    change 0 < normalizedGibbs u x
    rw [← normalized_apply]
    exact normalized_pos u x
  · intro he
    have hg0 : normalizedGibbs (0 : Space 11) = fun _ => 1 := by
      funext x
      rw [← normalized_apply, normalized_zero]
      rfl
    have hz : u = 0 := meanZero_gibbs_injective hm (by simp [MeanZero]) (by
      rw [hg0]
      exact he)
    apply hUnz
    rw [← huL, hz, map_zero]

theorem transition_strict_lower : (3543:ℝ)/200 < globalTransition := by
  by_contra hn
  have hb : globalTransition ≤ (3543:ℝ)/200 := le_of_not_gt hn
  obtain ⟨ρ,hmin,_,_,hnon⟩ := coexistence.2
  exact hnon ((uniform_unique globalTransition transition_pos.le hb ρ hmin.1).mp hmin)

theorem transition_interval :
    (3543:ℝ)/200 < globalTransition ∧ globalTransition < 2063/100 ∧
    (2063:ℝ)/100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 :=
  ⟨transition_strict_lower, transition_upper, spectralThreshold_bounds⟩

#print axioms coexistence
#print axioms transition_interval
end BecknerOnofri.HighDim.Eleven
