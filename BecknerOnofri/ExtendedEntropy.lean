module

public import BecknerOnofri.ExtendedEntropyDefinitions
public import BecknerOnofri.HeatEntropyConvergence
public import BecknerOnofri.LowDimensionRaw

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim

lemma extendedEntropy_eq {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    extendedEntropy ρ = (entropy ρ: EReal) := by
  have hn := entropy_nonneg ρ hρ
  unfold extendedEntropy
  rw [HeatApproximation.shifted_entropy_integral ρ hρ]
  change (ENNReal.ofReal (entropy ρ+1):EReal)-1 = _
  rw [EReal.coe_ennreal_ofReal, max_eq_left (by exact_mod_cast (by linarith : 0 ≤ entropy ρ+1))]
  norm_cast <;> ring

lemma extendedEntropy_top {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ¬ ρ.FiniteEntropy) :
    extendedEntropy ρ = ⊤ := by
  let g := fun x => ρ.value x*Real.log (ρ.value x)+1
  have hgm : AEStronglyMeasurable g (torusMeasure d) :=
    (Real.continuous_mul_log.comp_aestronglyMeasurable ρ.integrable.aestronglyMeasurable).add_const 1
  have hg : ¬ Integrable g (torusMeasure d) := by
    intro hi
    apply hρ
    exact (hi.sub (integrable_const (1:ℝ))).congr (ae_of_all _ (fun x => by simp [g]))
  have htop : (∫⁻ x, ENNReal.ofReal (g x) ∂torusMeasure d) = ⊤ := by
    by_contra hn
    exact hg ((lintegral_ofReal_ne_top_iff_integrable hgm
      (HeatApproximation.shifted_entropy_nonneg ρ)).mp hn)
  unfold extendedEntropy
  change (∫⁻ x, ENNReal.ofReal (g x) ∂torusMeasure d).toEReal-1 = ⊤
  rw [htop]
  simpa using EReal.top_sub_coe (1:ℝ)

/-- The extended-entropy form includes every probability density. -/
theorem low_density_extended {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) (ρ : ProbabilityDensity d) :
    (((d:ℝ)/spectralThreshold d:ℝ):EReal)*(spectralEnergy ρ).toEReal ≤ extendedEntropy ρ := by
  by_cases hρ : ρ.FiniteEntropy
  · rw [extendedEntropy_eq ρ hρ]
    exact LowDimension.density_bound hd hd10 ρ hρ
  · rw [extendedEntropy_top ρ hρ]
    exact le_top

#print axioms extendedEntropy_eq
#print axioms extendedEntropy_top
#print axioms low_density_extended
end BecknerOnofri.HighDim
