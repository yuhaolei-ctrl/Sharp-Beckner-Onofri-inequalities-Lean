module

public import BecknerOnofri.V2.Vocab.HomEntropy
public import Mathlib.Probability.IdentDistrib

@[expose] public section

/-! # The homogeneous entropy depends only on the distribution of `f` -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Vocab

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma measurable_entropyIntegrand (m : ℝ) : Measurable (entropyIntegrand m) := by
  unfold entropyIntegrand
  fun_prop

/-- Identically distributed functions have the same homogeneous entropy. -/
theorem homEntropy_identDistrib {μ : Measure α} {ν : Measure β} {f : α → ℝ} {g : β → ℝ}
    (h : IdentDistrib f g μ ν) : homEntropy μ f = homEntropy ν g := by
  have hm : ∫ x, f x ∂μ = ∫ x, g x ∂ν := h.integral_eq
  by_cases h0 : ∫ x, g x ∂ν = 0
  · rw [homEntropy_of_mass_zero (hm ▸ h0), homEntropy_of_mass_zero h0]
  · rw [homEntropy_of_mass_ne_zero (hm ▸ h0), homEntropy_of_mass_ne_zero h0, hm]
    have hu : Measurable (fun v : ℝ => ENNReal.ofReal (entropyIntegrand (∫ y, g y ∂ν) v)) :=
      ENNReal.measurable_ofReal.comp (measurable_entropyIntegrand _)
    exact (h.comp hu).lintegral_eq

end BecknerOnofri.V2.Vocab
