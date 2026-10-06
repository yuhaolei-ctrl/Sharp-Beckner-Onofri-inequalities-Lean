module

public import BecknerOnofri.GeneralShapeFourierEntropy
public import BecknerOnofri.SelectedChannelEntropyEta

@[expose] public section

/-!
# Proposition 5.12(i) for every admissible shape density

The general-density form of `SelectedChannelEntropyEta`: for a density satisfying the shape
hypotheses of Proposition 5.10 (packaged as `ShapeEntropy.Data`), the conditional entropy
estimates with the Jensen remainder of Lemma 5.18 give eq:section5-global-channel-entropy.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped BigOperators

namespace BecknerOnofri.HighDim.ShapeEntropy
open ConditionalEntropy

theorem channel_entropy_eta_finite {ρ : ProbabilityDensity 12} (D : Data ρ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, Spin.psi t ≤ CircleScalar.gamma t) (s : Finset ℕ) :
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference +
      12 * Spin.psi (Spin.mean (Spin.countLaw (Spin.channelLaw ρ))) +
      Spin.eta (Spin.mean (Spin.countLaw (Spin.channelLaw ρ))) *
        (Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference -
          12 * Spin.binaryCost (Spin.mean (Spin.countLaw (Spin.channelLaw ρ)))) +
      (21/1000) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2) +
      (67/100) * (∑ i : Fin 12, ∑ n ∈ s,
        (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤
      entropy ρ := by
  set t := Spin.mean (Spin.countLaw (Spin.channelLaw ρ))
  have hi (i : Fin 12) := integrate_conditional_budget_eta (positive_density D)
    ρ.mass i s (conditional_mean_range D i)
    (fun x => conditional_gamma_finite D Spin.psi hminor i x s)
  simp only [density_axis_mean D] at hi
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, Finset.sum_sub_distrib] at h
  rw [← entropy_chain_rule_full (positive_density D) ρ.mass] at h
  have hspin := spin_entropy D
  have heta : 0 ≤ Spin.eta t := Spin.eta_nonneg (spin_mean_range D).1 (spin_mean_range D).2
  have hmul := mul_le_mul_of_nonneg_left hspin heta
  unfold entropy
  nlinarith

/-- **Proposition 5.12(i)** (eq:section5-global-channel-entropy) for an admissible density. -/
theorem channel_fourier_entropy_eta {ρ : ProbabilityDensity 12} (D : Data ρ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, Spin.psi t ≤ CircleScalar.gamma t) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      ‖HighDim.fourierCoeff ρ.value (Pi.single i (n+3 : ℤ))‖^2 / (n+3 : ℝ))) ∧
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference +
      12 * Spin.psi (Spin.mean (Spin.countLaw (Spin.channelLaw ρ))) +
      Spin.eta (Spin.mean (Spin.countLaw (Spin.channelLaw ρ))) *
        (Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference -
          12 * Spin.binaryCost (Spin.mean (Spin.countLaw (Spin.channelLaw ρ)))) +
      (21/1000) * (∑ i : Fin 12, ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖^2) +
      (67/100) * (∑ i : Fin 12, ∑' n : ℕ,
        ‖HighDim.fourierCoeff ρ.value (Pi.single i (n+3 : ℤ))‖^2 / (n+3 : ℝ)) ≤
      HighDim.entropy ρ := by
  set t := Spin.mean (Spin.countLaw (Spin.channelLaw ρ))
  let a := fun (i : Fin 12) (n : ℕ) =>
    (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)
  let A := 2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference +
    12 * Spin.psi t + Spin.eta t *
      (Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference -
        12 * Spin.binaryCost t) +
    (21/1000) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2)
  have ha (i : Fin 12) (n : ℕ) : 0 ≤ a i n := by dsimp [a]; positivity
  have hf (s : Finset ℕ) : A + (67/100) * (∑ n ∈ s, ∑ i : Fin 12, a i n) ≤ entropy ρ := by
    rw [Finset.sum_comm]
    exact channel_entropy_eta_finite D hminor s
  obtain ⟨hs, hb⟩ := nonnegative_budget_limit (fun n => ∑ i : Fin 12, a i n)
    (fun n => Finset.sum_nonneg (fun i _ => ha i n)) A (entropy ρ) (67/100) (by norm_num) hf
  have hi (i : Fin 12) : Summable (a i) :=
    hs.of_nonneg_of_le (ha i) (fun n => Finset.single_le_sum (fun j _ => ha j n)
      (Finset.mem_univ i))
  rw [Summable.tsum_finsetSum (fun i _ => hi i)] at hb
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [a, density_axis_norm_sq D] using hi i
  · simpa only [a, density_axis_norm_sq D] using hb

end BecknerOnofri.HighDim.ShapeEntropy
