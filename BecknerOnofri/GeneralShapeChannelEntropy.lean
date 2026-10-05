import BecknerOnofri.GeneralShapeEntropyData

/-! The full integrated channel entropy estimate for a general smooth
shape density; no stationarity is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.ShapeEntropy
open ConditionalEntropy

theorem channel_entropy_finite {ρ : ProbabilityDensity 12} (D : Data ρ)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) (s : Finset ℕ) :
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference +
      (∑ i : Fin 12, ψ (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
      (21/1000) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2) +
      (27/40) * (∑ i : Fin 12, ∑ n ∈ s,
        (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤
      entropy ρ := by
  have hi (i : Fin 12) := integrate_conditional_budget (positive_density D)
    ρ.mass ψ hc hcv i s
    (fun x => ⟨(conditional_mean_range D i x).1,
      (conditional_mean_range D i x).2.le⟩)
    (fun x => conditional_gamma_finite D ψ hminor i x s)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [← entropy_chain_rule_full (positive_density D) ρ.mass] at h
  have hspin := spin_entropy D
  unfold entropy
  linarith


theorem channel_entropy {ρ : ProbabilityDensity 12} (D : Data ρ)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ))) ∧
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference +
      (∑ i : Fin 12, ψ (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
      (21/1000) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2) +
      (27/40) * (∑ i : Fin 12, ∑' n : ℕ,
        (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤
      entropy ρ := by
  let a := fun (i : Fin 12) (n : ℕ) =>
    (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)
  let A := 2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference +
    (∑ i : Fin 12, ψ (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
    (21/1000) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2)
  have ha (i : Fin 12) (n : ℕ) : 0 ≤ a i n := by dsimp [a]; positivity
  have hf (s : Finset ℕ) : A + (27/40) * (∑ n ∈ s, ∑ i : Fin 12, a i n) ≤ entropy ρ := by
    rw [Finset.sum_comm]
    exact channel_entropy_finite D ψ hc hcv hminor s
  obtain ⟨hs,hb⟩ := nonnegative_budget_limit (fun n => ∑ i : Fin 12, a i n)
    (fun n => Finset.sum_nonneg (fun i _ => ha i n)) A (entropy ρ) (27/40) (by norm_num) hf
  have hi (i : Fin 12) : Summable (a i) :=
    hs.of_nonneg_of_le (ha i) (fun n => Finset.single_le_sum (fun j _ => ha j n) (Finset.mem_univ i))
  refine ⟨hi, ?_⟩
  rw [Summable.tsum_finsetSum (fun i _ => hi i)] at hb
  exact hb


#print axioms channel_entropy
end BecknerOnofri.HighDim.ShapeEntropy
