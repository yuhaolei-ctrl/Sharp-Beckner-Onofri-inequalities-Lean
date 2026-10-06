module

public import BecknerOnofri.SelectedChannelEntropy

@[expose] public section

/-! The integrated channel gamma inequality for actual joint cosine profiles.
All conditional estimates and the infinite-sum passage are discharged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer Legacy.TorusEndpoint Legacy.BecknerOnofri.RadialWiener

theorem channel_gamma_entropy (ρ : ProbabilityDensity 12) (V : (Fin 12 → ℝ) → ℝ)
    (hcV : ContinuousOn V (cosineCube 12))
    (hconv : ∀ v ∈ cosineCube 12, ∀ i : Fin 12,
      ConvexOn ℝ (Icc (-1 : ℝ) 1) (fun t => V (Function.update v i t)))
    (hmono : ∀ v ∈ cosineCube 12, ∀ i : Fin 12,
      MonotoneOn (fun t => V (Function.update v i t)) (Icc (-1 : ℝ) 1))
    (hrep : ∀ x, ρ.value x = Real.exp (V (cosineVector x)))
    (a : Frequency 12 → ℂ) (ha : ∀ m : ℕ, RadialSummable a m)
    (he : ∀ x, (ρ.value x : ℂ) = absoluteFourierSeries a x)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ))) ∧
    2 * (∑ σ : Spin.Configuration, Spin.channelLaw ρ σ * Real.log (Spin.channelLaw ρ σ / (1/4096))) +
      (∑ i : Fin 12, ψ (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
      (21/1000) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2) +
      (67/100) * (∑ i : Fin 12, ∑' n : ℕ,
        (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤ entropy ρ := by
  have hcont : Continuous ρ.value := by
    have h := hcV.comp_continuous (cosineVector_continuous 12) (fun y => cosineVector_mem y)
    have heq : ρ.value = fun y => Real.exp (V (cosineVector y)) := funext hrep
    rw [heq]
    exact Real.continuous_exp.comp h
  have hf : PositiveBounded ρ.value := positiveBounded_of_continuous_pos hcont
    (fun x => by rw [hrep]; exact Real.exp_pos _)
  have hstats (i : Fin 12) (x : Torus 12) :
      conditionalCosineMoment ρ.value i 1 x ∈ Ico (0 : ℝ) 1 ∧
      Summable (fun n : ℕ => (conditionalCosineMoment ρ.value i (n+3) x)^2 / (n+3 : ℝ)) := by
    obtain ⟨F,hcF,hF,hmF,hp⟩ := conditional_log_profile V hcV hconv hmono ρ.value hrep i x
    have h := conditional_profile_stats hf i x F hcF hF hmF hp
    exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩
  have hpoint (s : Finset ℕ) (i : Fin 12) (x : Torus 12) :
      2 * Spin.binaryCost (conditionalCosineMoment ρ.value i 1 x) +
      ψ (conditionalCosineMoment ρ.value i 1 x) + (21/1000) * (conditionalCosineMoment ρ.value i 2 x)^2 +
      (67/100) * (∑ n ∈ s, (conditionalCosineMoment ρ.value i (n+3) x)^2 / (n+3 : ℝ)) ≤
      conditionalEntropy ρ.value i x := by
    have hψ := hminor _ (hstats i x).1
    have hs := Summable.sum_le_tsum s (fun n _ => by positivity) (hstats i x).2
    have h := conditional_gamma V hcV hconv hmono ρ.value hrep a ha he i x
    linarith
  let q := fun (i : Fin 12) (n : ℕ) =>
    (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)
  let A := 2 * (∑ σ : Spin.Configuration, Spin.channelLaw ρ σ * Real.log (Spin.channelLaw ρ σ / (1/4096))) +
    (∑ i : Fin 12, ψ (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
    (21/1000) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2)
  have hfinite (s : Finset ℕ) : A + (67/100) * (∑ n ∈ s, ∑ i : Fin 12, q i n) ≤ entropy ρ := by
    rw [Finset.sum_comm]
    have hi (i : Fin 12) := integrate_conditional_budget hf ρ.mass ψ hc hcv i s
      (fun x => ⟨(hstats i x).1.1, (hstats i x).1.2.le⟩) (hpoint s i)
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [← entropy_chain_rule_full hf ρ.mass] at h
    have hspin := Spin.channel_entropy_le_conditional ρ hf
    dsimp only [A,q,entropy]
    linarith
  have hq (i : Fin 12) (n : ℕ) : 0 ≤ q i n := by dsimp [q]; positivity
  obtain ⟨hs,hb⟩ := nonnegative_budget_limit (fun n => ∑ i : Fin 12, q i n)
    (fun n => Finset.sum_nonneg (fun i _ => hq i n)) A (entropy ρ) (67/100) (by norm_num) hfinite
  have hi (i : Fin 12) : Summable (q i) :=
    hs.of_nonneg_of_le (hq i) (fun n => Finset.single_le_sum (fun j _ => hq j n) (Finset.mem_univ i))
  refine ⟨hi, ?_⟩
  rw [Summable.tsum_finsetSum (fun i _ => hi i)] at hb
  exact hb

#print axioms channel_gamma_entropy
end BecknerOnofri.HighDim.ConditionalEntropy
