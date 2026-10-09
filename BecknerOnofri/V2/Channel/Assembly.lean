module

public import BecknerOnofri.V2.Channel.Budget

@[expose] public section

/-!
# Assembly of the channel entropy inequality (work package G10, part (d))

`channel_entropy_core` is the inequality `eq:section5-global-channel-entropy` in terms of the
real cosine integrals `∫ρ cos(2π n x_i) = Re ρ̂(n e_i)` (the identification with `|ρ̂(n e_i)|²` and
the common mean `t` is done in `Prop512`).

Hypotheses of this core statement: the closed-cube smoothness `V ∈ C^∞([-1,1]^{12})` with
`∂_iV ≥ 0`, the representation `ρ = e^{V(cos 2πx)}`, and smoothness of `ρ` on the torus.  Neither
`∂_i² V ≥ 0`, nor the cosine-mixture representation, nor the permutation invariance is used here
(permutation invariance enters only through the identification of the coefficients).
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped BigOperators ContDiff
namespace BecknerOnofri.V2.Channel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.HighDim.EntropyShearer
open BecknerOnofri.HighDim.Spin (binaryCost channelLaw)

/-- `eq:section5-channel-continuous-entropy` combined with `eq:section5-channel-discrete-entropy`,
before identification of the Fourier coefficients. -/
theorem channel_entropy_core (ρ : ProbabilityDensity 12) {V : (Fin 12 → ℝ) → ℝ}
    (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v)
    (hrep : ∀ x, ρ.value x = Real.exp (V (cosineVector x))) (hs : SmoothOnTorus ρ.value) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      (∫ x, ρ.value x * (fourier ((n + 4 : ℕ) : ℤ) (x i)).re ∂torusMeasure 12) ^ 2 /
        ((n : ℝ) + 4))) ∧
    2 * (∑ σ : Spin.Configuration, channelLaw ρ σ * Real.log (channelLaw ρ σ / (1 / 4096))) +
      (∑ i : Fin 12, BecknerOnofri.V2.Circle.psi
        (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
      (1 / 40) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12) ^ 2) +
      (2 / 15) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 3 (x i)).re ∂torusMeasure 12) ^ 2) +
      (27 / 40) * (∑ i : Fin 12, ∑' n : ℕ,
        (∫ x, ρ.value x * (fourier ((n + 4 : ℕ) : ℤ) (x i)).re ∂torusMeasure 12) ^ 2 /
          ((n : ℝ) + 4)) ≤ entropy ρ := by
  have hf : PositiveBounded ρ.value := rep_positiveBounded hV.continuousOn hrep
  have hstats (i : Fin 12) (x : Torus 12) := conditional_explicit hV h1 hrep hs i x
  have hpoint (s : Finset ℕ) (i : Fin 12) (x : Torus 12) :
      2 * binaryCost (conditionalCosineMoment ρ.value i 1 x) +
      BecknerOnofri.V2.Circle.psi (conditionalCosineMoment ρ.value i 1 x) +
      (1 / 40) * (conditionalCosineMoment ρ.value i 2 x) ^ 2 +
      (2 / 15) * (conditionalCosineMoment ρ.value i 3 x) ^ 2 +
      (27 / 40) * (∑ n ∈ s, (conditionalCosineMoment ρ.value i (n + 4) x) ^ 2 / ((n : ℝ) + 4)) ≤
        conditionalEntropy ρ.value i x := by
    obtain ⟨_, _, hsm, hmain⟩ := hstats i x
    have hsum := Summable.sum_le_tsum s (fun n _ => by positivity) hsm
    linarith
  let q := fun (i : Fin 12) (n : ℕ) =>
    (∫ x, ρ.value x * (fourier ((n + 4 : ℕ) : ℤ) (x i)).re ∂torusMeasure 12) ^ 2 / ((n : ℝ) + 4)
  let A := 2 * (∑ σ : Spin.Configuration, channelLaw ρ σ * Real.log (channelLaw ρ σ / (1 / 4096))) +
    (∑ i : Fin 12, BecknerOnofri.V2.Circle.psi
      (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
    (1 / 40) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12) ^ 2) +
    (2 / 15) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 3 (x i)).re ∂torusMeasure 12) ^ 2)
  have hfinite (s : Finset ℕ) : A + (27 / 40) * (∑ n ∈ s, ∑ i : Fin 12, q i n) ≤ entropy ρ := by
    rw [Finset.sum_comm]
    have hi (i : Fin 12) := integrate_budget hf ρ.mass i s
      (fun x => ⟨(hstats i x).1, (hstats i x).2.1.le⟩) (hpoint s i)
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [← entropy_chain_rule_full hf ρ.mass] at h
    have hspin := Spin.channel_entropy_le_conditional ρ hf
    dsimp only [A, q, entropy]
    linarith
  have hq (i : Fin 12) (n : ℕ) : 0 ≤ q i n := by dsimp [q]; positivity
  obtain ⟨hs', hb⟩ := nonneg_budget_limit (fun n => ∑ i : Fin 12, q i n)
    (fun n => Finset.sum_nonneg (fun i _ => hq i n)) A (entropy ρ) (27 / 40) (by norm_num) hfinite
  have hi (i : Fin 12) : Summable (q i) :=
    hs'.of_nonneg_of_le (hq i) (fun n => Finset.single_le_sum (fun j _ => hq j n) (Finset.mem_univ i))
  refine ⟨hi, ?_⟩
  rw [Summable.tsum_finsetSum (fun i _ => hi i)] at hb
  exact hb

end BecknerOnofri.V2.Channel
