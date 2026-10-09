module

public import BecknerOnofri.V2.Channel.Assembly
public import BecknerOnofri.V2.Channel.AllMinusCap
public import BecknerOnofri.V2.Channel.FourierAxis
public import BecknerOnofri.SpinChannelSymmetry
public import BecknerOnofri.SpinChannelMean
public import BecknerOnofri.CosineMixtureStatementDefinitions

@[expose] public section

/-!
# Proposition 5.12(i) (`prop:section5-spin-entropy`(i)), work package G10

If `ρ` satisfies the hypotheses of Proposition 5.11 (`prop:section5-global-entropy-gap`), then the
spin law `ν_ρ` (`channelLaw ρ`) of the binary channel `eq:section5-global-channel` is an exchangeable
probability measure with common spin mean `t = ρ̂(e_1)`, satisfies
`ν_ρ(σ_1 = ⋯ = σ_12 = -1) ≤ 2^{-12}`, and
`Ent(ρ) ≥ 2 Hr(ν_ρ | μ_spin) + 12 ψ(t) + Σ_i [|ρ̂(2e_i)|²/40 + 2|ρ̂(3e_i)|²/15 + (27/40) Σ_{n≥4} |ρ̂(ne_i)|²/n]`.

Conventions.
* A spin configuration is the finset of its positive spins; `ν_ρ σ` is the probability of that
  configuration, `μ_spin σ = 1/4096`, so `Hr(ν|μ_spin) = Σ_σ ν σ log(ν σ/(1/4096))`.
* `ψ = Circle.psi`, `ψ(t) = t⁴/(14 - 10t²)`.
* `Σ_{n≥4}` is written as `Σ'_{n∈ℕ}` with the index shifted by four.
* The printed hypotheses are: smooth strictly positive probability density, permutation invariance,
  the cosine-mixture form `eq:mixture`, `log ρ = V(cos 2πx)` with `V ∈ C^∞([-1,1]^{12})`,
  `∂_iV ≥ 0`, `∂_i²V ≥ 0`.  The proof uses only `∂_iV ≥ 0` (the manuscript says so after
  Proposition 5.11); the mixture and second-derivative hypotheses are kept in
  `spin_entropy_comparison_i` for fidelity to the printed statement, and the unused-hypothesis-free
  version is `spin_entropy_comparison_i_core`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped BigOperators ContDiff
namespace BecknerOnofri.V2.Channel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.HighDim.EntropyShearer
open BecknerOnofri.HighDim.Spin (channelLaw Exchangeable jointSpin countLaw mean)

/-- The relative entropy `Hr(ν | μ_spin)` of a spin law with respect to the uniform measure. -/
def spinRelEntropy (ν : Spin.Configuration → ℝ) : ℝ :=
  ∑ σ : Spin.Configuration, ν σ * Real.log (ν σ / (1 / 4096))

/-- The common spin mean `t = ρ̂(e_1)`: the real part of the first Fourier coefficient. -/
def firstCoefficient (ρ : ProbabilityDensity 12) : ℝ :=
  (HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re

theorem rep_even {V : (Fin 12 → ℝ) → ℝ} {f : Torus 12 → ℝ}
    (hrep : ∀ x, f x = Real.exp (V (cosineVector x))) (x : Torus 12) : f (-x) = f x := by
  rw [hrep, hrep]
  congr 2
  funext j
  simp [cosineVector, fourier_apply, AddCircle.toCircle_neg]

/-- **Proposition 5.12(i), core form** (no unused hypotheses). -/
theorem spin_entropy_comparison_i_core (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    {V : (Fin 12 → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hrep : ∀ x, ρ.value x = Real.exp (V (cosineVector x)))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v) :
    -- `ν_ρ` is an exchangeable probability measure with common spin mean `t = ρ̂(e_1)`
    (Exchangeable (channelLaw ρ) ∧ (∀ σ, 0 ≤ channelLaw ρ σ) ∧ (∑ σ, channelLaw ρ σ) = 1 ∧
      (HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).im = 0 ∧
      ∀ i : Fin 12, (∑ σ, channelLaw ρ σ * jointSpin {i} σ) = firstCoefficient ρ) ∧
    -- the all-minus probability
    channelLaw ρ ∅ ≤ 1 / 4096 ∧
    -- the entropy bound
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4))) ∧
    2 * spinRelEntropy (channelLaw ρ) + 12 * BecknerOnofri.V2.Circle.psi (firstCoefficient ρ) +
      ∑ i : Fin 12, ((1 / 40) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 +
        (2 / 15) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 +
        (27 / 40) * ∑' n : ℕ,
          ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4)) ≤
      entropy ρ := by
  have hc : Continuous ρ.value := rep_continuous hV.continuousOn hrep
  have heven : ∀ x, ρ.value (-x) = ρ.value x := rep_even hrep
  have hex : Exchangeable (channelLaw ρ) := by
    apply Spin.channelLaw_exchangeable_coordinates
    intro π x
    exact hperm π.symm x
  -- common mean
  have hmean (i : Fin 12) : (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12) =
      firstCoefficient ρ := by
    have hi : (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12) =
        mean (countLaw (channelLaw ρ)) := by
      rw [mean_countLaw_eq hex i, Spin.channelLaw_joint_moment]
      simp
    unfold firstCoefficient
    rw [fourierCoeff_axis_re hc 0 1, hi, Spin.channel_count_mean ρ hex]
  obtain ⟨hsum, hmain⟩ := channel_entropy_core ρ hV h1 hrep hs
  have hnorm (i : Fin 12) (n : ℤ) : ‖HighDim.fourierCoeff ρ.value (Pi.single i n)‖ ^ 2 =
      (∫ x, ρ.value x * (fourier n (x i)).re ∂torusMeasure 12) ^ 2 :=
    fourierCoeff_axis_norm_sq hc heven i n
  have hcast (n : ℕ) : (((n + 4 : ℕ) : ℤ)) = (n : ℤ) + 4 := by push_cast; ring
  have hq (i : Fin 12) (n : ℕ) :
      ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4) =
      (∫ x, ρ.value x * (fourier ((n + 4 : ℕ) : ℤ) (x i)).re ∂torusMeasure 12) ^ 2 /
        ((n : ℝ) + 4) := by
    rw [hnorm, hcast]
  refine ⟨⟨hex, fun σ => Spin.channelLaw_nonneg ρ σ, Spin.channelLaw_mass ρ,
    fourierCoeff_even_im heven _, fun i => ?_⟩, allMinus_le hc ?_, ?_, ?_⟩
  · rw [Spin.channelLaw_joint_moment]
    simp only [Finset.prod_singleton]
    exact hmean i
  · exact rep_cosMonotone hV h1 hrep
  · intro i
    simpa only [hq] using hsum i
  · have e1 : (∑ i : Fin 12, BecknerOnofri.V2.Circle.psi
        (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12)) =
        12 * BecknerOnofri.V2.Circle.psi (firstCoefficient ρ) := by
      simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]
    have e2 : (∑ i : Fin 12, ((1 / 40) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 +
        (2 / 15) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 +
        (27 / 40) * ∑' n : ℕ,
          ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4))) =
        (1 / 40) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12) ^ 2) +
        (2 / 15) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 3 (x i)).re ∂torusMeasure 12) ^ 2) +
        (27 / 40) * (∑ i : Fin 12, ∑' n : ℕ,
          (∫ x, ρ.value x * (fourier ((n + 4 : ℕ) : ℤ) (x i)).re ∂torusMeasure 12) ^ 2 /
            ((n : ℝ) + 4)) := by
      have h2 (i : Fin 12) := hnorm i 2
      have h3 (i : Fin 12) := hnorm i 3
      have h4 (i : Fin 12) : (∑' n : ℕ,
          ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4)) =
          ∑' n : ℕ, (∫ x, ρ.value x * (fourier ((n + 4 : ℕ) : ℤ) (x i)).re ∂torusMeasure 12) ^ 2 /
            ((n : ℝ) + 4) := tsum_congr (hq i)
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h2, h3, h4]
    have e3 : spinRelEntropy (channelLaw ρ) =
        ∑ σ : Spin.Configuration, channelLaw ρ σ * Real.log (channelLaw ρ σ / (1 / 4096)) := rfl
    rw [e2, e3]
    have h := hmain
    rw [e1] at h
    linarith

/-- **Proposition 5.12(i)** (`prop:section5-spin-entropy`(i)), with the hypotheses exactly as printed
(smooth strictly positive density `hs`, `hp`; permutation invariance `hperm`; cosine-mixture form
`hmix`; `log ρ = V(cos 2πx)` with `V ∈ C^∞([-1,1]^{12})`; `∂_iV ≥ 0`; `∂_i²V ≥ 0`).  The hypotheses
`hmix` and `h2` are not used by the proof (see the module docstring). -/
theorem spin_entropy_comparison_i (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hp : ∀ x, 0 < ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    (_hmix : IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hlog : ∀ x, Real.log (ρ.value x) = V (cosineVector x))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v)
    (_h2 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i (cosinePartial i V) v) :
    (Exchangeable (channelLaw ρ) ∧ (∀ σ, 0 ≤ channelLaw ρ σ) ∧ (∑ σ, channelLaw ρ σ) = 1 ∧
      (HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).im = 0 ∧
      ∀ i : Fin 12, (∑ σ, channelLaw ρ σ * jointSpin {i} σ) = firstCoefficient ρ) ∧
    channelLaw ρ ∅ ≤ 1 / 4096 ∧
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4))) ∧
    2 * spinRelEntropy (channelLaw ρ) + 12 * BecknerOnofri.V2.Circle.psi (firstCoefficient ρ) +
      ∑ i : Fin 12, ((1 / 40) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 +
        (2 / 15) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 +
        (27 / 40) * ∑' n : ℕ,
          ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4)) ≤
      entropy ρ :=
  spin_entropy_comparison_i_core ρ hs hperm hV (fun x => by rw [← hlog x, Real.exp_log (hp x)]) h1

end BecknerOnofri.V2.Channel
