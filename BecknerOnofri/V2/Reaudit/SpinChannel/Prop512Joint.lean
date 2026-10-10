module

public import BecknerOnofri.V2.Reaudit.SpinChannel.DiscreteSide
public import BecknerOnofri.V2.Channel.Prop512

@[expose] public section

/-!
# Proposition 5.12(i) (`prop:section5-spin-entropy`(i)) through the explicit joint law

`spin_entropy_jointLaw` is the printed statement with every object the joint law `P_ρ` of positions and
spins (`Conditional.lean`, `ContinuousSide.lean`, `DiscreteSide.lean`): the spin law `ν_ρ` is the spin
marginal `spinLaw ρ`, `Hr(ν_ρ | μ_spin)` is `relEntropy (spinLaw ρ)`, and the common mean is
`E[σ_i]`.  The theorem `spin_entropy_comparison_i_core_joint` has literally the statement of the existing
`V2.Channel.spin_entropy_comparison_i_core`, but is proved from the joint-law theorem (U15 bridge); the
module ends with the bridge identities between the existing nested integrals and expectations under
`P_ρ`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option warn.classDefReducibility false
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace BecknerOnofri.V2.Reaudit.SpinChannel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.Spin BecknerOnofri.HighDim.EntropyShearer
open BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.V2.Channel

/-- `ν_ρ(σ ≡ -1)` in terms of the spin marginal. -/
theorem jointLaw_allMinus_eq_spinLaw (ρ : ProbabilityDensity 12) :
    (jointLaw ρ).real allMinus = (spinLaw ρ).real {fun _ => false} := by
  simp [allMinus, spinLaw, measureReal_def,
    Measure.map_apply measurable_snd (measurableSet_singleton (fun _ : Fin 12 => false))]
  rfl

open scoped ContDiff in
/-- **Proposition 5.12(i), joint-law form.**  With `P_ρ` the joint law of positions and spins:
the spin marginal `ν_ρ` is an exchangeable probability measure, `E[σ_i] = ρ̂(e_1)` for all `i` (`ρ̂(e_1)`
real), `ν_ρ(σ ≡ -1) ≤ 2^{-12}`, the series are summable and
`2 Hr(ν_ρ | μ_spin) + 12 ψ(t) + ∑_i [ |ρ̂(2e_i)|²/40 + 2|ρ̂(3e_i)|²/15 + (27/40) ∑_{n≥4} |ρ̂(ne_i)|²/n ] ≤ Ent(ρ)`. -/
theorem spin_entropy_jointLaw (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    {V : (Fin 12 → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hrep : ∀ x, ρ.value x = Real.exp (V (cosineVector x)))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v) :
    (IsProbabilityMeasure (spinLaw ρ) ∧
      (∀ π : Equiv.Perm (Fin 12), (spinLaw ρ).map (permSpins π) = spinLaw ρ) ∧
      (HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).im = 0 ∧
      ∀ i : Fin 12, ∫ w, spinCoord i w ∂jointLaw ρ = firstCoefficient ρ) ∧
    (spinLaw ρ).real {fun _ => false} ≤ 1 / 4096 ∧
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4))) ∧
    2 * relEntropy (spinLaw ρ) + 12 * BecknerOnofri.V2.Circle.psi (firstCoefficient ρ) +
      ∑ i : Fin 12, ((1 / 40) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 +
        (2 / 15) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 +
        (27 / 40) * ∑' n : ℕ,
          ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4)) ≤
      entropy ρ := by
  have hc : Continuous ρ.value := rep_continuous hV.continuousOn hrep
  have hf : PositiveBounded ρ.value := rep_positiveBounded hV.continuousOn hrep
  have heven : ∀ x, ρ.value (-x) = ρ.value x := rep_even hrep
  have hperm' : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π.symm i)) = ρ.value x :=
    fun π x => hperm π.symm x
  have hE (i : Fin 12) (n : ℕ) : ∫ w, cosFn n (w.1 i) ∂jointLaw ρ =
      ∫ x, ρ.value x * (fourier (n : ℤ) (x i)).re ∂torusMeasure 12 :=
    integral_coord ρ i (bmc_cosFn n)
  have hmean (i : Fin 12) : ∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12 = firstCoefficient ρ := by
    rw [← spinCoord_mean ρ hc hperm' i]
    have h := integral_jointLaw_prod_spin ρ {i}
    simp only [Finset.prod_singleton] at h
    rw [h]
    rfl
  have hE1 (i : Fin 12) : ∫ w, cosFn 1 (w.1 i) ∂jointLaw ρ = firstCoefficient ρ := by
    rw [hE]; simpa using hmean i
  have hnorm (i : Fin 12) (n : ℤ) : ‖HighDim.fourierCoeff ρ.value (Pi.single i n)‖ ^ 2 =
      (∫ x, ρ.value x * (fourier n (x i)).re ∂torusMeasure 12) ^ 2 :=
    fourierCoeff_axis_norm_sq hc heven i n
  have hcast (n : ℕ) : (((n + 4 : ℕ) : ℤ)) = (n : ℤ) + 4 := by push_cast; ring
  have hq (i : Fin 12) (n : ℕ) :
      ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4) =
      (∫ w, cosFn (n + 4) (w.1 i) ∂jointLaw ρ) ^ 2 / ((n : ℝ) + 4) := by
    rw [hnorm, hE, hcast]
  have h2 (i : Fin 12) : ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 =
      (∫ w, cosFn 2 (w.1 i) ∂jointLaw ρ) ^ 2 := by
    rw [hnorm, hE]; norm_num
  have h3 (i : Fin 12) : ‖HighDim.fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 =
      (∫ w, cosFn 3 (w.1 i) ∂jointLaw ρ) ^ 2 := by
    rw [hnorm, hE]; norm_num
  obtain ⟨hsum, hmain⟩ := continuous_entropy_jointLaw ρ hV h1 hrep hs
  have hdisc := relEntropy_le_sum_expect ρ hf
  refine ⟨⟨inferInstance, spinLaw_exchangeable ρ hperm', fourierCoeff_even_im heven _,
    spinCoord_mean ρ hc hperm'⟩, ?_, ?_, ?_⟩
  · rw [← jointLaw_allMinus_eq_spinLaw]
    exact jointLaw_allMinus_le ρ hc (rep_cosMonotone hV h1 hrep)
  · intro i
    simpa only [hq] using hsum i
  · have e1 : (∑ i : Fin 12, BecknerOnofri.V2.Circle.psi (∫ w, cosFn 1 (w.1 i) ∂jointLaw ρ)) =
        12 * BecknerOnofri.V2.Circle.psi (firstCoefficient ρ) := by
      simp only [hE1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]
    have e2 : (∑ i : Fin 12, ((1 / 40) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 +
        (2 / 15) * ‖HighDim.fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 +
        (27 / 40) * ∑' n : ℕ,
          ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4))) =
        (1 / 40) * (∑ i : Fin 12, (∫ w, cosFn 2 (w.1 i) ∂jointLaw ρ) ^ 2) +
        (2 / 15) * (∑ i : Fin 12, (∫ w, cosFn 3 (w.1 i) ∂jointLaw ρ) ^ 2) +
        (27 / 40) * (∑ i : Fin 12, ∑' n : ℕ,
          (∫ w, cosFn (n + 4) (w.1 i) ∂jointLaw ρ) ^ 2 / ((n : ℝ) + 4)) := by
      have h4 (i : Fin 12) : (∑' n : ℕ,
          ‖HighDim.fourierCoeff ρ.value (Pi.single i ((n : ℤ) + 4))‖ ^ 2 / ((n : ℝ) + 4)) =
          ∑' n : ℕ, (∫ w, cosFn (n + 4) (w.1 i) ∂jointLaw ρ) ^ 2 / ((n : ℝ) + 4) :=
        tsum_congr (hq i)
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h2, h3, h4]
    rw [e2]
    rw [e1] at hmain
    linarith

open scoped ContDiff in
/-- **U15 bridge**: the statement of `V2.Channel.spin_entropy_comparison_i_core` (nested form, `Hr` of the
function `channelLaw ρ`) proved from the joint-law theorem `spin_entropy_jointLaw` and the identification
`relEntropy (spinLaw ρ) = spinRelEntropy (channelLaw ρ)`; the exchangeability, nonnegativity and mass
assertions on `channelLaw ρ` are the existing channel-level ones (`Spin.channelLaw_exchangeable_coordinates`,
`Spin.channelLaw_nonneg`, `Spin.channelLaw_mass`). -/
theorem spin_entropy_comparison_i_core_joint (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    {V : (Fin 12 → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hrep : ∀ x, ρ.value x = Real.exp (V (cosineVector x)))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v) :
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
      entropy ρ := by
  have hc : Continuous ρ.value := rep_continuous hV.continuousOn hrep
  have hperm' : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π.symm i)) = ρ.value x :=
    fun π x => hperm π.symm x
  have heven : ∀ x, ρ.value (-x) = ρ.value x := rep_even hrep
  obtain ⟨⟨-, -, him, hmean⟩, hcap, hsum, hent⟩ := spin_entropy_jointLaw ρ hs hperm hV hrep h1
  have hex : Exchangeable (channelLaw ρ) := Spin.channelLaw_exchangeable_coordinates ρ hperm'
  refine ⟨⟨hex, fun σ => Spin.channelLaw_nonneg ρ σ, Spin.channelLaw_mass ρ, him, fun i => ?_⟩, ?_,
    hsum, ?_⟩
  · rw [Spin.channelLaw_joint_moment]
    simp only [Finset.prod_singleton]
    rw [← hmean i]
    have h := integral_jointLaw_prod_spin ρ {i}
    simp only [Finset.prod_singleton] at h
    rw [h]
    rfl
  · have := hcap
    rw [spinLaw_real_singleton_eq_channelLaw] at this
    have e : posSet (fun _ => false) = ∅ := by ext j; simp [posSet]
    rwa [e] at this
  · rwa [← relEntropy_spinLaw_eq_spinRelEntropy]

open scoped ContDiff in
/-- **Proposition 5.12(i)** with the hypotheses exactly as printed (as `V2.Channel.spin_entropy_comparison_i`),
proved through the joint law. -/
theorem spin_entropy_comparison_i_joint (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
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
  spin_entropy_comparison_i_core_joint ρ hs hperm hV (fun x => by rw [← hlog x, Real.exp_log (hp x)]) h1

/-! ### Bridge between the existing nested integrals and expectations under `P_ρ` (U15) -/

/-- `∫ ρ I_B(t_i) dm = E_P[I_B(t_i)]`: the nested conditional-moment integral of the existing development
is the expectation of `I_B(t_i)` under the joint law (`t_i` the conditional mean of `cos 2πx_i` given
`x_{<i}`). -/
theorem nested_binaryCost_eq_expect (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12) :
    ∫ x, ρ.value x * binaryCost (conditionalCosineMoment ρ.value i 1 x) ∂torusMeasure 12 =
      ∫ ω, binaryCost (condInt ρ.value i (cosFn 1) ω.1) ∂jointLaw ρ := by
  exact (integral_jointLaw_position ρ (conditional_binaryCost_bounded hρ i)).symm

/-- The nested-integral form of the discrete bound (the statement of the existing
`Spin.channel_entropy_le_conditional`) from the joint-law chain rule and conditional Jensen. -/
theorem channel_entropy_le_conditional_joint (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) :
    (∑ σ : Configuration, channelLaw ρ σ * Real.log (channelLaw ρ σ / (1 / 4096))) ≤
      ∑ i : Fin 12, ∫ x, ρ.value x * binaryCost (conditionalCosineMoment ρ.value i 1 x)
        ∂torusMeasure 12 := by
  have h := relEntropy_le_sum_expect ρ hρ
  rw [relEntropy_spinLaw_eq_spinRelEntropy] at h
  simp only [nested_binaryCost_eq_expect ρ hρ]
  exact h

/-- The statement of the bridge theorem is that of the existing nested one. -/
theorem channel_entropy_le_conditional_joint_statement_eq :
    (type_of% @channel_entropy_le_conditional_joint) = (type_of% @Spin.channel_entropy_le_conditional) := rfl

theorem spin_entropy_comparison_i_core_joint_statement_eq :
    (type_of% @spin_entropy_comparison_i_core_joint) = (type_of% @Channel.spin_entropy_comparison_i_core) := rfl

theorem spin_entropy_comparison_i_joint_statement_eq :
    (type_of% @spin_entropy_comparison_i_joint) = (type_of% @Channel.spin_entropy_comparison_i) := rfl

end BecknerOnofri.V2.Reaudit.SpinChannel
