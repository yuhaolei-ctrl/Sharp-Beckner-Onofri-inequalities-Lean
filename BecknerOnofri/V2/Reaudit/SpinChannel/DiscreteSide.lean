module

public import BecknerOnofri.V2.Reaudit.SpinChannel.ContinuousSide
public import BecknerOnofri.SpinEntropyChain
public import BecknerOnofri.SpinBinaryJensen

@[expose] public section

/-!
# The discrete side of the entropy comparison, under the joint law

* the chain rule `Hr(ν_ρ | μ_spin) = ∑_i E_P[I_B(E[σ_i | σ_{<i}])]` for the spin marginal of the joint law
  (the telescoping `prefixEntropy_step` of the existing development is applied to the prefix laws
  `ν_ρ(σ_{<k} = a)`, and each summand is rewritten as an expectation under `P_ρ`);
* the conditional Jensen step `E[I_B(E[t_i | σ_{<i}])] ≤ E[I_B(t_i)]`, using the conditional-expectation
  identity `E[σ_i | σ_{<i}] = E[t_i | σ_{<i}]` of `Conditional.lean` and Mathlib's conditional Jensen
  inequality `ConvexOn.map_condExp_le`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option warn.classDefReducibility false
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace BecknerOnofri.V2.Reaudit.SpinChannel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.Spin BecknerOnofri.HighDim.EntropyShearer
open BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.V2.Channel

/-- The relative entropy `Hr(ν | μ_spin) = ∑_s ν{s} log (ν{s} / μ_spin{s})` of a measure on `{±1}^{12}`
with respect to the uniform measure `μ_spin{s} = 1/4096`. -/
def relEntropy (ν : Measure Spins) : ℝ :=
  ∑ s : Spins, ν.real {s} * Real.log (ν.real {s} / (1 / 4096))

/-- Spin patterns supported on the first `k` coordinates correspond to subsets of the first `k` indices. -/
theorem sum_Pat_eq_powerset (k : ℕ) (F : Spins → ℝ) (G : Configuration → ℝ)
    (h : ∀ a ∈ Pat k, F a = G (posSet a)) :
    ∑ a ∈ Pat k, F a = ∑ σ ∈ (prefixSet k).powerset, G σ := by
  classical
  rw [Finset.sum_congr rfl h]
  refine Finset.sum_nbij' posSet (fun σ j => decide (j ∈ σ)) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    have ha' : spinMask k a = a := by simpa [Pat] using ha
    rw [Finset.mem_powerset]
    intro j hj
    simp only [posSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [mem_prefixSet]
    by_contra hjk
    have : spinMask k a j = a j := by rw [ha']
    simp [spinMask, hjk] at this
    simp [this] at hj
  · intro σ hσ
    rw [Finset.mem_powerset] at hσ
    simp only [Pat, Finset.mem_filter, Finset.mem_univ, true_and]
    funext j
    by_cases hj : j.val < k
    · simp [spinMask, hj]
    · have : j ∉ σ := fun h => hj (mem_prefixSet.mp (hσ h))
      simp [spinMask, hj, this]
  · intro a ha
    funext j
    simp [posSet]
  · intro σ hσ
    ext j
    simp [posSet]

theorem posSet_mem_powerset (k : ℕ) {a : Spins} (ha : a ∈ Pat k) : posSet a ∈ (prefixSet k).powerset := by
  classical
  have ha' : spinMask k a = a := by simpa [Pat] using ha
  rw [Finset.mem_powerset]
  intro j hj
  simp only [posSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [mem_prefixSet]
  by_contra hjk
  have : spinMask k a j = a j := by rw [ha']
  simp [spinMask, hjk] at this
  simp [this] at hj

/-- `prefixMass` of the existing development is the prefix probability `ν_ρ(σ_{<k} = a)`. -/
theorem prefixMass_posSet (ρ : ProbabilityDensity 12) (k : ℕ) (a : Spins) :
    prefixMass ρ.value k (posSet a) = prefixProb ρ k a := by
  unfold prefixMass prefixProb
  simp only [lik_eq_prefixLikelihood]

/-- The prefix entropy of the existing development as a sum over spin patterns. -/
theorem prefixEntropy_eq_sum_Pat (ρ : ProbabilityDensity 12) (k : ℕ) :
    prefixEntropy ρ.value k =
      ∑ a ∈ Pat k, prefixProb ρ k a * Real.log (2 ^ k * prefixProb ρ k a) := by
  unfold prefixEntropy
  symm
  apply sum_Pat_eq_powerset
  intro a ha
  rw [prefixMass_posSet]

/-- The numerator of the posterior mean, in the form used by `prefixEntropy_step`. -/
theorem ratio_eq_postMean (ρ : ProbabilityDensity 12) (i : Fin 12) (a : Spins) :
    (∫ x, ρ.value x * (prefixLikelihood i.val (posSet a) x * torusCosines x i) ∂torusMeasure 12) /
      prefixMass ρ.value i.val (posSet a) = postMean ρ i a := by
  rw [prefixMass_posSet]
  unfold postMean prefixSpinMoment
  simp only [lik_eq_prefixLikelihood]

/-- One summand of the chain rule: `∑_a ν_ρ(σ_{<i} = a) I_B(E[σ_i | σ_{<i} = a])`
is the expectation `E_P[I_B(E[σ_i | σ_{<i}])]` under the joint law. -/
theorem step_eq_expect (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12) :
    ∑ σ ∈ (prefixSet i.val).powerset, prefixMass ρ.value i.val σ * binaryCost
        ((∫ x, ρ.value x * (prefixLikelihood i.val σ x * torusCosines x i) ∂torusMeasure 12) /
          prefixMass ρ.value i.val σ) =
      ∫ ω, binaryCost (postMean ρ i (spinMask i.val ω.2)) ∂jointLaw ρ := by
  have hΘ : BM (fun y : JointSpace => binaryCost (postMean ρ i y.2)) :=
    BM.of_spin (fun a : Spins => binaryCost (postMean ρ i a))
  have h := integral_jointLaw_Yk ρ i.val hΘ
  have e : (fun ω : JointSpace => binaryCost (postMean ρ i (Yk i.val ω).2)) =
      fun ω => binaryCost (postMean ρ i (spinMask i.val ω.2)) := rfl
  simp only [e] at h
  rw [h, integral_rho_sum_lik ρ hρ i.val (fun a => binaryCost (postMean ρ i a))]
  symm
  apply sum_Pat_eq_powerset
  intro a ha
  rw [ratio_eq_postMean, prefixMass_posSet]

/-- **Chain rule for the spin entropy** (prefix form): for `k ≤ 12`,
`H_k = ∑_{i<k} E_P[I_B(E[σ_i | σ_{<i}])]`, `H_k` the relative entropy of the law of `σ_{<k}`. -/
theorem prefixEntropy_chain (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (k : ℕ)
    (hk : k ≤ 12) :
    prefixEntropy ρ.value k = ∑ i ∈ prefixSet k,
      ∫ ω, binaryCost (postMean ρ i (spinMask i.val ω.2)) ∂jointLaw ρ := by
  induction k with
  | zero => simp [prefixEntropy_zero ρ.mass]
  | succ k ih =>
    let i : Fin 12 := ⟨k, by omega⟩
    change prefixEntropy ρ.value (i.val + 1) = _
    rw [prefixEntropy_step hρ i, step_eq_expect ρ hρ i, ih (by omega)]
    change _ = ∑ j ∈ prefixSet (i.val + 1), _
    rw [prefixSet_step, Finset.sum_insert (by simp)]
    ring


theorem Pat_twelve : Pat 12 = Finset.univ := by
  ext a
  simp only [Pat, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  funext j
  simp [spinMask, j.isLt]

/-- `ν_ρ(σ = a) = ν_ρ(σ_{<12} = a)`: the spin marginal of the joint law on a full pattern. -/
theorem spinLaw_real_singleton_eq_prefixProb (ρ : ProbabilityDensity 12) (a : Spins) :
    (spinLaw ρ).real {a} = prefixProb ρ 12 a := by
  rw [spinLaw_real_singleton_eq_channelLaw]
  unfold channelLaw prefixProb
  apply integral_congr_ae
  filter_upwards [] with x
  rw [lik_eq_prefixLikelihood, prefixLikelihood_full]

/-- The relative entropy of the spin marginal of the joint law is the full prefix entropy. -/
theorem relEntropy_spinLaw_eq_prefixEntropy (ρ : ProbabilityDensity 12) :
    relEntropy (spinLaw ρ) = prefixEntropy ρ.value 12 := by
  rw [prefixEntropy_eq_sum_Pat, Pat_twelve]
  unfold relEntropy
  apply Finset.sum_congr rfl
  intro a _
  rw [spinLaw_real_singleton_eq_prefixProb]
  congr 2
  norm_num
  ring

/-- The relative entropy of the spin marginal of the joint law is the relative entropy
`Hr(ν_ρ | μ_spin)` of the existing development (`spinRelEntropy (channelLaw ρ)`). -/
theorem relEntropy_spinLaw_eq_spinRelEntropy (ρ : ProbabilityDensity 12) :
    relEntropy (spinLaw ρ) = spinRelEntropy (channelLaw ρ) := by
  classical
  unfold relEntropy spinRelEntropy
  refine Finset.sum_nbij' posSet (fun σ j => decide (j ∈ σ)) (fun _ _ => Finset.mem_univ _)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a _; funext j; simp [posSet]
  · intro σ _; ext j; simp [posSet]
  · intro a _
    rw [spinLaw_real_singleton_eq_channelLaw]

/-- **Chain rule for the spin entropy** (`Hr(ν_ρ | μ_spin) = ∑_i E[I_B(E[σ_i | σ_{<i}])]`). -/
theorem relEntropy_chain (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) :
    relEntropy (spinLaw ρ) =
      ∑ i : Fin 12, ∫ ω, binaryCost (postMean ρ i (spinMask i.val ω.2)) ∂jointLaw ρ := by
  rw [relEntropy_spinLaw_eq_prefixEntropy, prefixEntropy_chain ρ hρ 12 le_rfl, prefixSet_twelve]

/-- **Conditional Jensen step**: `E[I_B(E[σ_i | σ_{<i}])] ≤ E[I_B(t_i)]`, where
`E[σ_i | σ_{<i}] = E[t_i | σ_{<i}]` (Mathlib's `ConvexOn.map_condExp_le`, `I_B` convex on `[-1,1]`). -/
theorem expect_binaryCost_postMean_le (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value)
    (i : Fin 12) :
    ∫ ω, binaryCost (postMean ρ i (spinMask i.val ω.2)) ∂jointLaw ρ ≤
      ∫ ω, binaryCost (condInt ρ.value i (cosFn 1) ω.1) ∂jointLaw ρ := by
  set t : JointSpace → ℝ := fun ω => condInt ρ.value i (cosFn 1) ω.1 with ht
  have hbm : BM t := BM.condInt ρ hρ i (bmc_cosFn 1)
  have htab : ∀ ω, t ω ∈ Icc (-1 : ℝ) 1 := by
    intro ω
    have := conditional_moment_abs_le_one hρ i 1 ω.1
    exact abs_le.mp this
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (binaryCost_continuous.norm.continuousOn : ContinuousOn (fun y => ‖binaryCost y‖) (Icc (-1 : ℝ) 1))
  have hBt : BM (fun ω => binaryCost (t ω)) :=
    ⟨binaryCost_continuous.measurable.comp hbm.1, C,
      fun ω => hC (mem_image_of_mem (fun y => ‖binaryCost y‖) (htab ω))⟩
  have hJ := ConvexOn.map_condExp_le (μ := jointLaw ρ) (m := sigmaSpin i.val) (f := t)
    (φ := binaryCost) (s := Icc (-1 : ℝ) 1) (sigmaSpin_le i.val)
    binaryCost_convex (binaryCost_continuous.lowerSemicontinuous.lowerSemicontinuousOn _)
    (Filter.Eventually.of_forall htab) isClosed_Icc (hbm.integrable _) (hBt.integrable _)
  have h2 : condExp (sigmaSpin i.val) (jointLaw ρ) t =ᵐ[jointLaw ρ]
      fun ω => postMean ρ i (spinMask i.val ω.2) :=
    (condExp_spin_prefix_eq ρ hρ i).symm.trans (condExp_spin_prefix_explicit ρ hρ i)
  have hpm : BM (fun ω : JointSpace => binaryCost (postMean ρ i (spinMask i.val ω.2))) := by
    have := BM.of_spin (fun a : Spins => binaryCost (postMean ρ i (spinMask i.val a)))
    exact this
  have e1 : ∫ ω, binaryCost (postMean ρ i (spinMask i.val ω.2)) ∂jointLaw ρ =
      ∫ ω, (binaryCost ∘ condExp (sigmaSpin i.val) (jointLaw ρ) t) ω ∂jointLaw ρ := by
    apply integral_congr_ae
    filter_upwards [h2] with ω hω
    simp only [Function.comp, hω]
  have hint : Integrable (binaryCost ∘ condExp (sigmaSpin i.val) (jointLaw ρ) t) (jointLaw ρ) := by
    refine (hpm.integrable _).congr ?_
    filter_upwards [h2] with ω hω
    simp only [Function.comp, hω]
  have e2 : ∫ ω, (condExp (sigmaSpin i.val) (jointLaw ρ) (binaryCost ∘ t)) ω ∂jointLaw ρ =
      ∫ ω, binaryCost (t ω) ∂jointLaw ρ :=
    integral_condExp (sigmaSpin_le i.val)
  rw [e1, ← e2]
  exact integral_mono_ae hint integrable_condExp hJ

/-- **Discrete side of `eq:section5-channel-continuous-entropy`'s comparison**:
`Hr(ν_ρ | μ_spin) ≤ ∑_i E_P[I_B(t_i)]`. -/
theorem relEntropy_le_sum_expect (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) :
    relEntropy (spinLaw ρ) ≤
      ∑ i : Fin 12, ∫ ω, binaryCost (condInt ρ.value i (cosFn 1) ω.1) ∂jointLaw ρ := by
  rw [relEntropy_chain ρ hρ]
  exact Finset.sum_le_sum fun i _ => expect_binaryCost_postMean_le ρ hρ i

end BecknerOnofri.V2.Reaudit.SpinChannel
