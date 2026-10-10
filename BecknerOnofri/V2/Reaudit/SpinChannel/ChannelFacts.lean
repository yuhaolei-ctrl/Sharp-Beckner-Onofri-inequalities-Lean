module

public import BecknerOnofri.V2.Reaudit.SpinChannel.JointLaw

@[expose] public section

/-!
# Exchangeability, common mean and all-minus cap of the spin law of the joint law

(`prop:section5-spin-entropy`(i), first assertions): for `ρ` satisfying the hypotheses of Proposition
5.11, `ν_ρ = (P_ρ).map σ` is an exchangeable probability measure with common spin mean
`t = ρ̂(e_1)` and `ν_ρ(σ_1 = ⋯ = σ_12 = -1) ≤ 2^{-12}`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace BecknerOnofri.V2.Reaudit.SpinChannel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.Spin BecknerOnofri.HighDim.EntropyShearer
open BecknerOnofri.V2.Channel

/-- A permutation of the spin coordinates. -/
def permSpins (π : Equiv.Perm (Fin 12)) (s : Spins) : Spins := fun i => s (π i)

theorem posSet_permSpins (π : Equiv.Perm (Fin 12)) (s : Spins) :
    posSet (permSpins π.symm s) = (posSet s).map π.toEmbedding := by
  ext j
  simp [posSet, permSpins]

/-- **Exchangeability of the spin law** (permutation invariance of `ρ` and the identical
coordinatewise construction of the spins). -/
theorem spinLaw_exchangeable (ρ : ProbabilityDensity 12)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π.symm i)) = ρ.value x)
    (π : Equiv.Perm (Fin 12)) :
    (spinLaw ρ).map (permSpins π) = spinLaw ρ := by
  have hex : Exchangeable (channelLaw ρ) := channelLaw_exchangeable_coordinates ρ hperm
  refine Measure.ext_of_singleton fun t => ?_
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton t)]
  have hpre : permSpins π ⁻¹' {t} = {permSpins π.symm t} := by
    ext s
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · rintro rfl; funext i; simp [permSpins]
    · rintro rfl; funext i; simp [permSpins]
  rw [hpre]
  have h1 : ((spinLaw ρ) {permSpins π.symm t}).toReal = ((spinLaw ρ) {t}).toReal := by
    have a := spinLaw_real_singleton_eq_channelLaw ρ (permSpins π.symm t)
    have b := spinLaw_real_singleton_eq_channelLaw ρ t
    simp only [measureReal_def] at a b
    rw [a, b, posSet_permSpins]
    exact hex π (posSet t)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h1

/-- **Common spin mean.**  `E[σ_i] = ρ̂(e_1)` for every `i`, and `ρ̂(e_1)` is real. -/
theorem spinCoord_mean (ρ : ProbabilityDensity 12) (hc : Continuous ρ.value)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π.symm i)) = ρ.value x)
    (i : Fin 12) :
    ∫ ω, spinCoord i ω ∂jointLaw ρ = firstCoefficient ρ := by
  have hex : Exchangeable (channelLaw ρ) := channelLaw_exchangeable_coordinates ρ hperm
  have h := integral_jointLaw_prod_spin ρ {i}
  simp only [Finset.prod_singleton] at h
  rw [h]
  have hi : (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12) =
      mean (countLaw (channelLaw ρ)) := by
    rw [mean_countLaw_eq hex i, Spin.channelLaw_joint_moment]
    simp
  unfold firstCoefficient
  rw [fourierCoeff_axis_re hc 0 1, ← Spin.channel_count_mean ρ hex, ← hi]
  rfl


/-- The event `σ_1 = ⋯ = σ_12 = -1`. -/
def allMinus : Set JointSpace := {ω | ω.2 = fun _ => false}

theorem measurableSet_allMinus : MeasurableSet allMinus :=
  (measurableSet_singleton (fun _ : Fin 12 => false)).preimage measurable_snd |>.congr rfl |> fun h => h

/-- `ν_ρ(σ ≡ -1) = 2^{-12} ∫ ρ ∏_i (1 - C_i) dm` (`eq:section5-channel-all-minus`). -/
theorem jointLaw_allMinus_eq (ρ : ProbabilityDensity 12) :
    (jointLaw ρ).real allMinus =
      (1 / 4096 : ℝ) * ∫ x, ρ.value x * ∏ i : Fin 12, (1 - (fourier 1 (x i)).re) ∂torusMeasure 12 := by
  have h1 : (jointLaw ρ).real allMinus = (spinLaw ρ).real {fun _ => false} := by
    simp [allMinus, spinLaw, measureReal_def,
      Measure.map_apply measurable_snd (measurableSet_singleton (fun _ : Fin 12 => false))]
    rfl
  rw [h1, spinLaw_real_singleton_eq_channelLaw]
  have : posSet (fun _ => false) = ∅ := by ext j; simp [posSet]
  rw [this]
  exact channelLaw_empty ρ

/-- **The all-minus cap** `ν_ρ(σ_1 = ⋯ = σ_12 = -1) ≤ 2^{-12}` (`eq:section5-global-p0`), for every
continuous probability density nondecreasing in the cosine of each coordinate (this is the property
of `e^{V(C)}` with `∂_iV ≥ 0` that the printed proof uses). -/
theorem jointLaw_allMinus_le (ρ : ProbabilityDensity 12) (hcont : Continuous ρ.value)
    (hm : CosMonotone ρ.value) : (jointLaw ρ).real allMinus ≤ 1 / 4096 := by
  rw [jointLaw_allMinus_eq]
  have h := integral_mul_prod_one_sub_cos_le (Finset.univ : Finset (Fin 12)) ρ.value
    (bm_of_continuous hcont) hm
  rw [ρ.mass] at h
  calc (1 / 4096 : ℝ) * _ ≤ (1 / 4096 : ℝ) * 1 := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 1 / 4096 := by ring

/-- `P(x ∈ A, σ = s) = ∫_A ρ(x) P(σ = s | x) dm(x)`: given the positions the spins are independent
with the printed Bernoulli probabilities. -/
theorem jointLaw_real_prod (ρ : ProbabilityDensity 12) {A : Set (Torus 12)} (hA : MeasurableSet A)
    (s : Spins) :
    (jointLaw ρ).real (A ×ˢ {s}) = ∫ x in A, ρ.value x * spinWeight x s ∂torusMeasure 12 := by
  have h2 := integral_indicator_one (μ := jointLaw ρ) (hA.prod (measurableSet_singleton s))
  rw [← h2]
  have hBM : BM ((A ×ˢ {s} : Set JointSpace).indicator 1) := by
    refine ⟨measurable_const.indicator (hA.prod (measurableSet_singleton s)), 1, fun ω => ?_⟩
    by_cases h : ω ∈ A ×ˢ {s} <;> simp [h]
  rw [integral_jointLaw ρ (hBM.integrable _), ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ A
  · simp only [hx, indicator_of_mem]
    congr 1
    rw [Finset.sum_eq_single s]
    · simp [hx]
    · intro t _ hts; simp [hts]
    · simp
  · simp [hx]

end BecknerOnofri.V2.Reaudit.SpinChannel
