module

public import BecknerOnofri.V2.Reaudit.Mixtures.Selection
public import BecknerOnofri.V2.Reaudit.Mixtures.PrintedGap
public import BecknerOnofri.V2.Section3.Lemma31
public import BecknerOnofri.V2.Section3.FinalCore
public import BecknerOnofri.V2.Section3.CircleBound
public import BecknerOnofri.V2.Section3.CircleCase
public import BecknerOnofri.ThresholdReduction
public import BecknerOnofri.ConcentrationDivergence

@[expose] public section

/-! # Theorem 1.1 (`thm:intro-low-dimensional`, `1 ≤ d ≤ 10`): the route-aligned assembly (S001, S016, S023)

This module assembles Theorem 1.1 exactly as the printed three-line proof does, through the
written-route declarations, with the leaves replaced by the route-aligned versions of this package:

* the minimizing mixture of Lemma `lem:selection-full-entropy-domain` is supplied by
  `canonical_selection_written` (S016: `coordinate_rearranged_minimizer` + `cosine_representation`),
  in the proof of `entropy_bound_of_minimizing_mixtures_aligned` (Lemma 3.1, `E1`);
* the two hypotheses of Lemma 3.1 are `mixtureInequality_printed`, `mixtureStrictness_printed`
  (S023/U06: `PrintedGap.lean`, the existing `mixture_energy_gap` with the countable limit);
* Proposition 3.7 is `prop_3_7_aligned` (the printed deduction from Lemma 3.1);
* the circle case, `FinalCore` (`potential_bound_of_full`, `extendedBound_of_full`, `collapse_isLeast`,
  `pressure_formula`, `globalTransition_eq`, `coefficientDefect_collapse_eq_zero_of_full`) and the
  entropy-to-`Challenge` translation are reused unchanged.

`theorem_1_1_aligned` has the type of `Section3.theorem_1_1_written`, and the eleven `low_dim_*`
declarations have exactly the types of `V2.Final.low_dim_*` (`Final/Low.lean`).  The files
`Final/Endpoint.lean` (and thus `Assembly`, `Onset`) are not imported: the two generic translation
lemmas `entropyEquality_iff_challenge` and `ereal_le_extendedEntropy` are re-proved verbatim here. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate

namespace BecknerOnofri.V2.Reaudit.Mixtures
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab BecknerOnofri.V2.Section3
open BecknerOnofri.V2.Rearrangement

variable {d : ℕ}

/-! ## Lemma 3.1 (`lem:collapse-conditional-reduction`) with the written-route selection -/

/-- The contradiction argument of E1 (same statement as `Section3.entropy_bound_of_minimizing_mixtures`),
with the minimizing mixture of Lemma 2.13 supplied by the written-route selection
`canonical_selection_written` (`coordinate_rearranged_minimizer` + `cosine_representation`)
instead of the polarization-closure `canonical_selection`. -/
theorem entropy_bound_of_minimizing_mixtures_aligned (hd : 0 < d) (hmix : SmoothMixtureInequality d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) : EntropyBound d ρ := by
  by_contra hviol
  have hviol : (torusEntropy ρ.value).toReal <
      (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal := not_le.mp hviol
  have hc := kernelConstant_pos hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hS0 := entropy_toReal_nonneg ρ hρ
  have hN0 : 0 ≤ (negSobolevEnergy ρ.value).toReal := ENNReal.toReal_nonneg
  set S := (torusEntropy ρ.value).toReal with hS
  set N := (negSobolevEnergy ρ.value).toReal with hN
  have hNpos : 0 < N := by
    rcases hN0.eq_or_lt with h | h
    · rw [← h] at hviol; nlinarith
    · exact h
  have hcN : 0 < kernelConstant d * N := mul_pos hc hNpos
  -- the coupling `β = S/(c N) + d ∈ (0, 2d)`
  set β : ℝ := S / (kernelConstant d * N) + d with hβdef
  have hq : S / (kernelConstant d * N) < d := by
    rw [div_lt_iff₀ hcN]; nlinarith
  have hβ : 0 < β := by
    have : 0 ≤ S / (kernelConstant d * N) := div_nonneg hS0 hcN.le
    rw [hβdef]; linarith
  have hβd : β < 2 * (d : ℝ) := by rw [hβdef]; linarith
  -- the free energy of `ρ` at `β` is strictly positive
  have hpos : 0 < β * kernelConstant d / 2 * N - S := by
    have : β * kernelConstant d / 2 * N = S / 2 + d * kernelConstant d * N / 2 := by
      rw [hβdef]; field_simp
    rw [this]; linarith
  obtain ⟨ρs, hρs⟩ := OptimizerDuality.exists_minimizer hd hβ hβd
  obtain ⟨η, u, -, hηmin, -, -, -, -, hsm, hηpos, -, -, -, -, -, -, -, hηmix, -, -⟩ :=
    canonical_selection_written hd β hβ hβd ρs hρs
  have hle := hηmin.2 ρ hρ
  rw [pressureValue_le_iff_real hd β ρ η hρ hηmin.1] at hle
  have hbound := hmix η hηmin.1 ⟨hsm, hηpos, hηmix⟩
  unfold EntropyBound at hbound
  have hNη : 0 ≤ (negSobolevEnergy η.value).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * (d : ℝ) - β) (mul_nonneg hc.le hNη)]


/-- **E2 (density inequality).**  Heat regularization: `ρ_t` is smooth and strictly positive, so
E1 applies to it; `t ↓ 0` with the entropy and energy limits of Lemma 2.1 (route difference: the
manuscript takes finite subsets of frequencies, monotone convergence and entropy contraction; here
the full convergence `Ent(ρ_t) → Ent(ρ)`, `c_d‖ρ_t‖² → c_d‖ρ‖²` of Section 2 is used instead). -/
theorem entropy_bound_full_aligned (hd : 0 < d) (hmix : SmoothMixtureInequality d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) : EntropyBound d ρ := by
  have hlim1 := (heat_energy_real_tendsto_nhdsGT hd ρ hρ).const_mul (d : ℝ)
  simp only [← mul_assoc] at hlim1
  have hent : torusEntropy ρ.value ≠ ∞ := (torusEntropy_density_ne_top_iff ρ).2 hρ
  have hlim2 : Tendsto (fun t : ℝ => (torusEntropy (heatRegularization ρ t)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 (torusEntropy ρ.value).toReal) :=
    (ENNReal.tendsto_toReal hent).comp (heat_entropy_tendsto_nhdsGT ρ hρ)
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  obtain ⟨η, h1, h2, h3, h4⟩ := heatRegularization_regular ρ ht
  have hb := entropy_bound_of_minimizing_mixtures_aligned hd hmix η h2
  unfold EntropyBound at hb
  rw [h1] at hb
  exact hb


theorem pressure_two_d_eq_zero_aligned (hd : 0 < d) (hmix : SmoothMixtureInequality d) :
    pressure d (2 * (d : ℝ)) = 0 :=
  pressure_two_d_eq_zero_of_full hd (fun ρ hρ => entropy_bound_full_aligned hd hmix ρ hρ)


theorem potential_bound_aligned (hd : 0 < d) (hmix : SmoothMixtureInequality d) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  potential_bound_of_full hd (fun ρ hρ => entropy_bound_full_aligned hd hmix ρ hρ) u hu


/-- **Lemma 3.1 (`lem:collapse-conditional-reduction`), weakest-hypothesis form.**  From the
mixture inequality and the mixture strictness, restricted to the smooth strictly positive
mixtures, one gets the entropy bound for every finite-entropy density, equality only at the
uniform density, `P_d(2d) = 0`, the potential inequality and its equality case.  The dimension
restriction `d ≤ 10` of the manuscript is not used here (it enters only through the proofs of the
two hypotheses). -/
theorem lemma_3_1_smooth_aligned (hd : 0 < d) (hineq : SmoothMixtureInequality d)
    (hstrict : SmoothMixtureStrictness d) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → EntropyBound d ρ) ∧
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → EntropyEquality d ρ →
      ρ.value =ᵐ[torusMeasure d] (fun _ => 1)) ∧
    pressure d (2 * (d : ℝ)) = 0 ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) →
        ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c) := by
  have hfull := fun ρ (hρ : ProbabilityDensity.FiniteEntropy ρ) => entropy_bound_full_aligned hd hineq ρ hρ
  exact ⟨hfull, fun ρ hρ heq => entropy_equality_uniform hd hfull hstrict ρ hρ heq,
    pressure_two_d_eq_zero_aligned hd hineq, fun u hu => potential_bound_aligned hd hineq u hu,
    fun u hu heq => potential_equality_const hd hfull hstrict u hu heq⟩

/-- **Lemma 3.1 (`lem:collapse-conditional-reduction`).**  Fix `d ≥ 2`.  Suppose every
finite-entropy countable cosine-power mixture satisfies `Ent ρ ≥ d c_d ‖ρ‖²` and that this is strict
for every nonuniform such mixture.  Then `d c_d ‖ρ‖² ≤ Ent ρ` for all finite-entropy densities with
equality only for the uniform density, and the dual potential inequality holds with equality only
for constants.

The two hypotheses are exactly `MixtureInequality d` and `MixtureStrictness d`; they are not the
density theorem.  (For `d = 1` the strictness hypothesis is false because of the
Lebedev--Milin equality family, so no rigidity statement is exported to `d = 1`.) -/
theorem lemma_3_1_aligned (hd : 2 ≤ d) (hineq : MixtureInequality d) (hstrict : MixtureStrictness d) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → EntropyBound d ρ) ∧
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → EntropyEquality d ρ →
      ρ.value =ᵐ[torusMeasure d] (fun _ => 1)) ∧
    pressure d (2 * (d : ℝ)) = 0 ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) →
        ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c) :=
  lemma_3_1_smooth_aligned (by omega) hineq.toSmooth hstrict.toSmooth


#print axioms entropy_bound_of_minimizing_mixtures_aligned
#print axioms lemma_3_1_aligned

/-! ## Proposition 3.7 and Theorem 1.1 -/

/-- **Proposition 3.7 (`prop:equality`)**, route-aligned: same type as `Section3.prop_3_7_written`. -/
theorem prop_3_7_aligned (hd2 : 2 ≤ d) (hd10 : d ≤ 10) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      (EntropyEquality d ρ ↔ ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
        ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) := by
  obtain ⟨-, hdens, -, -, hpot⟩ :=
    lemma_3_1_aligned hd2 (mixtureInequality_printed hd2 hd10) (mixtureStrictness_printed hd2 hd10)
  exact ⟨fun ρ hρ => ⟨hdens ρ hρ, entropyEquality_of_uniform ρ⟩,
    fun u hu => ⟨hpot u hu, fun ⟨c, hc⟩ => potential_equality_of_const (by omega) u hu c hc⟩⟩

/-- **Theorem 1.1 (`thm:intro-low-dimensional`), `1 ≤ d ≤ 10`**, route-aligned: same type as
`Section3.theorem_1_1_written`. -/
theorem theorem_1_1_aligned (hd1 : 1 ≤ d) (hd10 : d ≤ 10) :
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal)) ∧
    (∀ ρ : ProbabilityDensity d, ExtendedBound d ρ) ∧
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) ∧
    (d = 1 →
      (∀ ρ : ProbabilityDensity 1, ρ.FiniteEntropy →
        (EntropyEquality 1 ρ ↔ ∃ a : ℂ, ‖a‖ < 1 ∧ ρ.value =ᵐ[torusMeasure 1]
          fun x => (1 - ‖a‖ ^ 2) / ‖fourier 1 (x 0) - a‖ ^ 2)) ∧
      (∀ u : Torus 1 → ℝ, InCriticalSobolev u →
        (logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
          ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ, u =ᵐ[torusMeasure 1]
            fun x => -2 * Real.log ‖1 - conj a * fourier 1 (x 0)‖ + c))) ∧
    (2 ≤ d →
      (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
        (EntropyEquality d ρ ↔ ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
      (∀ u : Torus d → ℝ, InCriticalSobolev u →
        (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
          ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c))) ∧
    coefficientDefect d (collapseCoefficient d) = 0 ∧
    (∀ β : ℝ, pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤) ∧
    VariationalCurves.globalTransition d = 2 * (d : ℝ) := by
  have hd0 : 0 < d := by omega
  have hfull : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → EntropyBound d ρ := by
    rcases Nat.eq_or_lt_of_le hd1 with h | h
    · subst h; exact fun ρ hρ => circle_entropy_bound ρ hρ
    · exact (lemma_3_1_aligned (by omega) (mixtureInequality_printed (by omega) hd10)
        (mixtureStrictness_printed (by omega) hd10)).1
  refine ⟨fun u hu => potential_bound_of_full hd0 hfull u hu,
    fun ρ => extendedBound_of_full hd0 hfull ρ, collapse_isLeast hd0 hfull, ?_, ?_,
    coefficientDefect_collapse_eq_zero_of_full hd0 hfull, pressure_formula hd0 hfull,
    globalTransition_eq hd0 hfull⟩
  · rintro rfl
    exact ⟨fun ρ hρ => circle_entropy_equality_iff ρ hρ,
      fun u hu => circle_potential_equality_iff u hu⟩
  · intro h2
    exact prop_3_7_aligned h2 hd10

#print axioms prop_3_7_aligned
#print axioms theorem_1_1_aligned

/-! ## The `Challenge` normalisation: `V2.Final.low_dim_*` -/

/-- If `c · (spectralEnergy ρ).toReal ≤ Ent ρ` for finite-entropy `ρ` (and `0 < d`), then
`c · spectralEnergy ρ ≤ extendedEntropy ρ` in `EReal`, with `Ent = ∞` allowed. -/
theorem ereal_le_extendedEntropy {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d) (c : ℝ)
    (h : ρ.FiniteEntropy → c * (spectralEnergy ρ).toReal ≤ entropy ρ) :
    (c : EReal) * (spectralEnergy ρ).toEReal ≤ extendedEntropy ρ := by
  by_cases hρ : ρ.FiniteEntropy
  · have hfin : spectralEnergy ρ ≠ ⊤ := finiteEntropy_spectralEnergy_ne_top hd ρ hρ
    rw [extendedEntropy_eq_torusEntropy, torusEntropy_density_eq_ofReal_entropy ρ hρ,
      EReal.coe_ennreal_ofReal, max_eq_left (entropy_nonneg ρ hρ),
      ← EReal.coe_ennreal_toReal hfin, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    exact h hρ
  · rw [extendedEntropy_eq_torusEntropy, torusEntropy_density_eq_top ρ hρ]
    exact le_top


/-- Equality in `eq:collapse-entropy-full` (manuscript normalization) is equality in the
`Challenge` normalization `(d/β_s(d)) · spectralEnergy ρ = Ent ρ`. -/
theorem entropyEquality_iff_challenge {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    EntropyEquality d ρ ↔
      (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
        (entropy ρ : EReal) := by
  have hfin : spectralEnergy ρ ≠ ⊤ := finiteEntropy_spectralEnergy_ne_top hd ρ hρ
  have key := kernelConstant_mul_negSobolevEnergy_toReal hd ρ
  have h1 : (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal =
      (d : ℝ) / spectralThreshold d * (spectralEnergy ρ).toReal := by
    rw [mul_assoc, key]; ring
  unfold EntropyEquality
  rw [← EReal.coe_ennreal_toReal hfin, ← EReal.coe_mul, EReal.coe_eq_coe_iff, h1,
    ← entropy_eq_toReal_torusEntropy ρ hρ]


section Low
variable (d : ℕ)

/-- **Theorem 1.1, (eq:intro-low-dual).**  Statement as in `Challenge.low_dim_entropy_inequality`. -/
theorem low_dim_entropy_inequality (hd : 1 ≤ d) (hd10 : d ≤ 10) (ρ : ProbabilityDensity d) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤
      extendedEntropy ρ := by
  have hd0 : 0 < d := hd
  refine ereal_le_extendedEntropy hd0 ρ _ fun hρ => ?_
  have hext := (theorem_1_1_aligned hd hd10).2.1 ρ
  unfold ExtendedBound at hext
  have hfin : spectralEnergy ρ ≠ ⊤ := finiteEntropy_spectralEnergy_ne_top hd0 ρ hρ
  have hN : negSobolevEnergy ρ.value ≠ ⊤ := (negSobolevEnergy_ne_top_iff ρ).2 hfin
  have hc : 0 < kernelConstant d := kernelConstant_pos hd0
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [torusEntropy_density_eq_ofReal_entropy ρ hρ, ← ENNReal.ofReal_toReal hN,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (entropy_nonneg ρ hρ)] at hext
  have key := kernelConstant_mul_negSobolevEnergy_toReal hd0 ρ
  have h1 : (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal =
      (d : ℝ) / spectralThreshold d * (spectralEnergy ρ).toReal := by
    rw [mul_assoc, key]; ring
  rw [← h1]
  exact hext

/-- **Theorem 1.1, (eq:intro-low-primal).**  Statement as in `Challenge.low_dim_beckner_onofri`. -/
theorem low_dim_beckner_onofri (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  (theorem_1_1_aligned hd hd10).1 u hu

/-- **Theorem 1.1, sharpness.**  Statement as in `Challenge.low_dim_coefficient_sharp`. -/
theorem low_dim_coefficient_sharp (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) :=
  (theorem_1_1_aligned hd hd10).2.2.1

/-- **Theorem 1.1, equality for `d = 1` (potentials).**  Statement as in
`Challenge.circle_beckner_onofri_eq_iff`. -/
theorem circle_beckner_onofri_eq_iff (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x => -2 * Real.log ‖1 - conj a * fourier 1 (x 0)‖ + c :=
  ((theorem_1_1_aligned (le_refl 1) (by norm_num)).2.2.2.1 rfl).2 u hu

/-- **Theorem 1.1, equality for `d = 1` (densities).**  Statement as in
`Challenge.circle_entropy_eq_iff`. -/
theorem circle_entropy_eq_iff (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    (((1 : ℝ) / spectralThreshold 1 : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
        (entropy ρ : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧
        ρ.value =ᵐ[torusMeasure 1] fun x => (1 - ‖a‖ ^ 2) / ‖fourier 1 (x 0) - a‖ ^ 2 := by
  have h := entropyEquality_iff_challenge (by norm_num : 0 < 1) ρ hρ
  rw [Nat.cast_one] at h
  rw [← h]
  exact ((theorem_1_1_aligned (le_refl 1) (by norm_num)).2.2.2.1 rfl).1 ρ hρ

/-- **Theorem 1.1, equality for `2 ≤ d ≤ 10` (densities).**  Statement as in
`Challenge.low_dim_entropy_eq_iff`. -/
theorem low_dim_entropy_eq_iff (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
        (entropy ρ : EReal) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1 := by
  rw [← entropyEquality_iff_challenge (by omega) ρ hρ]
  exact ((theorem_1_1_aligned (by omega) hd10).2.2.2.2.1 hd).1 ρ hρ

/-- **Theorem 1.1, equality for `2 ≤ d ≤ 10` (potentials).**  Statement as in
`Challenge.low_dim_beckner_onofri_eq_iff`. -/
theorem low_dim_beckner_onofri_eq_iff (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c :=
  ((theorem_1_1_aligned (by omega) hd10).2.2.2.2.1 hd).2 u hu

/-- **(eq:intro-low-coefficient-consequence).**  Statement as in `Challenge.low_dim_pressure_eq`. -/
theorem low_dim_pressure_eq (hd : 1 ≤ d) (hd10 : d ≤ 10) (β : ℝ) :
    pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤ :=
  (theorem_1_1_aligned hd hd10).2.2.2.2.2.2.1 β

/-- **(eq:intro-low-coefficient-consequence).**  Statement as in `Challenge.low_dim_defect_eq`.
`theorem_1_1_aligned` only gives `C_d(A_c(d)) = 0`; the formula for all `A` follows by antitonicity of
`C_d` and `0 ≤ C_d` (above `A_c`) and `HighDim.coefficientDefect_below_collapse` (below `A_c`),
the latter being the concentration lemma (Lemma 2.3), also used in `Section3.collapse_isLeast`. -/
theorem low_dim_defect_eq (hd : 1 ≤ d) (hd10 : d ≤ 10) (A : ℝ) :
    coefficientDefect d A = if collapseCoefficient d ≤ A then 0 else ⊤ := by
  have hd0 : 0 < d := hd
  split_ifs with h
  · refine le_antisymm ?_ (coefficientDefect_nonneg d A)
    calc coefficientDefect d A ≤ coefficientDefect d (collapseCoefficient d) :=
          coefficientDefect_antitone hd0 h
      _ = 0 := (theorem_1_1_aligned hd hd10).2.2.2.2.2.1
  · exact coefficientDefect_below_collapse hd0 (not_le.mp h)

/-- **(eq:intro-low-coefficient-consequence).**  Statement as in `Challenge.low_dim_globalTransition`. -/
theorem low_dim_globalTransition (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    VariationalCurves.globalTransition d = 2 * (d : ℝ) :=
  (theorem_1_1_aligned hd hd10).2.2.2.2.2.2.2

end Low


#print axioms entropyEquality_iff_challenge
#print axioms low_dim_entropy_inequality
#print axioms low_dim_beckner_onofri
#print axioms low_dim_coefficient_sharp
#print axioms circle_beckner_onofri_eq_iff
#print axioms circle_entropy_eq_iff
#print axioms low_dim_entropy_eq_iff
#print axioms low_dim_beckner_onofri_eq_iff
#print axioms low_dim_pressure_eq
#print axioms low_dim_defect_eq
#print axioms low_dim_globalTransition

end BecknerOnofri.V2.Reaudit.Mixtures
