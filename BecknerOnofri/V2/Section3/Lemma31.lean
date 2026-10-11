module

public import BecknerOnofri.V2.Section3.Defs
public import BecknerOnofri.V2.Reaudit.Attainment.Main

@[expose] public section

/-! # Lemma 3.1 (`lem:collapse-conditional-reduction`): the conditional reduction (G04)

Three exports, in the order of the proof, with the two mixture hypotheses kept as hypotheses:

* **E1** `smooth_entropy_bound` — from `SmoothMixtureInequality d` the entropy bound for every smooth
  strictly positive density (the proof by contradiction at a coupling `β < 2d`, via the existence
  of a minimizer (Prop 2.7), the minimizing mixture of Lemma 2.13 and the displayed chain
  `0 > Ent - β c_d/2 ‖ρ*‖² ≥ (2d-β) c_d/2 ‖ρ*‖² ≥ 0`);
* **E2** `entropy_bound_full`, `pressure_two_d_eq_zero`, `coefficientDefect_collapse_eq_zero`,
  `potential_bound` — from E1 and heat regularization, the bound for **all** finite-entropy
  densities, the value `P_d(2d) = 0` of the pressure, and the potential inequality;
* **E3** `entropy_equality_uniform` (and `potential_equality_const`) — only after E2: an equality
  density is a global extremizer at `β = 2d`; attained-endpoint Gibbs regularity (Cor 2.6, valid at
  `β = 2d`), the bounded coordinate rearrangement of Lemma 2.9 at `β = 2d`
  (`coordinate_rearranged_minimizer`), Proposition 2.12 (`cosine_representation`) and
  `SmoothMixtureStrictness`.

No old endpoint theorem is used.  The statement `lemma_3_1` collects the manuscript conclusions. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab BecknerOnofri.V2.Rearrangement

variable {d : ℕ}

/-! ## E1: the inequality for smooth densities -/

/-- The contradiction argument of E1, in fact valid for every finite-entropy density `ρ`
(the minimizer of Prop 2.7 is taken over all finite-entropy densities). -/
theorem entropy_bound_of_minimizing_mixtures (hd : 0 < d) (hmix : SmoothMixtureInequality d)
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
  obtain ⟨ρs, hρs⟩ := (Reaudit.Attainment.subcritical_attainment hd hβ hβd).2.1
  obtain ⟨η, u, -, hηmin, -, -, -, -, hsm, hηpos, -, -, -, -, -, -, -, hηmix, -, -⟩ :=
    PrescribedSelection.canonical_selection hd β hβ hβd ρs hρs
  have hle := hηmin.2 ρ hρ
  rw [pressureValue_le_iff_real hd β ρ η hρ hηmin.1] at hle
  have hbound := hmix η hηmin.1 ⟨hsm, hηpos, hηmix⟩
  unfold EntropyBound at hbound
  have hNη : 0 ≤ (negSobolevEnergy η.value).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * (d : ℝ) - β) (mul_nonneg hc.le hNη)]

/-- **E1.**  The entropy bound for every smooth strictly positive density. -/
theorem smooth_entropy_bound (hd : 0 < d) (hmix : SmoothMixtureInequality d)
    (ρ : ProbabilityDensity d) (hs : SmoothOnTorus ρ.value) (_hpos : ∀ x, 0 < ρ.value x) :
    EntropyBound d ρ :=
  entropy_bound_of_minimizing_mixtures hd hmix ρ (finiteEntropy_of_smooth ρ hs)

/-! ## E2: all finite-entropy densities, the pressure, the potential inequality -/

/-- **E2 (density inequality).**  Heat regularization: `ρ_t` is smooth and strictly positive, so
E1 applies to it; `t ↓ 0` with the entropy and energy limits of Lemma 2.1 (route difference: the
manuscript takes finite subsets of frequencies, monotone convergence and entropy contraction; here
the full convergence `Ent(ρ_t) → Ent(ρ)`, `c_d‖ρ_t‖² → c_d‖ρ‖²` of Section 2 is used instead). -/
theorem entropy_bound_full (hd : 0 < d) (hmix : SmoothMixtureInequality d)
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
  have hb := entropy_bound_of_minimizing_mixtures hd hmix η h2
  unfold EntropyBound at hb
  rw [h1] at hb
  exact hb

/-- **E2 (pressure).**  `P_d(2d) = 0` as soon as the full bound holds: the bound gives `≤ 0`, the
uniform competitor gives `≥ 0`. -/
theorem pressure_two_d_eq_zero_of_full (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ) :
    pressure d (2 * (d : ℝ)) = 0 := by
  apply le_antisymm
  · refine iSup_le fun ρ => iSup_le fun hρ => ?_
    exact (entropyBound_iff hd ρ hρ).1 (hfull ρ hρ)
  · exact pressure_nonneg d _

theorem pressure_two_d_eq_zero (hd : 0 < d) (hmix : SmoothMixtureInequality d) :
    pressure d (2 * (d : ℝ)) = 0 :=
  pressure_two_d_eq_zero_of_full hd (fun ρ hρ => entropy_bound_full hd hmix ρ hρ)

/-- **E2 (duality).**  `C_d(A_c(d)) = P_d(2d) = 0`. -/
theorem coefficientDefect_collapse_eq_zero_of_full (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ) :
    coefficientDefect d (collapseCoefficient d) = 0 := by
  have hc := kernelConstant_pos hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 < collapseCoefficient d := by
    rw [collapseCoefficient_eq hd]; positivity
  rw [coefficient_pressure_duality hd hA]
  have : (2 * collapseCoefficient d * kernelConstant d)⁻¹ = 2 * (d : ℝ) := by
    rw [collapseCoefficient_eq hd]; field_simp; norm_num
  rw [this]
  exact pressure_two_d_eq_zero_of_full hd hfull

theorem coefficientDefect_collapse_eq_zero (hd : 0 < d) (hmix : SmoothMixtureInequality d) :
    coefficientDefect d (collapseCoefficient d) = 0 :=
  coefficientDefect_collapse_eq_zero_of_full hd (fun ρ hρ => entropy_bound_full hd hmix ρ hρ)

/-! ## E3: equality forces the uniform density (only after E2) -/

/-- Once the full bound holds, an equality density is a global extremizer at `β = 2d`. -/
theorem isGlobalMinimizer_of_equality (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) (heq : EntropyEquality d ρ) :
    IsGlobalMinimizer (2 * (d : ℝ)) ρ := by
  refine ⟨hρ, fun σ hσ => ?_⟩
  rw [pressureValue_two_d hd σ hσ, pressureValue_two_d hd ρ hρ, EReal.coe_le_coe_iff]
  have h1 := hfull σ hσ
  unfold EntropyBound at h1
  unfold EntropyEquality at heq
  linarith

/-- A density that agrees a.e. with a smooth strictly positive function `q` is a density with
value `q`. -/
def densityOfSmooth (ρ : ProbabilityDensity d) {q : Torus d → ℝ} (hq : ρ.value =ᵐ[torusMeasure d] q)
    (hqs : SmoothOnTorus q) (hqpos : ∀ x, 0 < q x) : ProbabilityDensity d where
  value := q
  nonneg := Filter.Eventually.of_forall fun x => (hqpos x).le
  integrable := by
    obtain ⟨K, hK⟩ := hqs.exists_lipschitz
    exact hK.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  mass := by rw [← integral_congr_ae hq]; exact ρ.mass

/-- **E3, smooth case.**  The coordinate rearrangement at `β = 2d`, the cosine representation and
the strictness hypothesis. -/
theorem entropy_equality_uniform_smooth (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ)
    (hstrict : SmoothMixtureStrictness d)
    (ρ : ProbabilityDensity d) (hs : SmoothOnTorus ρ.value) (heq : EntropyEquality d ρ) :
    ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  by_contra hnon
  have hρ := finiteEntropy_of_smooth ρ hs
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hmin := isGlobalMinimizer_of_equality hd hfull ρ hρ heq
  obtain ⟨η, u, -, hηmin, -, hee, -, hent, -, -, hgu, hηs, hηpos, hus, hm, -, -, heuler, -, hstu⟩ :=
    coordinate_rearranged_minimizer hd (β := 2 * (d : ℝ)) (by positivity) ρ hmin hs
  obtain ⟨U, -, -, -, hηmix⟩ := GeneralEulerBridge.cosine_representation hd (2 * (d : ℝ))
    (by positivity) u η hus hm hstu hgu heuler
  -- same energy and entropy
  have hkey : kernelConstant d * (negSobolevEnergy η.value).toReal =
      kernelConstant d * (negSobolevEnergy ρ.value).toReal := by
    rw [kernelConstant_mul_negSobolevEnergy_toReal hd, kernelConstant_mul_negSobolevEnergy_toReal hd,
      hee]
  have hηeq : EntropyEquality d η := by
    unfold EntropyEquality at heq ⊢
    rw [hent, ← heq, mul_assoc, hkey, ← mul_assoc]
  have hSpos : 0 < (torusEntropy ρ.value).toReal := (pos_entropy_iff ρ hρ).2 hnon
  have hηnon : ¬ η.value =ᵐ[torusMeasure d] (fun _ => 1) :=
    (pos_entropy_iff η hηmin.1).1 (by rw [hent]; exact hSpos)
  have hst := hstrict η hηmin.1 ⟨hηs, hηpos, hηmix⟩ hηnon
  unfold EntropyStrict at hst
  unfold EntropyEquality at hηeq
  linarith

/-- **E3 (density equality case).**  Every finite-entropy density with equality in the entropy bound
is the uniform density (a.e.). -/
theorem entropy_equality_uniform (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ)
    (hstrict : SmoothMixtureStrictness d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) (heq : EntropyEquality d ρ) :
    ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hmin := isGlobalMinimizer_of_equality hd hfull ρ hρ heq
  obtain ⟨q, hq, hqs, hqpos⟩ :=
    (Reaudit.Attainment.attained_extremizers_regular hd (by positivity : 0 < 2 * (d : ℝ))
      (Or.inr ⟨ρ, hmin⟩)).2.2.1 ρ hmin
  let ρq := densityOfSmooth ρ hq hqs hqpos
  have hae : ρ.value =ᵐ[torusMeasure d] ρq.value := hq
  have h := entropy_equality_uniform_smooth hd hfull hstrict ρq hqs (by
    unfold EntropyEquality at heq ⊢
    rw [← negSobolevEnergy_congr_ae hae, ← torusEntropy_congr_ae hae]
    exact heq)
  exact hae.trans h

/-! ## Centering and the potential statements -/

theorem fourierCoeff_const_nonzero (c : ℝ) {k : Frequency d} (hk : k ≠ 0) :
    BecknerOnofri.HighDim.fourierCoeff (fun _ : Torus d => c) k = 0 := by
  have h1 := fourierCoeff_one_nonzero (d := d) k hk
  unfold BecknerOnofri.HighDim.fourierCoeff at h1 ⊢
  have : (fun x : Torus d => UnitAddTorus.mFourier (-k) x * ((c : ℝ) : ℂ)) =
      fun x => (UnitAddTorus.mFourier (-k) x * (((1 : ℝ)) : ℂ)) * (c : ℂ) := by
    funext x; simp
  rw [this, integral_mul_const, h1, zero_mul]

theorem fourierCoeff_centered (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d))
    {k : Frequency d} (hk : k ≠ 0) :
    BecknerOnofri.HighDim.fourierCoeff (centered u) k = BecknerOnofri.HighDim.fourierCoeff u k := by
  have hc : centered u = u - fun _ => ∫ y, u y ∂torusMeasure d := rfl
  rw [hc, FullHessianDecomposition.fourierCoeff_sub u _ hu (memLp_const _) k,
    fourierCoeff_const_nonzero _ hk, sub_zero]

theorem centered_inCriticalSobolev (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    InCriticalSobolev (centered u) := by
  refine ⟨hu.1.sub (memLp_const _), ?_⟩
  have : potentialTerm (centered u) = potentialTerm u := by
    funext k
    unfold potentialTerm
    rw [fourierCoeff_centered u hu.1 k.property]
  rw [this]; exact hu.2

theorem potentialEnergy_centered (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    potentialEnergy (centered u) = potentialEnergy u := by
  unfold potentialEnergy potentialTerm
  refine tsum_congr fun k => ?_
  rw [fourierCoeff_centered u hu k.property]

theorem centered_meanZero (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    MeanZero (centered u) :=
  centered_integral u (hu.integrable (by norm_num))

/-- **E2 (potential inequality).**  `log ∫ e^{u-ū} ≤ A_c(d) ‖u‖²_{Ḣ^{d/2}}` (`eq:intro-low-primal`),
with the integrability of the exponential, from the full density bound. -/
theorem potential_bound_of_full (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  refine ⟨exp_centered_integrable hd u hu, ?_⟩
  have h0 := coefficientDefect_collapse_eq_zero_of_full hd hfull
  have h : logPartition u - ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ≤ 0 := by
    rw [← h0]
    exact le_iSup₂ (f := fun (u : Torus d → ℝ) (_ : InCriticalSobolev u) =>
      logPartition u - ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal)) u hu
  rw [logPartition_eq_log_integral hd u hu] at h ⊢
  have h' : Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤
      collapseCoefficient d * potentialEnergy u := by
    rw [← EReal.coe_sub, ← EReal.coe_zero, EReal.coe_le_coe_iff] at h
    linarith
  exact_mod_cast h'

theorem potential_bound (hd : 0 < d) (hmix : SmoothMixtureInequality d) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  potential_bound_of_full hd (fun ρ hρ => entropy_bound_full hd hmix ρ hρ) u hu

/-- **E3 (potential equality case).**  Equality in the potential inequality forces `u` to be an a.e.
constant.  Route: centering, the primal gap identity `eq:section2-primal-gap-identity` at
`β = 2d`, the density bound (E2) and the density equality case (E3). -/
theorem potential_equality_const (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ)
    (hstrict : SmoothMixtureStrictness d) (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (heq : logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal)) :
    ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c := by
  have hc := kernelConstant_pos hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 < collapseCoefficient d := by rw [collapseCoefficient_eq hd]; positivity
  set v := centered u with hvdef
  have hv : InCriticalSobolev v := centered_inCriticalSobolev u hu
  have hm : MeanZero v := centered_meanZero u hu.1
  have hEv : potentialEnergy v = potentialEnergy u := potentialEnergy_centered u hu.1
  have hreal : Real.log (∫ x, Real.exp (v x) ∂torusMeasure d) =
      collapseCoefficient d * potentialEnergy v := by
    rw [logPartition_eq_log_integral hd u hu] at heq
    rw [hEv]
    exact_mod_cast heq
  obtain ⟨-, hgap⟩ := primal_gap_manuscript hd hA v hv hm
  rw [← potentialEnergy_eq_toReal_sobolevEnergyPos hv, hreal] at hgap
  have hβ : Gap.coefficient d (collapseCoefficient d) * kernelConstant d / 2 = d * kernelConstant d := by
    rw [gapCoefficient_eq hd hA, collapseCoefficient_eq hd]
    field_simp
    norm_num
  rw [hβ] at hgap
  set σ := normalizedGibbsDensity hd v hv hm with hσ
  have hσf : σ.FiniteEntropy := normalizedGibbsDensity_finiteEntropy hd v hv hm
  have hb := hfull σ hσf
  unfold EntropyBound at hb
  have hW : 0 ≤ (sobolevEnergyPos (v - Gap.densityPotential (Gap.coefficient d
      (collapseCoefficient d)) (normalizedGibbs v))).toReal := ENNReal.toReal_nonneg
  have hb' : (d : ℝ) * kernelConstant d * (negSobolevEnergy (normalizedGibbs v)).toReal ≤
      (torusEntropy (normalizedGibbs v)).toReal := hb
  have hB : (d : ℝ) * kernelConstant d * (negSobolevEnergy (normalizedGibbs v)).toReal -
      (torusEntropy (normalizedGibbs v)).toReal = collapseCoefficient d *
        (sobolevEnergyPos (v - Gap.densityPotential (Gap.coefficient d
          (collapseCoefficient d)) (normalizedGibbs v))).toReal := by linarith [hgap]
  have hAW := mul_nonneg hA.le hW
  have hEq : EntropyEquality d σ := by
    change (d : ℝ) * kernelConstant d * (negSobolevEnergy (normalizedGibbs v)).toReal =
      (torusEntropy (normalizedGibbs v)).toReal
    linarith
  have h1 := entropy_equality_uniform hd hfull hstrict σ hσf hEq
  refine ⟨Real.log (∫ y, Real.exp (v y) ∂torusMeasure d) + ∫ y, u y ∂torusMeasure d, ?_⟩
  filter_upwards [h1] with x hx
  change normalizedGibbs v x = 1 at hx
  unfold normalizedGibbs at hx
  have hZ : 0 < ∫ y, Real.exp (v y) ∂torusMeasure d := partition_pos hd v hv hm
  have hexp : Real.exp (v x) = ∫ y, Real.exp (v y) ∂torusMeasure d := by
    field_simp at hx; exact hx
  have hvx : v x = Real.log (∫ y, Real.exp (v y) ∂torusMeasure d) := by
    rw [← hexp, Real.log_exp]
  have : u x = v x + ∫ y, u y ∂torusMeasure d := by
    simp only [hvdef, centered]; ring
  rw [this, hvx]

/-! ## Lemma 3.1 -/

/-- **Lemma 3.1 (`lem:collapse-conditional-reduction`), weakest-hypothesis form.**  From the
mixture inequality and the mixture strictness, restricted to the smooth strictly positive
mixtures, one gets the entropy bound for every finite-entropy density, equality only at the
uniform density, `P_d(2d) = 0`, the potential inequality and its equality case.  The dimension
restriction `d ≤ 10` of the manuscript is not used here (it enters only through the proofs of the
two hypotheses). -/
theorem lemma_3_1_smooth (hd : 0 < d) (hineq : SmoothMixtureInequality d)
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
  have hfull := fun ρ (hρ : ProbabilityDensity.FiniteEntropy ρ) => entropy_bound_full hd hineq ρ hρ
  exact ⟨hfull, fun ρ hρ heq => entropy_equality_uniform hd hfull hstrict ρ hρ heq,
    pressure_two_d_eq_zero hd hineq, fun u hu => potential_bound hd hineq u hu,
    fun u hu heq => potential_equality_const hd hfull hstrict u hu heq⟩

/-- **Lemma 3.1 (`lem:collapse-conditional-reduction`).**  Fix `d ≥ 2`.  Suppose every
finite-entropy countable cosine-power mixture satisfies `Ent ρ ≥ d c_d ‖ρ‖²` and that this is strict
for every nonuniform such mixture.  Then `d c_d ‖ρ‖² ≤ Ent ρ` for all finite-entropy densities with
equality only for the uniform density, and the dual potential inequality holds with equality only
for constants.

The two hypotheses are exactly `MixtureInequality d` and `MixtureStrictness d`; they are not the
density theorem.  (For `d = 1` the strictness hypothesis is false because of the
Lebedev--Milin equality family, so no rigidity statement is exported to `d = 1`.) -/
theorem lemma_3_1 (hd : 2 ≤ d) (hineq : MixtureInequality d) (hstrict : MixtureStrictness d) :
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
  lemma_3_1_smooth (by omega) hineq.toSmooth hstrict.toSmooth

#print axioms smooth_entropy_bound
#print axioms entropy_bound_full
#print axioms pressure_two_d_eq_zero
#print axioms coefficientDefect_collapse_eq_zero
#print axioms entropy_equality_uniform
#print axioms potential_bound
#print axioms potential_equality_const
#print axioms lemma_3_1_smooth
#print axioms lemma_3_1

end BecknerOnofri.V2.Section3
