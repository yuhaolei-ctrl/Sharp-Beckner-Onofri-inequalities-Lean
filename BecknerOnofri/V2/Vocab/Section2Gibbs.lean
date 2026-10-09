module

public import BecknerOnofri.V2.Vocab.Section2Bridge
public import BecknerOnofri.PaperGapIdentities
public import BecknerOnofri.FullHessianDecomposition

@[expose] public section

/-! # Lemma 2.5 interface: Gibbs densities, `Ḣ^{d/2}` seminorm, relative entropy (G02)

* `sobolevEnergyPos u = Σ_{k≠0} (2π|k|)^{2·(d/2)} |û(k)|²` is `‖u‖²_{Ḣ^{d/2}}` in `ℝ≥0∞`
  (`eq:intro-primal-energy` at `s = d/2`); for `u ∈ H^{d/2}` the repository's `potentialEnergy u`
  is its real value (`potentialEnergy_eq_toReal_sobolevEnergyPos`).
* `normalizedGibbsDensity`: for `u ∈ H^{d/2}` of mean zero, `normalizedGibbs u = e^u / ∫ e^u` is a
  `ProbabilityDensity` of finite entropy, with positive values.
* `relativeEntropy_eq_toReal_measureEntropy`: for a positive density `σ`,
  `Gap.relativeEntropy ρ σ = (H_r(ρ μ | σ μ)).toReal` with the homogeneous KL entropy `measureEntropy`
  (the junk value `0` of the Bochner integral matches `(⊤).toReal = 0`).
* `primal_gap_manuscript`, `dual_gap_manuscript`: `eq:section2-primal-gap-identity` and
  `eq:section2-dual-gap-identity` of Lemma 2.5 in the manuscript normalization. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Vocab
open BecknerOnofri.HighDim

section Seminorm
variable {d : ℕ}

/-- `‖u‖²_{Ḣ^{d/2}} = Σ_{k≠0} (2π|k|)^{2 s} |û(k)|²` at `s = d/2`, as an extended sum. -/
def sobolevEnergyPos (u : Torus d → ℝ) : ℝ≥0∞ :=
  ∑' k : NonzeroFrequency d,
    ENNReal.ofReal ((2 * Real.pi * frequencyLength k.val) ^ (2 * ((d : ℝ) / 2)) *
      ‖fourierCoeff u k.val‖ ^ 2)

/-- The real power `(2π|k|)^{2·(d/2)}` is the repository's natural power `(2π|k|)^d`. -/
theorem sobolevEnergyPos_eq {u : Torus d → ℝ} :
    sobolevEnergyPos u = ∑' k : NonzeroFrequency d, ENNReal.ofReal (potentialTerm u k) := by
  unfold sobolevEnergyPos
  refine tsum_congr fun k => ?_
  unfold potentialTerm
  congr 2
  rw [show 2 * ((d : ℝ) / 2) = (d : ℝ) by ring, Real.rpow_natCast]

theorem potentialTerm_nonneg (u : Torus d → ℝ) (k : NonzeroFrequency d) :
    0 ≤ potentialTerm u k := by
  unfold potentialTerm frequencyLength
  positivity

/-- `InCriticalSobolev` is `L²` plus finiteness of `‖u‖²_{Ḣ^{d/2}}`. -/
theorem inCriticalSobolev_iff {u : Torus d → ℝ} :
    InCriticalSobolev u ↔ MemLp u 2 (torusMeasure d) ∧ sobolevEnergyPos u ≠ ∞ := by
  unfold InCriticalSobolev
  rw [sobolevEnergyPos_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg (potentialTerm_nonneg u) h]
    exact ENNReal.ofReal_ne_top
  · intro h
    have := ENNReal.summable_toReal h
    refine this.congr fun k => ?_
    exact ENNReal.toReal_ofReal (potentialTerm_nonneg u k)

/-- For `u ∈ H^{d/2}`, the repository's `potentialEnergy u` is the real value of the manuscript's
squared seminorm `‖u‖²_{Ḣ^{d/2}}`. -/
theorem potentialEnergy_eq_toReal_sobolevEnergyPos {u : Torus d → ℝ} (hu : InCriticalSobolev u) :
    potentialEnergy u = (sobolevEnergyPos u).toReal := by
  rw [sobolevEnergyPos_eq, ← ENNReal.ofReal_tsum_of_nonneg (potentialTerm_nonneg u) hu.2,
    ENNReal.toReal_ofReal (tsum_nonneg (potentialTerm_nonneg u))]
  rfl

theorem ofReal_potentialEnergy_eq {u : Torus d → ℝ} (hu : InCriticalSobolev u) :
    ENNReal.ofReal (potentialEnergy u) = sobolevEnergyPos u := by
  rw [sobolevEnergyPos_eq]
  exact ENNReal.ofReal_tsum_of_nonneg (potentialTerm_nonneg u) hu.2

theorem potentialEnergy_nonneg' (u : Torus d → ℝ) : 0 ≤ potentialEnergy u :=
  tsum_nonneg (potentialTerm_nonneg u)

end Seminorm

section GibbsDensity
variable {d : ℕ}

section Existence
open Legacy.BecknerOnofri TorusSobolev SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual
open RawAttainment

/-- Copy of the first half of `Gap.primal_gap`: the Gibbs density of a mean-zero `u ∈ H^{d/2}`
exists as a finite-entropy probability density. -/
theorem exists_gibbs_density (hd : 0 < d) (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (hm : MeanZero u) :
    ∃ r : ProbabilityDensity d, r.value =ᵐ[torusMeasure d] normalizedGibbs u ∧ r.FiniteEntropy := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) hσ
  have hR := GenericAttainment.rough_bound hd (by positivity : 0 < endpointConstant d / 2)
    (by linarith : endpointConstant d / 2 < endpointConstant d)
  let U := Bridge.potentialLp u hu.1
  have hU : Admissible U := by
    refine ⟨Bridge.potentialLp_real u hu.1, ?_, Bridge.potentialLp_summable hd u hu⟩
    rw [SobolevCentering.fourier_zero]
    calc
      _ = ∫ x, (u x : ℂ) ∂torusMeasure d := integral_congr_ae (Bridge.potentialLp_ae u hu.1)
      _ = 0 := by
        rw [integral_complex_ofReal]
        exact congrArg Complex.ofReal hm
  have hUu : realValue U =ᵐ[torusMeasure d] u := by
    filter_upwards [Bridge.potentialLp_ae u hu.1] with x hx
    exact congrArg Complex.re hx
  refine ⟨Bridge.rawDensity (gibbsDensity hR hU), ?_, gibbsDensity_finiteEntropy hR hU⟩
  exact Gap.gibbs_congr hUu

end Existence

/-- The four properties making `normalizedGibbs u` a finite-entropy probability density. -/
theorem normalizedGibbs_facts (hd : 0 < d) (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (hm : MeanZero u) :
    (∀ᵐ x ∂torusMeasure d, 0 ≤ normalizedGibbs u x) ∧ Integrable (normalizedGibbs u) (torusMeasure d) ∧
      (∫ x, normalizedGibbs u x ∂torusMeasure d) = 1 ∧
      Integrable (fun x => normalizedGibbs u x * Real.log (normalizedGibbs u x)) (torusMeasure d) := by
  obtain ⟨r, hr, hf⟩ := exists_gibbs_density hd u hu hm
  refine ⟨?_, r.integrable.congr hr, ?_, ?_⟩
  · filter_upwards [r.nonneg, hr] with x h1 h2
    rwa [← h2]
  · rw [← integral_congr_ae hr]
    exact r.mass
  · refine hf.congr ?_
    filter_upwards [hr] with x hx
    rw [hx]

/-- For `u ∈ H^{d/2}` of mean zero, `normalizedGibbs u` as a `ProbabilityDensity`. -/
def normalizedGibbsDensity (hd : 0 < d) (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (hm : MeanZero u) : ProbabilityDensity d where
  value := normalizedGibbs u
  nonneg := (normalizedGibbs_facts hd u hu hm).1
  integrable := (normalizedGibbs_facts hd u hu hm).2.1
  mass := (normalizedGibbs_facts hd u hu hm).2.2.1

theorem normalizedGibbsDensity_value (hd : 0 < d) (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (hm : MeanZero u) : (normalizedGibbsDensity hd u hu hm).value = normalizedGibbs u := rfl

/-- `FiniteEntropy (normalizedGibbs u)` for `u ∈ H^{d/2}` of mean zero. -/
theorem normalizedGibbsDensity_finiteEntropy (hd : 0 < d) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) (hm : MeanZero u) :
    (normalizedGibbsDensity hd u hu hm).FiniteEntropy :=
  (normalizedGibbs_facts hd u hu hm).2.2.2

/-- The partition function `∫ e^u` of a mean-zero `u ∈ H^{d/2}` is positive. -/
theorem partition_pos (hd : 0 < d) (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (hm : MeanZero u) : 0 < ∫ x, Real.exp (u x) ∂torusMeasure d := by
  have hZ : 0 ≤ ∫ x, Real.exp (u x) ∂torusMeasure d :=
    integral_nonneg fun x => (Real.exp_pos _).le
  rcases hZ.eq_or_lt with h | h
  · exfalso
    have hmass := (normalizedGibbsDensity hd u hu hm).mass
    change ∫ x, normalizedGibbs u x ∂torusMeasure d = 1 at hmass
    unfold normalizedGibbs at hmass
    rw [← h] at hmass
    simp at hmass
  · exact h

/-- The Gibbs density is strictly positive everywhere. -/
theorem normalizedGibbs_pos (hd : 0 < d) (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (hm : MeanZero u) (x : Torus d) : 0 < normalizedGibbs u x :=
  div_pos (Real.exp_pos _) (partition_pos hd u hu hm)

end GibbsDensity

section RelativeEntropy
variable {d : ℕ} (ρ σ : ProbabilityDensity d)

lemma ofReal_density_lt_top : ∀ᵐ x ∂torusMeasure d, ENNReal.ofReal (σ.value x) < ∞ :=
  Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

lemma aemeasurable_ofReal_density : AEMeasurable (fun x => ENNReal.ofReal (σ.value x))
    (torusMeasure d) :=
  σ.integrable.aemeasurable.ennreal_ofReal

/-- Integral against `σ μ` is the `σ`-weighted integral against `μ`. -/
lemma integral_densityMeasure (g : Torus d → ℝ) :
    ∫ x, g x ∂densityMeasure σ = ∫ x, σ.value x * g x ∂torusMeasure d := by
  unfold densityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ (aemeasurable_ofReal_density σ)
    (ofReal_density_lt_top σ)]
  refine integral_congr_ae ?_
  filter_upwards [σ.nonneg] with x hx
  simp [ENNReal.toReal_ofReal hx]

variable {ρ σ}

lemma density_eq_ratio_withDensity (hσ : ∀ x, 0 < σ.value x) :
    densityMeasure ρ =
      (densityMeasure σ).withDensity (fun x => ENNReal.ofReal (ρ.value x / σ.value x)) := by
  unfold densityMeasure
  have hg : AEMeasurable (fun x => ENNReal.ofReal (ρ.value x / σ.value x)) (torusMeasure d) :=
    (ρ.integrable.aemeasurable.div σ.integrable.aemeasurable).ennreal_ofReal
  rw [← withDensity_mul₀ (aemeasurable_ofReal_density σ) hg]
  refine withDensity_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (hσ x).le]
  congr 1
  have := (hσ x).ne'
  field_simp

lemma ratio_domain (hσ : ∀ x, 0 < σ.value x) :
    FiniteMassDomain (densityMeasure σ) (fun x => ρ.value x / σ.value x) := by
  refine ⟨?_, ?_⟩
  · refine (withDensity_absolutelyContinuous (torusMeasure d) _).ae_le ?_
    filter_upwards [ρ.nonneg] with x hx
    exact div_nonneg hx (hσ x).le
  · unfold densityMeasure
    rw [integrable_withDensity_iff_integrable_smul₀' (aemeasurable_ofReal_density σ)
      (ofReal_density_lt_top σ)]
    refine ρ.integrable.congr ?_
    filter_upwards [σ.nonneg] with x hx
    have := (hσ x).ne'
    simp [ENNReal.toReal_ofReal hx]
    field_simp

lemma weighted_ratio_log (hσ : ∀ x, 0 < σ.value x) (x : Torus d) :
    σ.value x * ((ρ.value x / σ.value x) * Real.log (ρ.value x / σ.value x)) =
      ρ.value x * Real.log (ρ.value x / σ.value x) := by
  have := (hσ x).ne'
  field_simp

lemma integrable_ratio_iff (hσ : ∀ x, 0 < σ.value x) :
    Integrable (fun x => (ρ.value x / σ.value x) * Real.log (ρ.value x / σ.value x))
        (densityMeasure σ) ↔
      Integrable (fun x => ρ.value x * Real.log (ρ.value x / σ.value x)) (torusMeasure d) := by
  unfold densityMeasure
  rw [integrable_withDensity_iff_integrable_smul₀' (aemeasurable_ofReal_density σ)
    (ofReal_density_lt_top σ)]
  refine integrable_congr ?_
  filter_upwards [σ.nonneg] with x hx
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hx]
  exact weighted_ratio_log hσ x

lemma integral_ratio_log (hσ : ∀ x, 0 < σ.value x) :
    ∫ x, (ρ.value x / σ.value x) * Real.log (ρ.value x / σ.value x) ∂densityMeasure σ =
      ∫ x, ρ.value x * Real.log (ρ.value x / σ.value x) ∂torusMeasure d := by
  rw [integral_densityMeasure]
  exact integral_congr_ae (Eventually.of_forall fun x => weighted_ratio_log hσ x)

lemma integral_ratio (hσ : ∀ x, 0 < σ.value x) :
    ∫ x, ρ.value x / σ.value x ∂densityMeasure σ = 1 := by
  rw [integral_densityMeasure]
  have : (fun x => σ.value x * (ρ.value x / σ.value x)) = ρ.value := by
    funext x
    have := (hσ x).ne'
    field_simp
  rw [this]
  exact ρ.mass

/-- `H_r(ρ μ | σ μ) = Ent_{σμ}(ρ/σ)` (homogeneous entropy against the measure `σ μ`). -/
theorem measureEntropy_density_eq (hσ : ∀ x, 0 < σ.value x) :
    measureEntropy (densityMeasure ρ) (densityMeasure σ) =
      homEntropy (densityMeasure σ) (fun x => ρ.value x / σ.value x) := by
  rw [density_eq_ratio_withDensity (ρ := ρ) hσ]
  exact measureEntropy_withDensity (ratio_domain hσ)

/-- The relative entropy `H_r(ρ|σ) = ∫ ρ log(ρ/σ)` is `+∞` exactly when the integrand is not
integrable. -/
theorem measureEntropy_density_eq_top_iff (hσ : ∀ x, 0 < σ.value x) :
    measureEntropy (densityMeasure ρ) (densityMeasure σ) = ∞ ↔
      ¬ Integrable (fun x => ρ.value x * Real.log (ρ.value x / σ.value x)) (torusMeasure d) := by
  rw [measureEntropy_density_eq hσ, ← integrable_ratio_iff hσ,
    integrable_mul_log_iff (ratio_domain hσ)]
  tauto

/-- When `ρ log(ρ/σ)` is integrable, the relative entropy is `ofReal (Gap.relativeEntropy ρ σ)`,
and it is nonnegative. -/
theorem relativeEntropy_nonneg_of_integrable (hσ : ∀ x, 0 < σ.value x)
    (h : Integrable (fun x => ρ.value x * Real.log (ρ.value x / σ.value x)) (torusMeasure d)) :
    0 ≤ Gap.relativeEntropy ρ.value σ.value := by
  have hint := (integrable_ratio_iff hσ).2 h
  have hf : Integrable (fun x => ρ.value x / σ.value x) (densityMeasure σ) :=
    (ratio_domain hσ).integrable
  have h0 : 0 ≤ ∫ x, ((ρ.value x / σ.value x) * Real.log (ρ.value x / σ.value x) -
      ρ.value x / σ.value x + 1) ∂densityMeasure σ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [(ratio_domain hσ).nonneg] with x hx
    have := entropyIntegrand_nonneg (m := 1) one_pos hx
    simpa [entropyIntegrand] using this
  have hI1 : Integrable (fun x => (ρ.value x / σ.value x) * Real.log (ρ.value x / σ.value x) -
      ρ.value x / σ.value x) (densityMeasure σ) := hint.sub hf
  have e : ∫ x, ((ρ.value x / σ.value x) * Real.log (ρ.value x / σ.value x) -
      ρ.value x / σ.value x + 1) ∂densityMeasure σ =
      (∫ x, (ρ.value x / σ.value x) * Real.log (ρ.value x / σ.value x) ∂densityMeasure σ) -
        (∫ x, ρ.value x / σ.value x ∂densityMeasure σ) + 1 := by
    rw [integral_add hI1 (integrable_const 1), integral_sub hint hf]
    simp
  rw [e, integral_ratio hσ, integral_ratio_log hσ] at h0
  unfold Gap.relativeEntropy
  simpa using h0

theorem measureEntropy_density_eq_ofReal (hσ : ∀ x, 0 < σ.value x)
    (h : Integrable (fun x => ρ.value x * Real.log (ρ.value x / σ.value x)) (torusMeasure d)) :
    measureEntropy (densityMeasure ρ) (densityMeasure σ) =
      ENNReal.ofReal (Gap.relativeEntropy ρ.value σ.value) := by
  rw [measureEntropy_density_eq hσ]
  have hint := (integrable_ratio_iff hσ).2 h
  rw [homEntropy_eq_ofReal (ratio_domain hσ) hint, integral_ratio hσ, Real.log_one, mul_zero,
    sub_zero, integral_ratio_log hσ]
  rfl

/-- **Relative entropy bridge.**  For a positive density `σ`, the repository's real relative
entropy `∫ ρ log(ρ/σ)` is the real part of the extended `H_r(ρ|σ) = Ent_σ(ρ/σ)` (`measureEntropy`);
the two junk values (`0` for a non-integrable Bochner integral, `(⊤).toReal = 0`) agree. -/
theorem relativeEntropy_eq_toReal_measureEntropy (hσ : ∀ x, 0 < σ.value x) :
    Gap.relativeEntropy ρ.value σ.value =
      (measureEntropy (densityMeasure ρ) (densityMeasure σ)).toReal := by
  by_cases h : Integrable (fun x => ρ.value x * Real.log (ρ.value x / σ.value x)) (torusMeasure d)
  · rw [measureEntropy_density_eq_ofReal hσ h,
      ENNReal.toReal_ofReal (relativeEntropy_nonneg_of_integrable hσ h)]
  · rw [(measureEntropy_density_eq_top_iff hσ).2 h]
    simp only [ENNReal.toReal_top]
    exact integral_undef h

end RelativeEntropy

section Lemma25
open Legacy.BecknerOnofri TorusSobolev SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual
open RawAttainment
variable {d : ℕ}

/-- The relative entropy integrand of the dual gap is integrable: `H_r(ρ|σ_ρ) < ∞`. -/
theorem dual_gap_relativeEntropy_integrable (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    Integrable (fun x => ρ.value x * Real.log (ρ.value x /
      normalizedGibbs (Gap.densityPotential β ρ.value) x)) (torusMeasure d) := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hA : 0 < spectralThreshold d / (2 * β) := by positivity
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) hσ
  have hR := GenericAttainment.rough_bound hd (by positivity : 0 < endpointConstant d / 2)
    (by linarith : endpointConstant d / 2 < endpointConstant d)
  let r := Bridge.density ρ
  let v := FiniteEntropyGreen.dualPotential hd (spectralThreshold d / (2 * β)) r hρ
  have hv := FiniteEntropyGreen.dualPotential_admissible hd (spectralThreshold d / (2 * β)) r hρ
  have he := Gap.potential_ae hd hβ r hρ
  have hg : gibbsValue v =ᵐ[torusMeasure d] normalizedGibbs (Gap.densityPotential β ρ.value) :=
    Gap.gibbs_congr he
  have hrel := (FiniteEntropyGreen.relative_entropy_gibbs hR r hρ v hv
    (FiniteEntropyGreen.dualPotential_pair_integrable hd _ r hρ)).1
  refine hrel.congr ?_
  filter_upwards [hg] with x hx
  change ρ.value x * Real.log (ρ.value x / gibbsValue v x) = _
  rw [hx]

end Lemma25

section Lemma25Manuscript
variable {d : ℕ}

/-- **`eq:section2-primal-gap-identity`** in the manuscript normalization.  For `A > 0`, mean-zero
`u ∈ H^{d/2}`, `σ = e^u/∫e^u` and `β = (2 A c_d)⁻¹ = Gap.coefficient d A`:
`log ∫ e^u - A ‖u‖²_{Ḣ^{d/2}} = (β c_d/2 ‖σ‖²_{Ḣ^{-d/2}} - Ent σ) - A ‖u - u_σ‖²_{Ḣ^{d/2}}`,
`u_σ = β g * σ`. -/
theorem primal_gap_manuscript (hd : 0 < d) {A : ℝ} (hA : 0 < A) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) (hm : MeanZero u) :
    ∃ _ : InCriticalSobolev (Gap.densityPotential (Gap.coefficient d A) (normalizedGibbs u)),
      Real.log (∫ x, Real.exp (u x) ∂torusMeasure d) - A * (sobolevEnergyPos u).toReal =
        (Gap.coefficient d A * kernelConstant d / 2 *
            (negSobolevEnergy (normalizedGibbs u)).toReal -
          (torusEntropy (normalizedGibbs u)).toReal) -
        A * (sobolevEnergyPos (u - Gap.densityPotential (Gap.coefficient d A)
          (normalizedGibbs u))).toReal := by
  set σ := normalizedGibbsDensity hd u hu hm with hσdef
  have hσf : σ.FiniteEntropy := normalizedGibbsDensity_finiteEntropy hd u hu hm
  have hβ : 0 < Gap.coefficient d A := Gap.coefficient_pos hd hA
  have hreg := Gap.densityPotential_regular hd hβ σ hσf
  have hreg' : InCriticalSobolev (Gap.densityPotential (Gap.coefficient d A) (normalizedGibbs u)) :=
    hreg.1
  refine ⟨hreg', ?_⟩
  have hsub : InCriticalSobolev (u - Gap.densityPotential (Gap.coefficient d A)
      (normalizedGibbs u)) := FullHessianDecomposition.critical_sub _ _ hu hreg'
  rw [← potentialEnergy_eq_toReal_sobolevEnergyPos hu,
    ← potentialEnergy_eq_toReal_sobolevEnergyPos hsub,
    Gap.primal_gap_paper hd hA u hu hm]
  have := densityValue_eq_manuscript hd (Gap.coefficient d A) σ hσf
  change Gap.densityValue (Gap.coefficient d A) (normalizedGibbs u) = _ at this
  rw [this]
  rfl

/-- **`eq:section2-dual-gap-identity`** in the manuscript normalization.  For `A > 0`, a
finite-entropy density `ρ`, `β = (2 A c_d)⁻¹`, and `u = β g * ρ` (mean zero, in `H^{d/2}`), the
Gibbs density `σ = e^u / ∫ e^u` is a positive probability density with finite relative entropy
`H_r(ρ|σ) < ∞` and
`β c_d/2 ‖ρ‖²_{Ḣ^{-d/2}} - Ent ρ = log ∫ e^u - A ‖u‖²_{Ḣ^{d/2}} - H_r(ρ|σ)`. -/
theorem dual_gap_manuscript (hd : 0 < d) {A : ℝ} (hA : 0 < A) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    ∃ (hu : InCriticalSobolev (Gap.densityPotential (Gap.coefficient d A) ρ.value))
      (hm : MeanZero (Gap.densityPotential (Gap.coefficient d A) ρ.value)),
      (∀ x, 0 < normalizedGibbs (Gap.densityPotential (Gap.coefficient d A) ρ.value) x) ∧
      measureEntropy (densityMeasure ρ)
        (densityMeasure (normalizedGibbsDensity hd _ hu hm)) ≠ ∞ ∧
      Gap.coefficient d A * kernelConstant d / 2 * (negSobolevEnergy ρ.value).toReal -
          (torusEntropy ρ.value).toReal =
        Real.log (∫ x, Real.exp (Gap.densityPotential (Gap.coefficient d A) ρ.value x)
            ∂torusMeasure d) -
          A * (sobolevEnergyPos (Gap.densityPotential (Gap.coefficient d A) ρ.value)).toReal -
          (measureEntropy (densityMeasure ρ)
            (densityMeasure (normalizedGibbsDensity hd _ hu hm))).toReal := by
  have hβ : 0 < Gap.coefficient d A := Gap.coefficient_pos hd hA
  obtain ⟨hu, hm⟩ := Gap.densityPotential_regular hd hβ ρ hρ
  refine ⟨hu, hm, normalizedGibbs_pos hd _ hu hm, ?_, ?_⟩
  · have hpos := normalizedGibbs_pos hd _ hu hm
    rw [Ne, measureEntropy_density_eq_top_iff (σ := normalizedGibbsDensity hd _ hu hm) hpos,
      not_not]
    exact dual_gap_relativeEntropy_integrable hd hβ ρ hρ
  · have hpos := normalizedGibbs_pos hd _ hu hm
    rw [← relativeEntropy_eq_toReal_measureEntropy (σ := normalizedGibbsDensity hd _ hu hm)
      (ρ := ρ) hpos, ← potentialEnergy_eq_toReal_sobolevEnergyPos hu,
      ← densityValue_eq_manuscript hd _ ρ hρ]
    exact Gap.dual_gap_paper hd hA ρ hρ

end Lemma25Manuscript

end BecknerOnofri.V2.Vocab
