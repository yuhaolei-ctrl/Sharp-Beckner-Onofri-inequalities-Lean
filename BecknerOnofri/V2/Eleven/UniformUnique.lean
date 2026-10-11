module

public import BecknerOnofri.V2.Eleven.Estimates
public import BecknerOnofri.OptimizerDuality
public import BecknerOnofri.V2.Reaudit.Attainment.Main
public import BecknerOnofri.V2.Reaudit.Mixtures.Selection
public import BecknerOnofri.ContinuousMixtureMajorant
public import BecknerOnofri.EndpointDuality
public import BecknerOnofri.ElevenMixture
public import BecknerOnofri.ElevenStrictMixture
public import BecknerOnofri.ElevenScalarFinite
public import BecknerOnofri.ElevenScalarTail

@[expose] public section

/-! # Subsections 4.3-4.4: the scalar estimate and uniqueness of the uniform minimizer through 17.715

Source: `d11:prop:scalar` (Lemma 4.7 in the order of appearance in Section 4), the proof of
`subsec:section4-mixture` (`d11:eq:mixture-gap`, `d11:eq:beta0-full-entropy`) and the first sentences of
`d11:thm:interval` (uniqueness for `0 ≤ β ≤ 3543/200`, `β_gm ≥ 3543/200`).

The logical order of the manuscript is respected: nothing here uses coexistence or the upper bound,
and **the lower transition bound obtained here is non-strict** (`3543/200 ≤ β_gm`).

* `scalar_gap`: `11 H_n - (β_0/β_s) G_{11,n} > 1/2000` for all `n ≥ 1` (existing certified chain).
* `SmoothMixtureGap11` : the single Section 3 conclusion consumed here, with exactly the content of the
  strictness consequence of `d11:eq:mixture-gap`: `E_{β_0}(ρ) > 0` for every nonuniform smooth strictly
  positive finite-entropy countable cosine-power mixture, where `E_β(ρ) = Ent(ρ) - (β c_{11}/2) ‖ρ‖²_{Ḣ^{-11/2}}`
  (`= Ent - β/(2β_s) (2π)^{11}‖ρ‖²`).  It is a *hypothesis* of `uniform_unique_of_gap`.
* `smoothMixtureGap11` discharges the hypothesis from the repository's mixture chain
  (`ElevenMixture`/`ElevenStrictMixture`, route difference below), so that `uniform_unique` is unconditional.

Selection and attainment (REAUDIT S016, S009, S010): `Efree_beta0_nonneg` and `uniform_of_Efree_nonpos` obtain the
minimizer from `Reaudit.Attainment.subcritical_attainment` (direct method) and the canonical rearranged
minimizer from the written-route wrapper `Reaudit.Mixtures.canonical_selection_written`
(`coordinate_rearranged_minimizer` and `cosine_representation`), not from the polarization-closure
`PrescribedSelection.canonical_selection` nor `OptimizerDuality.exists_minimizer`.  The statement of
`CanonicalSelection 11` is the same.

Route differences: the manuscript's gap is `E_{β_0}(ρ) ≥ (1/44000) Σ_i P(L_i ≥ 1)` for the latent
hypergeometric variables `L`; the repository's chain gives `E_{β_0}(ρ) ≥ w_a² (latent weight) (1/22000)/2 > 0`
for any component `a` with `w_a > 0`, `N_a ≠ 0`, by the finite-mixture/limit route
(`finite_mixture_gap`, `countable_mixture_gap`).  The consequence used (strictness) is identical. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Eleven

open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- `β_0 = 3543/200 = 17.715`. -/
def beta0 : ℝ := 3543 / 200

/-- The manuscript's free energy `E_β(ρ) = Ent(ρ) - (β c_{11}/2) ‖ρ‖²_{Ḣ^{-11/2}}`
(`= Ent(ρ) - β/(2β_s) (2π)^{11} ‖ρ‖²_{Ḣ^{-11/2}}`), for `d = 11`. -/
def Efree (β : ℝ) (ρ : ProbabilityDensity 11) : ℝ :=
  (torusEntropy ρ.value).toReal - β * kernelConstant 11 / 2 * (negSobolevEnergy ρ.value).toReal

/-! ## Lemma `d11:prop:scalar` -/

/-- **`d11:prop:scalar`** (`d11:eq:gap`): `11 H_n - (β_0/β_s) G_{11,n} > 1/2000` for every `n ≥ 1`, with
`H_n = harmonic n`, `G_{11,n} = Eleven.scalarEnergy n = Σ_{k≠0} |k|^{-11} ∏ a_n(k_i)`.
Existing certified chain: `n ≤ 21` is `ScalarFinite.finite_scalar_gap` (rational comparison with the
certificate), all `n ≥ 1` is `ScalarTail.all_scalar_gap` (Gaussian estimate with the theta bound). -/
theorem scalar_gap {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) / 2000 < 11 * (harmonic n : ℝ) -
      beta0 / spectralThreshold 11 * HighDim.Eleven.scalarEnergy n :=
  HighDim.Eleven.ScalarTail.all_scalar_gap hn

theorem scalar_gap_finite {n : ℕ} (hn : 1 ≤ n) (hn21 : n ≤ 21) :
    (1 : ℝ) / 2000 < 11 * (harmonic n : ℝ) -
      beta0 / spectralThreshold 11 * HighDim.Eleven.scalarEnergy n :=
  HighDim.Eleven.ScalarFinite.finite_scalar_gap hn hn21

/-! ## The hypothesis taken from Section 3 -/

/-- The strictness consequence of `d11:eq:mixture-gap`, restricted to smooth strictly positive
mixtures (the only mixtures to which the proof applies it, see `uniform_unique_of_gap`). -/
def SmoothMixtureGap11 : Prop :=
  ∀ ρ : ProbabilityDensity 11, ρ.FiniteEntropy → SmoothOnTorus ρ.value → (∀ x, 0 < ρ.value x) →
    IsCountableCosineMixture ρ → ¬ ρ.value =ᵐ[torusMeasure 11] (fun _ => 1) →
      0 < Efree beta0 ρ

/-! ## Elementary facts on the uniform density -/

theorem pressureValue_uniform (β : ℝ) : pressureValue β (uniformDensity 11) = 0 := by
  simp [pressureValue, spectralEnergy]

theorem Efree_congr_ae {ρ σ : ProbabilityDensity 11}
    (h : ρ.value =ᵐ[torusMeasure 11] σ.value) (β : ℝ) : Efree β ρ = Efree β σ := by
  unfold Efree
  have e1 : negSobolevEnergy ρ.value = negSobolevEnergy σ.value := by
    unfold negSobolevEnergy
    simp only [fourierCoeff_congr_ae h]
  have e2 : torusEntropy ρ.value = torusEntropy σ.value := homEntropy_congr_ae h
  rw [e1, e2]

theorem Efree_uniform (β : ℝ) : Efree β (uniformDensity 11) = 0 := by
  have h1 : negSobolevEnergy (uniformDensity 11).value = 0 := by
    unfold negSobolevEnergy
    refine ENNReal.tsum_eq_zero.mpr fun k => ?_
    have : fourierCoeff (uniformDensity 11).value k.val = 0 :=
      uniformDensity_fourierCoeff_nonzero _ k.property
    simp [this]
  have h2 : (torusEntropy (uniformDensity 11).value).toReal = 0 := by
    rw [← entropy_eq_toReal_torusEntropy _ (uniformDensity_finiteEntropy 11)]
    simp
  unfold Efree
  rw [h1, h2]
  simp

theorem Efree_eq_neg_pressureValue (β : ℝ) (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) :
    pressureValue β ρ = ((-(Efree β ρ) : ℝ) : EReal) := by
  rw [pressureValue_eq_real_ms (by norm_num) β ρ hρ]
  unfold Efree
  congr 1
  ring

theorem Efree_le_iff (β : ℝ) (ρ σ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy)
    (hσ : σ.FiniteEntropy) :
    pressureValue β σ ≤ pressureValue β ρ ↔ Efree β ρ ≤ Efree β σ := by
  rw [Efree_eq_neg_pressureValue β ρ hρ, Efree_eq_neg_pressureValue β σ hσ, EReal.coe_le_coe_iff]
  constructor <;> intro h <;> linarith

/-- `E_β(ρ) = E_{β_0}(ρ) + (β_0-β)/(2β_s)(2π)^{11}‖ρ‖²` (`d11:eq:beta0-full-entropy`). -/
theorem Efree_sub (β β' : ℝ) (ρ : ProbabilityDensity 11) :
    Efree β ρ = Efree β' ρ + (β' - β) * kernelConstant 11 / 2 * (negSobolevEnergy ρ.value).toReal := by
  unfold Efree; ring

/-! ## Uniqueness of the uniform minimizer, conditional on `SmoothMixtureGap11` -/

section Conditional

variable (hgap : SmoothMixtureGap11)
include hgap

/-- `E_{β_0}(σ) ≥ 0` for every finite-entropy density: a minimizer exists (Prop 2.7), Lemma 2.13
replaces it by a minimizing smooth mixture with the same free energy, and the mixture gap gives the
sign. -/
theorem Efree_beta0_nonneg (σ : ProbabilityDensity 11) (hσ : σ.FiniteEntropy) :
    0 ≤ Efree beta0 σ := by
  by_contra hneg
  have hneg : Efree beta0 σ < 0 := not_le.mp hneg
  have h0 : (0 : ℝ) < beta0 := by unfold beta0; norm_num
  have h22 : beta0 < 2 * ((11 : ℕ) : ℝ) := by unfold beta0; norm_num
  obtain ⟨ρs, hρs⟩ :=
    (Reaudit.Attainment.subcritical_attainment (d := 11) (by norm_num) h0 h22).2.1
  obtain ⟨η, u, -, hηmin, -, -, -, -, hηs, hηpos, -, -, -, -, -, -, -, hηmix, -, -⟩ :=
    Reaudit.Mixtures.canonical_selection_written (d := 11) (by norm_num) beta0 h0 h22 ρs hρs
  have hle := (Efree_le_iff beta0 η σ hηmin.1 hσ).1 (hηmin.2 σ hσ)
  by_cases hnon : η.value =ᵐ[torusMeasure 11] (fun _ => 1)
  · have hu : η.value =ᵐ[torusMeasure 11] (uniformDensity 11).value := hnon
    have := Efree_congr_ae hu beta0
    rw [Efree_uniform] at this
    linarith
  · have := hgap η hηmin.1 hηs hηpos hηmix hnon
    linarith

/-- A finite-entropy density with `E_{β_0} ≤ 0` is uniform. -/
theorem uniform_of_Efree_nonpos (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy)
    (hle : Efree beta0 ρ ≤ 0) : ρ.value =ᵐ[torusMeasure 11] (fun _ => 1) := by
  by_contra hnon
  have h0 : (0 : ℝ) < beta0 := by unfold beta0; norm_num
  have h22 : beta0 < 2 * ((11 : ℕ) : ℝ) := by unfold beta0; norm_num
  have hmin : IsGlobalMinimizer beta0 ρ := by
    refine ⟨hρ, fun σ hσ => ?_⟩
    rw [Efree_le_iff beta0 ρ σ hρ hσ]
    exact hle.trans (Efree_beta0_nonneg hgap σ hσ)
  obtain ⟨η, u, -, hηmin, -, -, hpv, -, hηs, hηpos, -, -, -, -, -, -, -, hηmix, -, hηnon⟩ :=
    Reaudit.Mixtures.canonical_selection_written (d := 11) (by norm_num) beta0 h0 h22 ρ hmin
  have hE : Efree beta0 η = Efree beta0 ρ := by
    have h1 := Efree_eq_neg_pressureValue beta0 η hηmin.1
    have h2 := Efree_eq_neg_pressureValue beta0 ρ hρ
    rw [hpv, h2] at h1
    have := EReal.coe_eq_coe_iff.mp h1
    linarith
  have := hgap η hηmin.1 hηs hηpos hηmix (hηnon hnon)
  linarith

/-- **Uniqueness of the uniform minimizer for `0 ≤ β ≤ 3543/200`** (`d11:thm:interval`, second sentence;
`subsec:section4-mixture`), conditional on the Section 3 mixture gap. -/
theorem uniform_unique_of_gap (β : ℝ) (_hβ : 0 ≤ β) (hβ0 : β ≤ beta0)
    (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) :
    IsGlobalMinimizer β ρ ↔ ρ.value =ᵐ[torusMeasure 11] (fun _ => 1) := by
  have hA : 0 ≤ (negSobolevEnergy ρ.value).toReal := ENNReal.toReal_nonneg
  have hc := kernelConstant_pos (d := 11) (by norm_num)
  constructor
  · intro hm
    have hz := hm.2 (uniformDensity 11) (uniformDensity_finiteEntropy 11)
    have hle := (Efree_le_iff β ρ (uniformDensity 11) hρ (uniformDensity_finiteEntropy 11)).1 hz
    rw [Efree_uniform] at hle
    apply uniform_of_Efree_nonpos hgap ρ hρ
    have := Efree_sub β beta0 ρ
    have h2 : 0 ≤ (beta0 - β) * kernelConstant 11 / 2 * (negSobolevEnergy ρ.value).toReal := by
      have : 0 ≤ beta0 - β := by linarith
      positivity
    linarith
  · intro he
    have hu : ρ.value =ᵐ[torusMeasure 11] (uniformDensity 11).value := he
    refine ⟨hρ, fun σ hσ => ?_⟩
    rw [Efree_le_iff β ρ σ hρ hσ, Efree_congr_ae hu, Efree_uniform]
    have h1 := Efree_beta0_nonneg hgap σ hσ
    have h2 := Efree_sub β beta0 σ
    have h3 : 0 ≤ (beta0 - β) * kernelConstant 11 / 2 * (negSobolevEnergy σ.value).toReal := by
      have : 0 ≤ beta0 - β := by linarith
      positivity
    linarith

/-- `P_11(β) = 0` for `0 ≤ β ≤ 3543/200`, conditional on the mixture gap. -/
theorem pressure_zero_of_gap (β : ℝ) (_hβ : 0 ≤ β) (hβ0 : β ≤ beta0) : pressure 11 β = 0 := by
  apply le_antisymm
  · refine iSup_le fun ρ => iSup_le fun hρ => ?_
    have h := Efree_beta0_nonneg hgap ρ hρ
    have h2 := Efree_sub β beta0 ρ
    have hA : 0 ≤ (negSobolevEnergy ρ.value).toReal := ENNReal.toReal_nonneg
    have hc := kernelConstant_pos (d := 11) (by norm_num)
    have h3 : 0 ≤ (beta0 - β) * kernelConstant 11 / 2 * (negSobolevEnergy ρ.value).toReal := by
      have : 0 ≤ beta0 - β := by linarith
      positivity
    show pressureValue β ρ ≤ 0
    rw [Efree_eq_neg_pressureValue β ρ hρ, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    linarith
  · exact pressure_nonneg 11 β

/-- **The non-strict lower bound** `3543/200 ≤ β_gm(11)` (`d11:thm:interval`, "gives `β_gm ≥ β_0`").
It does not use coexistence; the strict inequality comes only after coexistence. -/
theorem beta0_le_globalTransition : beta0 ≤ VariationalCurves.globalTransition 11 :=
  (VariationalCurves.pressure_zero_iff (by norm_num) beta0).1
    (pressure_zero_of_gap hgap beta0 (by unfold beta0; norm_num) le_rfl)

end Conditional

/-! ## Discharge of `SmoothMixtureGap11` from the repository's mixture chain -/

open Legacy.BecknerOnofri in
/-- The data of a smooth countable cosine-power mixture, with the majorant derived from continuity. -/
theorem smoothMixture_data {ρ : ProbabilityDensity 11} (hs : SmoothOnTorus ρ.value)
    (hmix : IsCountableCosineMixture ρ) :
    ∃ (w : ℕ → ℝ) (N : ℕ → Fin 11 → ℕ) (_ : ∀ n, 0 ≤ w n) (_ : HasSum w 1)
      (_ : Summable fun n => w n * CosineMixture.tensor (N n) 0),
      ρ.value =ᵐ[torusMeasure 11] CosineMixtureApproximation.rho w N := by
  obtain ⟨w, N, hw, hm, he⟩ := hmix
  obtain ⟨K, hK⟩ := hs.exists_lipschitz
  have he' : ρ.value =ᵐ[torusMeasure 11] CosineMixtureApproximation.rho w N := he
  exact ⟨w, N, hw, hm, CosineMixtureTransfer.mixture_majorant_of_continuous ρ.value
    hK.continuous w N hw hm.summable he', he'⟩

theorem entropy_real_eq_legacy (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy)
    (r : Legacy.TorusEndpoint.ProbabilityDensity 11)
    (hae : ρ.value =ᵐ[torusMeasure 11] r.value) :
    (torusEntropy ρ.value).toReal = Legacy.TorusEndpoint.densityEntropy r.value := by
  rw [← entropy_eq_toReal_torusEntropy ρ hρ]
  unfold entropy Legacy.TorusEndpoint.densityEntropy
  exact integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])

/-- `β_0 c_{11}/2 ‖ρ‖² = coupling · fourierEnergy r` (`coupling = β_0/(2β_s)`): the manuscript term
`β_0/(2β_s)(2π)^{11}‖ρ‖²` equals the repository's legacy energy. -/
theorem energy_term_eq_legacy (ρ : ProbabilityDensity 11)
    (r : Legacy.TorusEndpoint.ProbabilityDensity 11)
    (hae : ρ.value =ᵐ[torusMeasure 11] r.value)
    (hsum : Summable (Legacy.TorusEndpoint.densitySpectralTerm r)) :
    beta0 * kernelConstant 11 / 2 * (negSobolevEnergy ρ.value).toReal =
      Legacy.BecknerOnofri.ElevenMixture.coupling * Legacy.BecknerOnofri.fourierEnergy r := by
  have hnn : 0 ≤ Legacy.BecknerOnofri.fourierEnergy r :=
    tsum_nonneg fun k => by
      unfold Legacy.TorusEndpoint.densitySpectralTerm
      exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hE : spectralEnergy ρ = ENNReal.ofReal (Legacy.BecknerOnofri.fourierEnergy r) := by
    rw [← Bridge.rawDensity_spectralEnergy r hsum]
    unfold spectralEnergy spectralTerm
    refine tsum_congr fun k => ?_
    rw [fourierCoeff_congr_ae hae]
    rfl
  have hkey := kernelConstant_mul_negSobolevEnergy_toReal (d := 11) (by norm_num) ρ
  rw [hE, ENNReal.toReal_ofReal hnn] at hkey
  have hs := spectralThreshold_pos' (d := 11) (by norm_num)
  unfold Legacy.BecknerOnofri.ElevenMixture.coupling beta0
  have : kernelConstant 11 * (negSobolevEnergy ρ.value).toReal =
      Legacy.BecknerOnofri.fourierEnergy r / spectralThreshold 11 := hkey
  calc (3543 : ℝ) / 200 * kernelConstant 11 / 2 * (negSobolevEnergy ρ.value).toReal
      = 3543 / 200 / 2 * (kernelConstant 11 * (negSobolevEnergy ρ.value).toReal) := by ring
    _ = _ := by rw [this]; field_simp

/-- **`SmoothMixtureGap11`, discharged.**  A nonuniform smooth countable cosine-power mixture has a
component with positive weight and nonzero index; the repository's strict gap
(`ElevenMixture.countable_mixture_strict_of_component`) gives `coupling · E < Ent`. -/
theorem smoothMixtureGap11 : SmoothMixtureGap11 := by
  intro ρ hρ hsm hpos hmix hnon
  obtain ⟨w, N, hw, hm, hSup, he⟩ := smoothMixture_data hsm hmix
  have hcomp : ∃ a, 0 < w a ∧ N a ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hnon
    have hall : ∀ n, 0 < w n → N n = 0 := fun n hn => by
      by_contra hne; exact absurd (hno n hn) (by simpa using hne)
    have h1 := Legacy.BecknerOnofri.ElevenMixture.countable_uniform_of_no_component
      w N hw hm hall
    filter_upwards [he] with x hx
    rw [hx]
    exact h1 x
  obtain ⟨a, ha, hNa⟩ := hcomp
  have hstrict := Legacy.BecknerOnofri.ElevenMixture.countable_mixture_strict_of_component
    w N hw hm hSup a ha hNa
  have hsumm := (Legacy.BecknerOnofri.ElevenMixture.countable_mixture_endpoint w N hw hm hSup).1
  set r := Legacy.BecknerOnofri.CosineMixtureApproximation.probabilityDensity w N hw hm hSup with hr
  have hae : ρ.value =ᵐ[torusMeasure 11] r.value := he
  unfold Efree
  rw [energy_term_eq_legacy ρ r hae hsumm, entropy_real_eq_legacy ρ hρ r hae]
  linarith

/-- **Uniqueness of the uniform minimizer for `0 ≤ β ≤ 3543/200`** (`d11:thm:interval`), unconditional. -/
theorem uniform_unique (β : ℝ) (hβ : 0 ≤ β) (hβ0 : β ≤ beta0)
    (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) :
    IsGlobalMinimizer β ρ ↔ ρ.value =ᵐ[torusMeasure 11] (fun _ => 1) :=
  uniform_unique_of_gap smoothMixtureGap11 β hβ hβ0 ρ hρ

theorem pressure_zero_below (β : ℝ) (hβ : 0 ≤ β) (hβ0 : β ≤ beta0) : pressure 11 β = 0 :=
  pressure_zero_of_gap smoothMixtureGap11 β hβ hβ0

/-- `3543/200 ≤ β_gm(11)` (non-strict). -/
theorem transition_lower : beta0 ≤ VariationalCurves.globalTransition 11 :=
  beta0_le_globalTransition smoothMixtureGap11

end BecknerOnofri.V2.Eleven
