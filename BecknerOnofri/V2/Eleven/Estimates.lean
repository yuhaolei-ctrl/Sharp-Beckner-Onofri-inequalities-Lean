module

public import BecknerOnofri.V2.Vocab.Section2Bridge
public import BecknerOnofri.ElevenTrialConsequences
public import BecknerOnofri.ElevenEuclideanEntropy
public import BecknerOnofri.ElevenPeriodizedFourier
public import BecknerOnofri.ElevenUnscaledFourier
public import BecknerOnofri.ElevenConstants
public import BecknerOnofri.Uniform
public import BecknerOnofri.Entropy

@[expose] public section

/-! # Section 4 estimates in the manuscript normalization

* Lemma 4.4 (`lem:section4-euclidean-entropy`): `η`, `η_ε`, the scaling `η_{1/5} = euclideanProfile`,
  `∫ η = 1`, `Ent_{ℝ^{11}}(η_{1/5}) = log(3·5^{12}/(2^9 π^6)) + 17897/2520 < 721/50`.
* Proposition 4.2 (`prop:section4-entropy-bound`): `Ent(ρ_*) < 8653/600`, via the chain
  `Ent(ρ_*) = Ent_ℝ(η_{1/5}) + H_Sh(N|Y) < 721/50 + 1/600` of Lemmas 4.3, 4.4, 4.5.
* Lemma 4.6 (`lem:section4-profile-fourier-transform`) and the energy bound `eq:d11:upper`:
  `(2π)^{11}/2 · ‖ρ_*‖²_{Ḣ^{-11/2}} > 14475384292906/10^{12}`.
* The explicit competitor upper bound `β_gm(11) < 2063/100` through the quotient characterization
  `eq:section2-beta-gm-quotient` (`d11:eq:beta-upper`), with the printed `1/600`.
* `P_11(β_s) > 4/75 > 1/30` (`eq:section4-positive-spectral-pressure`).

All numerical content is the existing certified chain (`ElevenEuclideanEntropy`, `ElevenConditionalEntropy`,
`ElevenCompetitorEnergy`); this file restates it in the manuscript's normalization (`Ent = (torusEntropy ·).toReal`,
`‖ρ‖²_{Ḣ^{-11/2}} = negSobolevEnergy`, `(2π)^{11}` explicit) and adds the printed-constant forms. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Eleven

open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-! ## The profile `η` and its rescaling (eq:section4-eta, eq:section4-eta-epsilon) -/

/-- `η(x) = (122880/π^6)(1+|x|^2)^{-11}` on `ℝ^{11}` (`eq:section4-eta`). -/
def etaProfile (x : Fin 11 → ℝ) : ℝ :=
  122880 / Real.pi ^ 6 * (1 + ∑ i : Fin 11, x i ^ 2) ^ (-11 : ℤ)

/-- `η_ε(x) = ε^{-11} η(x/ε)` (`eq:section4-eta-epsilon`). -/
def etaEps (ε : ℝ) (x : Fin 11 → ℝ) : ℝ := ε ^ (-11 : ℤ) * etaProfile (ε⁻¹ • x)

/-- `η_{1/5}` is the repository's `euclideanProfile` (`eq:section4-rho-star`'s summand). -/
theorem etaEps_fifth : etaEps (1 / 5) = HighDim.Eleven.euclideanProfile := by
  funext x
  unfold etaEps etaProfile HighDim.Eleven.euclideanProfile
  have h : ∀ i : Fin 11, ((1 / 5 : ℝ)⁻¹ • x) i ^ 2 = 25 * x i ^ 2 := by
    intro i; simp [smul_eq_mul]; ring
  simp only [h, ← Finset.mul_sum]
  have : ((1 / 5 : ℝ)) ^ (-11 : ℤ) = 5 ^ 11 := by
    rw [zpow_neg, one_div, inv_zpow, inv_inv]; norm_cast
  rw [this]
  ring

theorem etaProfile_pos (x : Fin 11 → ℝ) : 0 < etaProfile x := by
  unfold etaProfile
  have : 0 < 1 + ∑ i : Fin 11, x i ^ 2 := by positivity
  positivity

/-- `euclideanProfile (x/5) = 5^{11} η(x)`. -/
theorem euclideanProfile_smul_fifth (x : Fin 11 → ℝ) :
    HighDim.Eleven.euclideanProfile ((1 / 5 : ℝ) • x) = 5 ^ 11 * etaProfile x := by
  unfold HighDim.Eleven.euclideanProfile etaProfile
  have h : ∀ i : Fin 11, ((1 / 5 : ℝ) • x) i ^ 2 = (1 / 25) * x i ^ 2 := by
    intro i; simp [smul_eq_mul]; ring
  simp only [h, ← Finset.mul_sum]
  have h25 : 1 + 25 * (1 / 25 * ∑ i : Fin 11, x i ^ 2) = 1 + ∑ i : Fin 11, x i ^ 2 := by ring
  rw [h25]
  ring

/-- `η` is integrable. -/
theorem etaProfile_integrable : Integrable etaProfile := by
  have h := (HighDim.Eleven.euclideanProfile_integrable).comp_smul (E := Fin 11 → ℝ)
    (show ((1 / 5 : ℝ)) ≠ 0 by norm_num)
  have h2 : (fun x : Fin 11 → ℝ => HighDim.Eleven.euclideanProfile ((1 / 5 : ℝ) • x)) =
      fun x => 5 ^ 11 * etaProfile x := funext euclideanProfile_smul_fifth
  rw [h2] at h
  exact (h.const_mul ((5 : ℝ) ^ 11)⁻¹).congr (Filter.Eventually.of_forall fun x => by
    field_simp)

/-- `∫ η = 1`: `η` is a probability density (`lem:section4-euclidean-entropy`, first claim), obtained
from the repository's `∫ η_{1/5} = 1` by scaling.  (The written proof uses the beta integral
`eq:section4-beta-integral` with `a = d = 11`; the Gamma normalization `122880 = 32·3628800/945` is
inside `euclideanProfile_integral`.) -/
theorem etaProfile_integral : ∫ x, etaProfile x = 1 := by
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Fin 11 → ℝ)))
    (HighDim.Eleven.euclideanProfile) (1 / 5 : ℝ)
  have h2 : (fun x : Fin 11 → ℝ => HighDim.Eleven.euclideanProfile ((1 / 5 : ℝ) • x)) =
      fun x => 5 ^ 11 * etaProfile x := funext euclideanProfile_smul_fifth
  rw [h2, integral_const_mul, HighDim.Eleven.euclideanProfile_integral] at h
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  have h5 : (5 : ℝ) ^ 11 * ∫ x, etaProfile x = 5 ^ 11 := by
    rw [h]; simp [abs_of_nonneg]
  have : (5 : ℝ) ^ 11 ≠ 0 := by positivity
  exact mul_left_cancel₀ this (h5.trans (mul_one _).symm)

/-! ## Lemma 4.4: the Euclidean entropy of `η_{1/5}` -/

/-- `Ent_{ℝ^{11}}(η_{1/5}) = log(3·5^{12}/(2^9 π^6)) + 17897/2520`
(`eq:section4-euclidean-entropy`, equality; the integral is relative to Lebesgue measure). -/
theorem euclidean_entropy_eq :
    ∫ x, etaEps (1 / 5) x * Real.log (etaEps (1 / 5) x) =
      Real.log (3 * 5 ^ 12 / (2 ^ 9 * Real.pi ^ 6)) + 17897 / 2520 := by
  rw [etaEps_fifth]
  exact HighDim.Eleven.euclideanProfile_entropy_exact

/-- `Ent_{ℝ^{11}}(η_{1/5}) < 721/50` (`eq:section4-euclidean-entropy`, inequality). -/
theorem euclidean_entropy_lt :
    ∫ x, etaEps (1 / 5) x * Real.log (etaEps (1 / 5) x) < 721 / 50 := by
  rw [etaEps_fifth]
  exact HighDim.Eleven.euclideanProfile_entropy_lt

/-- The finer rational bound used in `d11:eq:entropy-upper`. -/
theorem euclidean_entropy_fine :
    ∫ x, etaEps (1 / 5) x * Real.log (etaEps (1 / 5) x) <
      7305164 / 10 ^ 6 + 17897 / 2520 := by
  rw [etaEps_fifth]
  exact HighDim.Eleven.euclideanProfile_entropy_fine

theorem euclidean_entropy_integrable :
    Integrable (fun x => etaEps (1 / 5) x * Real.log (etaEps (1 / 5) x)) := by
  rw [etaEps_fifth]
  exact HighDim.Eleven.euclideanProfile_entropy_integrable

/-! ## Lemma 4.3 (identity) and Lemma 4.5 (label entropy) in the explicit conditional-entropy form -/

/-- Any `ProbabilityDensity 11` with value `ρ_*` has finite entropy. -/
theorem finiteEntropy_of_value_eq (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) : ρ.FiniteEntropy := by
  have := HighDim.Eleven.competitorDensity_finiteEntropy
  unfold ProbabilityDensity.FiniteEntropy at this ⊢
  rw [h]
  exact this

/-- `eq:section4-periodization-entropy-identity`, with `H_Sh(N|Y)` the explicit formula
`eq:section4-conditional-entropy-formula` (`conditionalLabelEntropy`).  Route: the existing proof
unfolds the cube and applies Fubini-Tonelli to the conditional probabilities `p(n|y)` exactly as in
`eq:section4-entropy-chain-rule-proof`; the probabilistic reading of the same quantity as
`H_Sh(N|Y)` for the lattice-label decomposition of a random vector with density `η_{1/5}` is
`JointLaw.lean`. -/
theorem periodization_entropy_identity (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    entropy ρ = (∫ x, etaEps (1 / 5) x * Real.log (etaEps (1 / 5) x)) +
      HighDim.Eleven.conditionalLabelEntropy := by
  rw [etaEps_fifth]
  have h1 : entropy ρ = entropy HighDim.Eleven.competitorDensity := by
    unfold entropy; rw [h]; rfl
  rw [h1]
  exact HighDim.Eleven.periodization_entropy_identity

/-- `eq:section4-label-entropy-bound`: `H_Sh(N|Y) < 1/600`.  The repository proves the stronger
`< 1/625` (the written arithmetic `eq:section4-label-entropy-final-rational` gives `1/600`; the
repository's rational comparison is `HighDim.Eleven.label_entropy_rational`, `< 1/625`). -/
theorem label_entropy_lt : HighDim.Eleven.conditionalLabelEntropy < 1 / 600 :=
  HighDim.Eleven.conditionalLabelEntropy_lt.trans (by norm_num)

/-- `H_Sh(N|Y) ≤ H_Sh(N) ≤ 11 H_Sh(N_1)` (`eq:section4-label-entropy-subadditivity`). -/
theorem label_entropy_chain :
    HighDim.Eleven.conditionalLabelEntropy ≤ HighDim.Eleven.labelEntropy ∧
    HighDim.Eleven.labelEntropy ≤
      11 * -∑' n : ℤ, HighDim.Eleven.coordinateLabelProbability n *
        Real.log (HighDim.Eleven.coordinateLabelProbability n) :=
  ⟨HighDim.Eleven.conditionalLabelEntropy_le_labelEntropy,
    HighDim.Eleven.labelEntropy_subadditive.2⟩

/-! ## Proposition 4.2: the entropy bound -/

/-- The chain `Ent(ρ_*) < 721/50 + 1/600` of the text after `prop:section4-entropy-bound`. -/
theorem entropy_lt_chain (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    entropy ρ < 721 / 50 + 1 / 600 := by
  rw [periodization_entropy_identity ρ h]
  exact add_lt_add euclidean_entropy_lt label_entropy_lt

/-- **Proposition 4.2** (`prop:section4-entropy-bound`): `Ent(ρ_*) < 8653/600`. -/
theorem periodized_entropy_bound (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (torusEntropy ρ.value).toReal < 8653 / 600 := by
  have hρ := finiteEntropy_of_value_eq ρ h
  rw [← entropy_eq_toReal_torusEntropy ρ hρ]
  have := entropy_lt_chain ρ h
  linarith

/-- `d11:eq:entropy-upper`: `Ent(ρ_*) < 7305164/10^6 + 17897/2520 + 1/600`. -/
theorem periodized_entropy_fine (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (torusEntropy ρ.value).toReal < 7305164 / 10 ^ 6 + 17897 / 2520 + 1 / 600 := by
  have hρ := finiteEntropy_of_value_eq ρ h
  rw [← entropy_eq_toReal_torusEntropy ρ hρ, periodization_entropy_identity ρ h]
  exact add_lt_add euclidean_entropy_fine label_entropy_lt |>.trans_eq (by ring)

/-- The existing competitor entropy bound `18011/1250` is strictly stronger than the printed
`8653/600`; the difference is `193/15000`.  This is a bridge, not an identity. -/
theorem entropy_bound_bridge : (18011 : ℝ) / 1250 < 8653 / 600 ∧
    (8653 : ℝ) / 600 - 18011 / 1250 = 193 / 15000 := by norm_num

theorem periodized_entropy_bound_of_repository (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (torusEntropy ρ.value).toReal < 18011 / 1250 := by
  have hρ := finiteEntropy_of_value_eq ρ h
  rw [← entropy_eq_toReal_torusEntropy ρ hρ]
  exact HighDim.Eleven.competitor_entropy ρ h

/-! ## Lemma 4.6: the Fourier transform of the profile -/

/-- `Φ(z) = e^{-z} P(z)/945` (`eq:section4-Phi`). -/
abbrev Phi (z : ℝ) : ℝ := HighDim.Eleven.fourierProfile z

/-- `P(z) = z^5 + 15 z^4 + 105 z^3 + 420 z^2 + 945 z + 945` (`eq:section4-profile-polynomial`). -/
abbrev Ppoly (z : ℝ) : ℝ := HighDim.Eleven.fourierPolynomial z

theorem Ppoly_eq (z : ℝ) : Ppoly z = z ^ 5 + 15 * z ^ 4 + 105 * z ^ 3 + 420 * z ^ 2 + 945 * z + 945 :=
  rfl

theorem Phi_eq (z : ℝ) : Phi z = Real.exp (-z) * Ppoly z / 945 := rfl

theorem Phi_pos {z : ℝ} (hz : 0 ≤ z) : 0 < Phi z := HighDim.Eleven.fourierProfile_pos hz

open scoped RealInnerProductSpace in
lemma etaProfile_norm (x : EuclideanSpace ℝ (Fin 11)) :
    etaProfile (fun i => x i) = (122880 / Real.pi ^ 6) * (1 + ‖x‖ ^ 2) ^ (-(11 : ℝ)) := by
  simp only [etaProfile, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [show -(11 : ℝ) = ((-11 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]

/-- `η̂_{ℝ^{11}}(ξ) = Φ(2π|ξ|)` (`eq:section4-eta-fourier-transform`) with the Euclidean convention
`f̂(ξ) = ∫ f(x) e^{-2πi ξ·x} dx` of `eq:section4-euclidean-fourier-convention`
(`StudentIntegral.phase ξ x = exp(-(2π ⟨ξ,x⟩) i)`). -/
theorem eta_fourier (ξ : EuclideanSpace ℝ (Fin 11)) :
    (∫ x : EuclideanSpace ℝ (Fin 11),
      StudentIntegral.phase ξ x * ((etaProfile (fun i => x i) : ℝ) : ℂ)) =
        ((Phi (2 * Real.pi * ‖ξ‖) : ℝ) : ℂ) := by
  simp_rw [etaProfile_norm]
  exact HighDim.Eleven.unscaledProfile_fourier ξ

/-- `η̂_{1/5,ℝ^{11}}(ξ) = Φ(2π|ξ|/5)` (scaling, after `eq:section4-eta-fourier-transform`). -/
theorem etaEps_fifth_fourier (ξ : EuclideanSpace ℝ (Fin 11)) :
    (∫ x : EuclideanSpace ℝ (Fin 11),
      StudentIntegral.phase ξ x * ((etaEps (1 / 5) (fun i => x i) : ℝ) : ℂ)) =
        ((Phi (2 * Real.pi * ‖ξ‖ / 5) : ℝ) : ℂ) := by
  rw [etaEps_fifth]
  exact HighDim.Eleven.euclideanProfile_fourier ξ

/-- `ρ̂_*(k) = Φ((2π/5)|k|)` (`eq:section4-rho-star-fourier`), in the torus convention
`f̂(k) = ∫ f e^{-2πi k·x} dm_{11}`. -/
theorem rhoStar_fourier (k : Frequency 11) :
    fourierCoeff HighDim.Eleven.periodizedProfile k =
      ((Phi (2 * Real.pi / 5 * frequencyLength k) : ℝ) : ℂ) := by
  rw [HighDim.Eleven.periodizedProfile_fourier]
  congr 2
  ring

theorem rhoStar_fourier_pos (k : Frequency 11) :
    0 < Phi (2 * Real.pi / 5 * frequencyLength k) :=
  Phi_pos (by unfold frequencyLength; positivity)

/-! ## The energy bound `eq:d11:upper` in the manuscript normalization -/

/-- `(2π)^{11}/2 · ‖ρ_*‖²_{Ḣ^{-11/2}} > 14475384292906/10^{12}` (`eq:d11:upper`,
`eq:d11:competitor-rounded-sum`).  The numerical content is the existing certified computation
(`Shell.certified_finite_energy` → `competitor_energy`), stated for `spectralEnergy`; here it is
transported through `spectralEnergy ρ = (2π)^{11} ‖ρ‖²` (`spectralEnergy_eq_mul_negSobolevEnergy`). -/
theorem periodized_energy_bound (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (14475384292906 : ℝ) / 10 ^ 12 <
      (2 * Real.pi) ^ 11 / 2 * (negSobolevEnergy ρ.value).toReal := by
  have hρ := finiteEntropy_of_value_eq ρ h
  have hq := HighDim.Eleven.competitor_energy ρ h
  have hfin : spectralEnergy ρ ≠ ∞ := finiteEntropy_spectralEnergy_ne_top (by norm_num) ρ hρ
  have hN : negSobolevEnergy ρ.value ≠ ∞ := (negSobolevEnergy_ne_top_iff ρ).2 hfin
  rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfin,
    spectralEnergy_eq_mul_negSobolevEnergy, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hq
  linarith

/-! ## The explicit competitor upper bound `d11:eq:beta-upper` -/

/-- A finite-entropy density with positive Ĥ^{-11/2} energy has positive entropy. -/
theorem entropy_pos_of_energy_pos (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy)
    (hN : 0 < (negSobolevEnergy ρ.value).toReal) : 0 < (torusEntropy ρ.value).toReal := by
  rw [pos_entropy_iff ρ hρ]
  intro hu
  have hu' : ρ.value =ᵐ[torusMeasure 11] (uniformDensity 11).value := hu
  have : negSobolevEnergy ρ.value = 0 := by
    unfold negSobolevEnergy
    refine ENNReal.tsum_eq_zero.mpr fun k => ?_
    have h1 : fourierCoeff ρ.value k.val = 0 := by
      rw [fourierCoeff_congr_ae hu']
      exact uniformDensity_fourierCoeff_nonzero _ k.property
    simp [h1]
  rw [this] at hN
  simp at hN

/-- **The upper bound for `β_gm(11)`** through the quotient characterization
`eq:section2-beta-gm-quotient` (`globalTransition_eq_manuscript_quotient`), exactly the
computation `d11:eq:beta-upper` with the printed `1/600`:
`β_gm < (64/945)(104348/33215)^5 (7305164/10^6 + 17897/2520 + 1/600)/(14475384292906/10^12) < 2063/100`. -/
theorem globalTransition_lt_of_competitor (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy)
    (he : (torusEntropy ρ.value).toReal < 7305164 / 10 ^ 6 + 17897 / 2520 + 1 / 600)
    (hq : (14475384292906 : ℝ) / 10 ^ 12 <
      (2 * Real.pi) ^ 11 / 2 * (negSobolevEnergy ρ.value).toReal) :
    VariationalCurves.globalTransition 11 < 2063 / 100 := by
  set S := (torusEntropy ρ.value).toReal with hS
  set A := (negSobolevEnergy ρ.value).toReal with hA
  have hc := kernelConstant_pos (d := 11) (by norm_num)
  have hs := spectralThreshold_pos' (d := 11) (by norm_num)
  have hcs := kernelConstant_mul_spectralThreshold (d := 11) (by norm_num)
  have hE0 : (0 : ℝ) < 14475384292906 / 10 ^ 12 := by norm_num
  have hApos : 0 < A := by
    by_contra hneg
    have : A ≤ 0 := not_lt.mp hneg
    have : (2 * Real.pi) ^ 11 / 2 * A ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    linarith
  have hSpos : 0 < S := entropy_pos_of_energy_pos ρ hρ hApos
  rw [globalTransition_eq_manuscript_quotient (by norm_num : 0 < 11)]
  have hmem : 2 * S / (kernelConstant 11 * A) ∈
      {q | ∃ ρ : ProbabilityDensity 11, ρ.FiniteEntropy ∧ 0 < (torusEntropy ρ.value).toReal ∧
        q = 2 * (torusEntropy ρ.value).toReal /
          (kernelConstant 11 * (negSobolevEnergy ρ.value).toReal)} :=
    ⟨ρ, hρ, hSpos, rfl⟩
  have hbdd : BddBelow {q | ∃ ρ : ProbabilityDensity 11, ρ.FiniteEntropy ∧
      0 < (torusEntropy ρ.value).toReal ∧ q = 2 * (torusEntropy ρ.value).toReal /
        (kernelConstant 11 * (negSobolevEnergy ρ.value).toReal)} := by
    refine ⟨0, ?_⟩
    rintro q ⟨σ, -, hσ, rfl⟩
    exact div_nonneg (by linarith) (mul_nonneg hc.le ENNReal.toReal_nonneg)
  refine (csInf_le hbdd hmem).trans_lt ?_
  -- `2 S / (c A) = S β_s / ((2π)^{11} A / 2)`
  have hcA : 0 < kernelConstant 11 * A := mul_pos hc hApos
  rw [div_lt_iff₀ hcA]
  have hpi : Real.pi ^ 5 < ((104348 : ℝ) / 33215) ^ 5 := by
    gcongr
    exact HighDim.Eleven.pi_fine_bounds.2
  have hsig : spectralThreshold 11 < (64 : ℝ) / 945 * (104348 / 33215) ^ 5 := by
    rw [HighDim.Eleven.spectralThreshold_eleven]
    nlinarith
  -- c = (2π)^11 / β_s
  have hc' : kernelConstant 11 = (2 * Real.pi) ^ 11 / spectralThreshold 11 := by
    rw [← hcs]; field_simp
  rw [hc']
  have hpow : 0 < (2 * Real.pi) ^ 11 := by positivity
  -- reduce to `2 S β_s < (2063/100) (2π)^11 A`
  have key : 2 * S * spectralThreshold 11 < 2063 / 100 * ((2 * Real.pi) ^ 11 * A) := by
    have h1 : 2 * S * spectralThreshold 11 <
        2 * (7305164 / 10 ^ 6 + 17897 / 2520 + 1 / 600) * ((64 : ℝ) / 945 * (104348 / 33215) ^ 5) := by
      have hS' := mul_lt_mul_of_pos_right he (by norm_num : (0 : ℝ) < 2)
      have := mul_lt_mul'' hS' hsig (by positivity) hs.le
      nlinarith
    have h2 : 2 * (7305164 / 10 ^ 6 + 17897 / 2520 + 1 / 600) *
        ((64 : ℝ) / 945 * (104348 / 33215) ^ 5) < 2063 / 100 * (2 * (14475384292906 / 10 ^ 12)) := by
      norm_num
    nlinarith
  calc 2 * S = 2 * S * spectralThreshold 11 / spectralThreshold 11 := by field_simp
    _ < 2063 / 100 * ((2 * Real.pi) ^ 11 * A) / spectralThreshold 11 :=
        div_lt_div_of_pos_right key hs
    _ = 2063 / 100 * ((2 * Real.pi) ^ 11 / spectralThreshold 11 * A) := by ring

/-- The upper bound `β_gm(11) < 2063/100` for the periodized profile `ρ_*`, using only the printed
entropy bound `Ent(ρ_*) < 7305164/10^6 + 17897/2520 + 1/600` and the energy bound `eq:d11:upper`. -/
theorem transition_upper (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    VariationalCurves.globalTransition 11 < 2063 / 100 :=
  globalTransition_lt_of_competitor ρ (finiteEntropy_of_value_eq ρ h)
    (periodized_entropy_fine ρ h) (periodized_energy_bound ρ h)

/-- `2063/100 < β_s(11) < 22` (`eq:section4-transition-spectral-chain`). -/
theorem upper_lt_spectral : (2063 : ℝ) / 100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 :=
  HighDim.Eleven.spectralThreshold_bounds

/-- `β_gm(11) = Eleven.globalTransition` (definitional). -/
theorem globalTransition_eq_eleven :
    VariationalCurves.globalTransition 11 = HighDim.Eleven.globalTransition := rfl

/-! ## `P_11(β_s) > 4/75 > 1/30` and `C_11(A_s) = P_11(β_s)` -/

/-- Real form of the free energy (manuscript normalization), `d > 0`. -/
theorem pressureValue_eq_real_ms {d : ℕ} (hd : 0 < d) (β : ℝ) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    pressureValue β ρ =
      ((β * kernelConstant d / 2 * (negSobolevEnergy ρ.value).toReal -
        (torusEntropy ρ.value).toReal : ℝ) : EReal) := by
  have hN : negSobolevEnergy ρ.value ≠ ∞ :=
    (negSobolevEnergy_ne_top_iff ρ).2 (finiteEntropy_spectralEnergy_ne_top hd ρ hρ)
  have hent : torusEntropy ρ.value ≠ ∞ := (torusEntropy_density_ne_top_iff ρ).2 hρ
  rw [pressureValue_eq_manuscript hd β ρ hρ, ← EReal.coe_ennreal_toReal hN,
    ← EReal.coe_ennreal_toReal hent, ← EReal.coe_mul, ← EReal.coe_sub]

/-- `(2π)^{11}/2 ‖ρ_*‖² - Ent(ρ_*) > 579/40 - 8653/600 = 4/75`. -/
theorem free_energy_spectral_gt (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (4 : ℝ) / 75 < (2 * Real.pi) ^ 11 / 2 * (negSobolevEnergy ρ.value).toReal -
      (torusEntropy ρ.value).toReal := by
  have h1 := periodized_energy_bound ρ h
  have h2 := periodized_entropy_bound ρ h
  have h3 : (579 : ℝ) / 40 < 14475384292906 / 10 ^ 12 := by norm_num
  linarith

/-- `P_11(β_s) ≥ (2π)^{11}/2 ‖ρ_*‖² - Ent(ρ_*) > 4/75`
(`eq:section4-positive-spectral-pressure`, first inequality). -/
theorem spectral_pressure_gt (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (((4 : ℝ) / 75 : ℝ) : EReal) < pressure 11 (spectralThreshold 11) := by
  have hρ := finiteEntropy_of_value_eq ρ h
  have hv := HighDim.Eleven.pressureValue_le_pressure (spectralThreshold 11) ρ hρ
  rw [pressureValue_eq_real_ms (by norm_num) _ ρ hρ] at hv
  have hcs := kernelConstant_mul_spectralThreshold (d := 11) (by norm_num)
  have e : spectralThreshold 11 * kernelConstant 11 / 2 *
      (negSobolevEnergy ρ.value).toReal = (2 * Real.pi) ^ 11 / 2 * (negSobolevEnergy ρ.value).toReal := by
    rw [mul_comm (spectralThreshold 11), hcs]
  rw [e] at hv
  refine lt_of_lt_of_le ?_ hv
  exact EReal.coe_lt_coe_iff.mpr (free_energy_spectral_gt ρ h)

theorem spectral_pressure_gt_thirtieth (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (((1 : ℝ) / 30 : ℝ) : EReal) < pressure 11 (spectralThreshold 11) :=
  lt_trans (EReal.coe_lt_coe_iff.mpr (by norm_num)) (spectral_pressure_gt ρ h)

/-- `C_11(A_s(11)) = P_11(β_s(11))` (`eq:section2-coefficient-pressure-duality` at `A = A_s`). -/
theorem defect_spectral_eq_pressure :
    coefficientDefect 11 (spectralCoefficient 11) = pressure 11 (spectralThreshold 11) := by
  have hc := kernelConstant_pos (d := 11) (by norm_num)
  have hA : 0 < spectralCoefficient 11 := by unfold spectralCoefficient; positivity
  rw [coefficient_pressure_duality (by norm_num) hA]
  congr 1
  have hcs := kernelConstant_mul_spectralThreshold (d := 11) (by norm_num)
  have hs := spectralThreshold_pos' (d := 11) (by norm_num)
  unfold spectralCoefficient
  rw [← hcs]
  field_simp

/-- `C_11(A_s(11)) = P_11(β_s(11)) > 1/30` (first display of `eq:intro-d11-threshold`). -/
theorem spectral_defect_gt (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (((1 : ℝ) / 30 : ℝ) : EReal) < coefficientDefect 11 (spectralCoefficient 11) := by
  rw [defect_spectral_eq_pressure]
  exact spectral_pressure_gt_thirtieth ρ h

end BecknerOnofri.V2.Eleven
