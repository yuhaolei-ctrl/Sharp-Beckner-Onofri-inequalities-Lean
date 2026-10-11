module

public import BecknerOnofri.V2.Transfer.DimensionTransfer
public import BecknerOnofri.V2.Transfer.Transport
public import BecknerOnofri.V2.Rearrangement.Comparison
public import BecknerOnofri.V2.Reaudit.Attainment.Main
public import BecknerOnofri.GeneralEuler.Paper
public import BecknerOnofri.OptimizerDuality
public import BecknerOnofri.SubcriticalGap
public import BecknerOnofri.Uniform

@[expose] public section

/-! # Proposition 5.7 along the written proof (`prop:spectral-dimension-transfer`)

This file formalizes the argument as written in the manuscript, in addition to the repository route of
`DimensionTransfer.lean` (which inducts `d → d+1` through `mixture_rigidity_successor`).  The chain is

1. a minimizing cosine mixture `ρ̃` of `Ent - ½ E` at the spectral coupling `β = β_s(d)`
   (Lemma 2.13: `exists_minimizer`, smooth Gibbs form, coordinate rearrangement
   `coordinate_rearranged_minimizer`, cosine representation);
2. Proposition 5.5 at `r = 12`: `E(ρ̃) ≤ d/(12 C(d,12)) ∑_{|I|=12} E_12(ρ̃_I)`;
3. the `d = 12` hypothesis applied to the transported `12`-marginals `ρ_I` (`Transport.lean`):
   `E_12(ρ̃_I) ≤ 2 Ent(ρ_I)`;
4. Lemma 5.2 at `r = 12`: `d/(12 C(d,12)) ∑_I Ent(ρ_I) ≤ Ent(ρ̃)`;
5. transfer back to arbitrary finite-entropy densities via the minimizing mixture;
6. equality: a density with equality is a global minimizer at `β_s`; its selected mixture has equality,
   all deficits vanish, the `12`-equality hypothesis makes each marginal uniform, so the (nonnegative)
   Fourier contributions of the marginals vanish, hence `E(ρ̃) = 0`, `Ent(ρ̃) = 0` and `ρ = 1`.

Nothing here refers to `mixture_rigidity_successor`, `mixture_rigidity_from_twelve`,
`mixture_endpoint_successor` or the other `d → d+1` induction steps; see `RESOLUTION.md`. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Transfer
open BecknerOnofri.HighDim

/-! ## Selection of a continuous minimizing cosine mixture (Lemma 2.13) -/

/-- A density with the same a.e. class as a smooth strictly positive function. -/
def densityOfSmooth' {d : ℕ} (ρ : ProbabilityDensity d) {q : Torus d → ℝ}
    (hq : ρ.value =ᵐ[torusMeasure d] q) (hqs : SmoothOnTorus q) (hqpos : ∀ x, 0 < q x) :
    ProbabilityDensity d where
  value := q
  nonneg := Filter.Eventually.of_forall fun x => (hqpos x).le
  integrable := by
    obtain ⟨K, hK⟩ := hqs.exists_lipschitz
    exact hK.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  mass := by rw [← integral_congr_ae hq]; exact ρ.mass

/-- **Lemma 2.13, selected mixture.**  A global minimizer at coupling `β > 0` can be replaced by a
continuous countable cosine-power mixture that is again a global minimizer with the same entropy and
the same value of the pressure functional. -/
theorem mixture_of_minimizer {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) :
    ∃ η : ProbabilityDensity d, IsCountableCosineMixture η ∧ Continuous η.value ∧
      IsGlobalMinimizer β η ∧ entropy η = entropy ρ ∧ pressureValue β η = pressureValue β ρ := by
  obtain ⟨⟨q, hq, hqs, hqpos⟩, -, -⟩ :=
    OptimizerDuality.minimizer_smooth_positive_kirkwood hd hβ ρ hρ
  let ρq := densityOfSmooth' ρ hq hqs hqpos
  have hae : ρ.value =ᵐ[torusMeasure d] ρq.value := hq
  have hρq : IsGlobalMinimizer β ρq := (OptimizerDuality.minimizer_congr_ae hae β).1 hρ
  obtain ⟨η, u, -, hηmin, -, -, -, -, hent, hpv, hgu, hηs, -, hus, hm, -, -, heuler, -, hstu⟩ :=
    BecknerOnofri.V2.Rearrangement.coordinate_rearranged_minimizer hd hβ ρq hρq hqs
  obtain ⟨U, -, -, -, hηmix⟩ := GeneralEulerBridge.cosine_representation hd β hβ u η hus hm hstu
    hgu heuler
  obtain ⟨K, hK⟩ := hηs.exists_lipschitz
  refine ⟨η, hηmix, hK.continuous, hηmin, ?_, ?_⟩
  · rw [hent]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    show ρq.value x * Real.log (ρq.value x) = ρ.value x * Real.log (ρ.value x)
    rw [← hx]
  · rw [hpv]
    exact (OptimizerDuality.pressureValue_congr_ae hae β).symm

/-- Every finite-entropy density is dominated, for the pressure functional at the spectral coupling, by a
continuous countable cosine mixture that is a global minimizer. -/
theorem exists_mixture_ge {d : ℕ} (hd : 12 ≤ d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    ∃ η : ProbabilityDensity d, IsCountableCosineMixture η ∧ Continuous η.value ∧
      IsGlobalMinimizer (spectralThreshold d) η ∧
      pressureValue (spectralThreshold d) ρ ≤ pressureValue (spectralThreshold d) η := by
  have hd0 : 0 < d := by omega
  have hβ : 0 < spectralThreshold d := spectralThreshold_pos hd0
  obtain ⟨ρ0, h0⟩ := (BecknerOnofri.V2.Reaudit.Attainment.subcritical_attainment hd0 hβ
    (spectral_subcritical_gap hd)).2.1
  obtain ⟨η, hmix, hc, hmin, -, hpv⟩ := mixture_of_minimizer hd0 hβ ρ0 h0
  exact ⟨η, hmix, hc, hmin, (h0.2 ρ hρ).trans_eq hpv.symm⟩

/-! ## The pressure functional at the spectral coupling in real form -/

/-- `Ent - ½ E` in real form. -/
def freeGap {d : ℕ} (σ : ProbabilityDensity d) : ℝ :=
  (spectralEnergy σ).toReal / 2 - entropy σ

theorem pressureValue_spectral {d : ℕ} (hd : 0 < d) (σ : ProbabilityDensity d)
    (hσ : σ.FiniteEntropy) :
    pressureValue (spectralThreshold d) σ = ((freeGap σ : ℝ) : EReal) := by
  have hpos := spectralThreshold_pos hd
  have hne := finiteEntropy_spectralEnergy_ne_top hd σ hσ
  have hcoef : spectralThreshold d / (2 * spectralThreshold d) = 1 / 2 := by
    field_simp
  unfold pressureValue freeGap
  rw [hcoef, ← EReal.coe_ennreal_toReal hne, ← EReal.coe_mul, ← EReal.coe_sub]
  congr 1
  ring

/-! ## Marginal facts from the dimension-twelve hypothesis -/

/-- The dimension-twelve inequality for the transported `12`-marginal. -/
theorem marginal_energy_le (h12 : SpectralD12Inequality) {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : IsCountableCosineMixture ρ) (hc : Continuous ρ.value) (I : Finset (Fin d))
    (hI : I.card = 12) :
    inversePowerEnergy 12 (coordinateMarginal ρ I) ≤
        ENNReal.ofReal (2 * coordinateMarginalEntropy ρ I) ∧
      0 ≤ coordinateMarginalEntropy ρ I := by
  obtain ⟨ρ', hfin, hE, hS⟩ := exists_marginal_density (r := 12) (by norm_num) ρ hρ hc I hI
  refine ⟨?_, ?_⟩
  · have h := h12 ρ' hfin
    rwa [hE, hS] at h
  · rw [← hS]; exact entropy_nonneg ρ' hfin

/-- The dimension-twelve equality case for the transported `12`-marginal: equality forces the marginal to
have vanishing (nonnegative) Fourier energy. -/
theorem marginal_energy_eq_zero (hEq : SpectralD12Equality) {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : IsCountableCosineMixture ρ) (hc : Continuous ρ.value) (I : Finset (Fin d))
    (hI : I.card = 12)
    (h : inversePowerEnergy 12 (coordinateMarginal ρ I) =
      ENNReal.ofReal (2 * coordinateMarginalEntropy ρ I)) :
    inversePowerEnergy 12 (coordinateMarginal ρ I) = 0 := by
  obtain ⟨ρ', hfin, hE, hS⟩ := exists_marginal_density (r := 12) (by norm_num) ρ hρ hc I hI
  have hsp : spectralEnergy ρ' = ENNReal.ofReal (2 * entropy ρ') := by rw [hE, hS, h]
  have hone := hEq ρ' hfin hsp
  have h0 : entropy ρ' = 0 := (entropy_eq_zero_iff ρ' hfin).2 hone
  rw [h, ← hS, h0]
  simp

/-! ## The chain of the written proof -/

/-- The coefficient `d / (12 C(d,12))` of Proposition 5.5 and Lemma 5.2 at `r = 12`. -/
def subsetCoeff (d : ℕ) : ℝ := (d : ℝ) / (((12 : ℕ) : ℝ) * (d.choose 12 : ℝ))

theorem subsetCoeff_pos {d : ℕ} (hd : 12 ≤ d) : 0 < subsetCoeff d := by
  unfold subsetCoeff
  have h1 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h2 : (0 : ℝ) < (d.choose 12 : ℝ) := by exact_mod_cast Nat.choose_pos hd
  positivity

/-- Real form of the three displays of the chain.  `a I` is the (finite) `12`-energy of the `I`-marginal. -/
theorem chain_real (h12 : SpectralD12Inequality) {d : ℕ} (hd : 12 ≤ d) (ρ : ProbabilityDensity d)
    (hmix : IsCountableCosineMixture ρ) (hc : Continuous ρ.value) (hfin : ρ.FiniteEntropy) :
    ∃ a : Finset (Fin d) → ℝ,
      (∀ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12,
        0 ≤ a I ∧ a I ≤ 2 * coordinateMarginalEntropy ρ I ∧
          inversePowerEnergy 12 (coordinateMarginal ρ I) = ENNReal.ofReal (a I)) ∧
      (spectralEnergy ρ).toReal ≤
        subsetCoeff d * ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12, a I ∧
      subsetCoeff d * ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12,
          2 * coordinateMarginalEntropy ρ I ≤ 2 * entropy ρ := by
  have hcpos := subsetCoeff_pos hd
  refine ⟨fun I => (inversePowerEnergy 12 (coordinateMarginal ρ I)).toReal, ?_, ?_, ?_⟩
  · intro I hI
    have hcard := (Finset.mem_powersetCard.mp hI).2
    obtain ⟨hle, hent⟩ := marginal_energy_le h12 ρ hmix hc I hcard
    have hne : inversePowerEnergy 12 (coordinateMarginal ρ I) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    refine ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by linarith) hle, ?_⟩
    exact (ENNReal.ofReal_toReal hne).symm
  · have h55 := spectral_marginal_energy_subset (r := 12) le_rfl hd ρ hmix
    have hnetop : ∀ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12,
        inversePowerEnergy 12 (coordinateMarginal ρ I) ≠ ⊤ := by
      intro I hI
      have hcard := (Finset.mem_powersetCard.mp hI).2
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (marginal_energy_le h12 ρ hmix hc I hcard).1
    have hrhs : ENNReal.ofReal ((d : ℝ) / (((12 : ℕ) : ℝ) * (d.choose 12 : ℝ))) *
        ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12,
          inversePowerEnergy 12 (coordinateMarginal ρ I) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr hnetop)
    have h := ENNReal.toReal_mono hrhs h55
    have hc0 : 0 ≤ (d : ℝ) / (((12 : ℕ) : ℝ) * (d.choose 12 : ℝ)) := hcpos.le
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0, ENNReal.toReal_sum hnetop] at h
    exact h
  · have h52 := (spectral_subset_entropy (r := 12) (by norm_num) hd ρ hfin).2
    have : subsetCoeff d * ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12,
        2 * coordinateMarginalEntropy ρ I =
        2 * ((d : ℝ) / (((12 : ℕ) : ℝ) * (d.choose 12 : ℝ)) *
          ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12, coordinateMarginalEntropy ρ I) := by
      rw [← Finset.mul_sum]
      unfold subsetCoeff
      ring
    rw [this]
    linarith

/-- **Written proof, inequality for mixtures.**  A continuous finite-entropy countable cosine mixture on
`𝕋^d`, `d ≥ 12`, satisfies `E(ρ) ≤ 2 Ent(ρ)`. -/
theorem mixture_energy_le_written (h12 : SpectralD12Inequality) {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hmix : IsCountableCosineMixture ρ) (hc : Continuous ρ.value)
    (hfin : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) := by
  have hcpos := subsetCoeff_pos hd
  obtain ⟨a, ha, h1, h2⟩ := chain_real h12 hd ρ hmix hc hfin
  have hsum : ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12, a I ≤
      ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12, 2 * coordinateMarginalEntropy ρ I :=
    Finset.sum_le_sum (fun I hI => (ha I hI).2.1)
  have hreal : (spectralEnergy ρ).toReal ≤ 2 * entropy ρ :=
    h1.trans ((mul_le_mul_of_nonneg_left hsum hcpos.le).trans h2)
  have hne := finiteEntropy_spectralEnergy_ne_top (by omega) ρ hfin
  calc spectralEnergy ρ = ENNReal.ofReal (spectralEnergy ρ).toReal := (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal (2 * entropy ρ) := ENNReal.ofReal_le_ofReal hreal

/-- **Written proof, equality for mixtures.**  If a continuous finite-entropy countable cosine mixture
attains equality, all `12`-marginal deficits vanish, each marginal is uniform by the `d = 12` equality
case, the Fourier contributions of all marginals vanish, hence `E(ρ) = 0` and `Ent(ρ) = 0`. -/
theorem mixture_entropy_zero_of_equality_written (h12 : SpectralD12Inequality)
    (hEq : SpectralD12Equality) {d : ℕ} (hd : 12 ≤ d) (ρ : ProbabilityDensity d)
    (hmix : IsCountableCosineMixture ρ) (hc : Continuous ρ.value) (hfin : ρ.FiniteEntropy)
    (hE : spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ)) :
    entropy ρ = 0 := by
  have hcpos := subsetCoeff_pos hd
  obtain ⟨a, ha, h1, h2⟩ := chain_real h12 hd ρ hmix hc hfin
  have hent := entropy_nonneg ρ hfin
  have hEreal : (spectralEnergy ρ).toReal = 2 * entropy ρ := by
    rw [hE, ENNReal.toReal_ofReal (by linarith)]
  have hsum : ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12, a I ≤
      ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12, 2 * coordinateMarginalEntropy ρ I :=
    Finset.sum_le_sum (fun I hI => (ha I hI).2.1)
  have hmid := mul_le_mul_of_nonneg_left hsum hcpos.le
  -- every inequality of the chain is an equality
  have hsumeq : ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12, a I =
      ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12, 2 * coordinateMarginalEntropy ρ I := by
    have hle : subsetCoeff d * ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12,
        2 * coordinateMarginalEntropy ρ I ≤
        subsetCoeff d * ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12, a I := by
      linarith
    exact le_antisymm hsum (le_of_mul_le_mul_left hle hcpos)
  have hI0 : ∀ I ∈ (Finset.univ : Finset (Fin d)).powersetCard 12,
      inversePowerEnergy 12 (coordinateMarginal ρ I) = 0 := by
    intro I hI
    have hcard := (Finset.mem_powersetCard.mp hI).2
    have hdiff : ∑ J ∈ (Finset.univ : Finset (Fin d)).powersetCard 12,
        (2 * coordinateMarginalEntropy ρ J - a J) = 0 := by
      rw [Finset.sum_sub_distrib, hsumeq, sub_self]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun J hJ => sub_nonneg.mpr (ha J hJ).2.1)).mp hdiff I hI
    have heq : a I = 2 * coordinateMarginalEntropy ρ I := by linarith
    apply marginal_energy_eq_zero hEq ρ hmix hc I hcard
    rw [(ha I hI).2.2, heq]
  have h0 := (mixture_energy_vanishes_of_marginals (r := 12) le_rfl hd ρ hmix hI0).1
  rw [h0] at hE
  have : 2 * entropy ρ ≤ 0 := ENNReal.ofReal_eq_zero.mp hE.symm
  linarith

/-! ## Proposition 5.7 along the written proof -/

theorem ae_one_spectralEnergy {d : ℕ} (ρ : ProbabilityDensity d)
    (h : ρ.value =ᵐ[torusMeasure d] fun _ => 1) : spectralEnergy ρ = 0 := by
  unfold spectralEnergy
  refine ENNReal.tsum_eq_zero.mpr (fun k => ?_)
  unfold spectralTerm
  rw [fourierCoeff_congr_ae h, fourierCoeff_one_nonzero k.val k.property]
  simp

/-- Every finite-entropy density satisfies the transferred inequality (written route). -/
theorem spectral_dimension_transfer_inequality_written (h12 : SpectralD12Inequality) {d : ℕ}
    (hd : 12 ≤ d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) := by
  have hd0 : 0 < d := by omega
  obtain ⟨η, hmix, hc, hmin, hle⟩ := exists_mixture_ge hd ρ hρ
  have hηfin := hmin.1
  have hη := mixture_energy_le_written h12 hd η hmix hc hηfin
  have hηreal : (spectralEnergy η).toReal ≤ 2 * entropy η := by
    have hne := finiteEntropy_spectralEnergy_ne_top hd0 η hηfin
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hη
    rwa [ENNReal.toReal_ofReal (by linarith [entropy_nonneg η hηfin])] at this
  rw [pressureValue_spectral hd0 ρ hρ, pressureValue_spectral hd0 η hηfin, EReal.coe_le_coe_iff]
    at hle
  have hρreal : (spectralEnergy ρ).toReal ≤ 2 * entropy ρ := by
    unfold freeGap at hle
    linarith
  have hne := finiteEntropy_spectralEnergy_ne_top hd0 ρ hρ
  calc spectralEnergy ρ = ENNReal.ofReal (spectralEnergy ρ).toReal := (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal (2 * entropy ρ) := ENNReal.ofReal_le_ofReal hρreal

/-- Equality case (written route). -/
theorem spectral_dimension_transfer_equality_written (h12 : SpectralD12Inequality)
    (hEq : SpectralD12Equality) {d : ℕ} (hd : 12 ≤ d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔ ρ.value =ᵐ[torusMeasure d] fun _ => 1 := by
  have hd0 : 0 < d := by omega
  have hβ : 0 < spectralThreshold d := spectralThreshold_pos hd0
  constructor
  · intro hE
    have hent := entropy_nonneg ρ hρ
    have hEreal : (spectralEnergy ρ).toReal = 2 * entropy ρ := by
      rw [hE, ENNReal.toReal_ofReal (by linarith)]
    have hgap : freeGap ρ = 0 := by unfold freeGap; linarith
    -- ρ is a global minimizer at the spectral coupling
    have hmin : IsGlobalMinimizer (spectralThreshold d) ρ := by
      refine ⟨hρ, fun σ hσ => ?_⟩
      have hs := spectral_dimension_transfer_inequality_written h12 hd σ hσ
      have hne := finiteEntropy_spectralEnergy_ne_top hd0 σ hσ
      have hσreal : (spectralEnergy σ).toReal ≤ 2 * entropy σ := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
        rwa [ENNReal.toReal_ofReal (by linarith [entropy_nonneg σ hσ])] at this
      rw [pressureValue_spectral hd0 σ hσ, pressureValue_spectral hd0 ρ hρ, EReal.coe_le_coe_iff,
        hgap]
      unfold freeGap
      linarith
    obtain ⟨η, hmix, hc, hηmin, hent', hpv⟩ := mixture_of_minimizer hd0 hβ ρ hmin
    have hηfin := hηmin.1
    rw [pressureValue_spectral hd0 η hηfin, pressureValue_spectral hd0 ρ hρ, EReal.coe_eq_coe_iff,
      hgap] at hpv
    have hηE : spectralEnergy η = ENNReal.ofReal (2 * entropy η) := by
      have hne := finiteEntropy_spectralEnergy_ne_top hd0 η hηfin
      have hreal : (spectralEnergy η).toReal = 2 * entropy η := by
        unfold freeGap at hpv
        linarith
      rw [← hreal, ENNReal.ofReal_toReal hne]
    have h0 := mixture_entropy_zero_of_equality_written h12 hEq hd η hmix hc hηfin hηE
    exact (entropy_eq_zero_iff ρ hρ).1 (by rw [← hent', h0])
  · intro h
    have h0 : entropy ρ = 0 := (entropy_eq_zero_iff ρ hρ).2 h
    rw [ae_one_spectralEnergy ρ h, h0]
    simp

/-- **Proposition 5.7, written proof.**  Same hypotheses and conclusion as `spectral_dimension_transfer`,
proved along the manuscript chain (selected minimizing mixture, Proposition 5.5 and Lemma 5.2 at `r = 12`,
the `d = 12` hypotheses on the transported `12`-marginals) without the `d → d+1` induction. -/
theorem spectral_dimension_transfer_written (h12 : SpectralD12Inequality)
    (hEq : SpectralD12Equality) {d : ℕ} (hd : 12 ≤ d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
      (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
        ρ.value =ᵐ[torusMeasure d] fun _ => 1) :=
  ⟨spectral_dimension_transfer_inequality_written h12 hd ρ hρ,
    spectral_dimension_transfer_equality_written h12 hEq hd ρ hρ⟩

/-- The written-route theorem and the repository-route theorem state, and hence prove, the same
proposition: their statements agree, and their conclusions coincide for every input. -/
theorem spectral_dimension_transfer_written_agree (h12 : SpectralD12Inequality)
    (hEq : SpectralD12Equality) {d : ℕ} (hd : 12 ≤ d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    spectral_dimension_transfer_written h12 hEq hd ρ hρ = spectral_dimension_transfer h12 hEq hd ρ hρ :=
  rfl

/-- The two theorems have literally the same statement. -/
theorem spectral_dimension_transfer_written_statement_eq :
    (type_of% @spectral_dimension_transfer_written) = (type_of% @spectral_dimension_transfer) :=
  rfl

end BecknerOnofri.V2.Transfer
