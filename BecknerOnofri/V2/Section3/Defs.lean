module

public import BecknerOnofri.V2.Rearrangement.Comparison
public import BecknerOnofri.V2.Vocab.Section2Heat
public import BecknerOnofri.V2.Vocab.Section2Gibbs
public import BecknerOnofri.CanonicalSelectionFullDomain
public import BecknerOnofri.GeneralEuler.Paper

@[expose] public section

/-! # Section 3 (G04): vocabulary and real-form interfaces

Everything in `BecknerOnofri.V2.Section3` is stated with the manuscript normalization:

* `Ent ρ = (torusEntropy ρ.value).toReal` (`= entropy ρ` for finite entropy),
* `c_d ‖ρ‖²_{Ḣ^{-d/2}} = kernelConstant d * (negSobolevEnergy ρ.value).toReal`,
* the entropy bound of the section is `EntropyBound d ρ : d c_d ‖ρ‖² ≤ Ent ρ`
  (`eq:collapse-entropy-full`), the equality statement `EntropyEquality`.

`MixtureInequality d` / `MixtureStrictness d` are the two inputs of Lemma 3.1
(`lem:collapse-conditional-reduction`), quantified over **every** finite-entropy countable
cosine-power mixture, exactly as in the manuscript.  The proof of Lemma 3.1 only ever applies them to
*smooth strictly positive* mixtures; `SmoothMixtureInequality` / `SmoothMixtureStrictness` are the
(weaker) hypotheses restricted to that subclass, and `Lemma31.lean` proves the lemma from these
weaker hypotheses (so the manuscript statement follows a fortiori: `MixtureInequality.toSmooth`). -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

/-- `d c_d ‖ρ‖²_{Ḣ^{-d/2}} ≤ Ent ρ` (`eq:collapse-entropy-full`), in real form. -/
def EntropyBound (d : ℕ) (ρ : ProbabilityDensity d) : Prop :=
  (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal ≤ (torusEntropy ρ.value).toReal

/-- Equality in `eq:collapse-entropy-full`. -/
def EntropyEquality (d : ℕ) (ρ : ProbabilityDensity d) : Prop :=
  (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal = (torusEntropy ρ.value).toReal

/-- Strict inequality `d c_d ‖ρ‖² < Ent ρ`. -/
def EntropyStrict (d : ℕ) (ρ : ProbabilityDensity d) : Prop :=
  (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal < (torusEntropy ρ.value).toReal

/-- **First hypothesis of Lemma 3.1.**  Every finite-entropy countable cosine-power mixture
satisfies `Ent(ρ) ≥ d c_d ‖ρ‖²`. -/
def MixtureInequality (d : ℕ) : Prop :=
  ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → IsCountableCosineMixture ρ → EntropyBound d ρ

/-- **Second hypothesis of Lemma 3.1.**  The inequality is strict for every nonuniform
finite-entropy countable cosine-power mixture. -/
def MixtureStrictness (d : ℕ) : Prop :=
  ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → IsCountableCosineMixture ρ →
    ¬ ρ.value =ᵐ[torusMeasure d] (fun _ => 1) → EntropyStrict d ρ

/-- A smooth strictly positive finite-entropy countable cosine-power mixture. -/
def SmoothMixture (ρ : ProbabilityDensity d) : Prop :=
  SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧ IsCountableCosineMixture ρ

/-- `MixtureInequality` restricted to smooth strictly positive mixtures. -/
def SmoothMixtureInequality (d : ℕ) : Prop :=
  ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → SmoothMixture ρ → EntropyBound d ρ

/-- `MixtureStrictness` restricted to smooth strictly positive mixtures. -/
def SmoothMixtureStrictness (d : ℕ) : Prop :=
  ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → SmoothMixture ρ →
    ¬ ρ.value =ᵐ[torusMeasure d] (fun _ => 1) → EntropyStrict d ρ

theorem MixtureInequality.toSmooth (h : MixtureInequality d) : SmoothMixtureInequality d :=
  fun ρ hρ hs => h ρ hρ hs.2.2

theorem MixtureStrictness.toSmooth (h : MixtureStrictness d) : SmoothMixtureStrictness d :=
  fun ρ hρ hs hn => h ρ hρ hs.2.2 hn

/-! ### Real forms of the free energy -/

/-- For a finite-entropy density the free energy is the real number `β c_d/2 ‖ρ‖² - Ent ρ`. -/
theorem pressureValue_eq_real (hd : 0 < d) (β : ℝ) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    pressureValue β ρ =
      ((β * kernelConstant d / 2 * (negSobolevEnergy ρ.value).toReal -
        (torusEntropy ρ.value).toReal : ℝ) : EReal) := by
  have hN : negSobolevEnergy ρ.value ≠ ∞ :=
    (negSobolevEnergy_ne_top_iff ρ).2 (finiteEntropy_spectralEnergy_ne_top hd ρ hρ)
  have hent : torusEntropy ρ.value ≠ ∞ := (torusEntropy_density_ne_top_iff ρ).2 hρ
  rw [pressureValue_eq_manuscript hd β ρ hρ, ← EReal.coe_ennreal_toReal hN,
    ← EReal.coe_ennreal_toReal hent, ← EReal.coe_mul, ← EReal.coe_sub]

/-- Hence `pressureValue β ρ ≤ pressureValue β σ` is a real inequality. -/
theorem pressureValue_le_iff_real (hd : 0 < d) (β : ℝ) (ρ σ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (hσ : σ.FiniteEntropy) :
    pressureValue β ρ ≤ pressureValue β σ ↔
      β * kernelConstant d / 2 * (negSobolevEnergy ρ.value).toReal -
          (torusEntropy ρ.value).toReal ≤
        β * kernelConstant d / 2 * (negSobolevEnergy σ.value).toReal -
          (torusEntropy σ.value).toReal := by
  rw [pressureValue_eq_real hd β ρ hρ, pressureValue_eq_real hd β σ hσ, EReal.coe_le_coe_iff]

/-- At the coupling `β = 2d` the real free energy is `d c_d ‖ρ‖² - Ent ρ`. -/
theorem pressureValue_two_d (hd : 0 < d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    pressureValue (2 * (d : ℝ)) ρ =
      (((d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal -
        (torusEntropy ρ.value).toReal : ℝ) : EReal) := by
  rw [pressureValue_eq_real hd _ ρ hρ]
  congr 2
  ring

theorem entropyBound_iff (hd : 0 < d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    EntropyBound d ρ ↔ pressureValue (2 * (d : ℝ)) ρ ≤ 0 := by
  rw [pressureValue_two_d hd ρ hρ, ← EReal.coe_zero, EReal.coe_le_coe_iff]
  unfold EntropyBound
  constructor <;> intro h <;> linarith

theorem entropy_toReal_nonneg (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    0 ≤ (torusEntropy ρ.value).toReal := by
  rw [← entropy_eq_toReal_torusEntropy ρ hρ]
  exact entropy_nonneg ρ hρ

/-- Neighbouring densities (a.e. equal values) have the same real quantities. -/
theorem negSobolevEnergy_congr_ae {ρ η : ProbabilityDensity d}
    (h : ρ.value =ᵐ[torusMeasure d] η.value) : negSobolevEnergy ρ.value = negSobolevEnergy η.value := by
  unfold negSobolevEnergy
  simp only [BecknerOnofri.V2.Rearrangement.fourierCoeff_congr_ae' h]

theorem torusEntropy_congr_ae {ρ η : ProbabilityDensity d}
    (h : ρ.value =ᵐ[torusMeasure d] η.value) : torusEntropy ρ.value = torusEntropy η.value :=
  homEntropy_congr_ae h

/-- A smooth, strictly positive representative gives a density of finite entropy. -/
theorem finiteEntropy_of_smooth (ρ : ProbabilityDensity d) (hs : SmoothOnTorus ρ.value) :
    ρ.FiniteEntropy := by
  obtain ⟨K, hK⟩ := hs.exists_lipschitz
  have hc : Continuous ρ.value := hK.continuous
  unfold ProbabilityDensity.FiniteEntropy
  exact (Real.continuous_mul_log.comp hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end BecknerOnofri.V2.Section3
