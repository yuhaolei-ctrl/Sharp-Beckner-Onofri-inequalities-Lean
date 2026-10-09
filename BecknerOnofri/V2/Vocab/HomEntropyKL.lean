module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import BecknerOnofri.V2.Vocab.HomEntropy

@[expose] public section

/-! # Entropy of a probability measure relative to a probability measure

`eq:section2-relative-entropy` and the sentence after it: for a probability measure `ν ≪ μ` the
entropy relative to `μ` is `Ent_μ(dν/dμ)`; otherwise it is `+∞`. At unit mass this is Mathlib's
`InformationTheory.klDiv ν μ`. (For a *non-normalized* finite measure `ν`, `klDiv ν μ` is
`∫ klFun (dν/dμ)` which differs from `homEntropy` by the term `(1 - m)`; the two agree only at
mass one, which is why the bridge below is stated for probability measures only.) -/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Vocab

variable {α : Type*} [MeasurableSpace α]

open scoped Classical in
/-- Entropy of the probability measure `ν` relative to `μ`. -/
def measureEntropy (ν μ : Measure α) : ℝ≥0∞ :=
  if ν ≪ μ then homEntropy μ (fun x => (ν.rnDeriv μ x).toReal) else ∞

variable {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
lemma measureEntropy_of_not_ac (h : ¬ ν ≪ μ) : measureEntropy ν μ = ∞ := by
  simp only [measureEntropy, h, ↓reduceIte]


omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- The measure with density `g` (for `g` of unit mass) is a probability measure. -/
lemma isProbabilityMeasure_withDensity {g : α → ℝ} (hg : FiniteMassDomain μ g)
    (hmass : ∫ x, g x ∂μ = 1) : IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (g x)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hg.integrable hg.nonneg, hmass, ENNReal.ofReal_one]

omit [IsProbabilityMeasure ν] in
/-- The measure `g μ` is absolutely continuous with respect to `μ`, with Radon--Nikodym density
`g` a.e. (no measurability of `g` beyond `FiniteMassDomain` is needed). -/
lemma rnDeriv_withDensity_toReal {g : α → ℝ} (hg : FiniteMassDomain μ g) :
    (fun x => ((μ.withDensity fun y => ENNReal.ofReal (g y)).rnDeriv μ x).toReal) =ᵐ[μ] g := by
  have hmk : AEMeasurable (fun y => ENNReal.ofReal (g y)) μ :=
    hg.integrable.aemeasurable.ennreal_ofReal
  have h1 : (μ.withDensity fun y => ENNReal.ofReal (g y)) = μ.withDensity hmk.mk :=
    withDensity_congr_ae hmk.ae_eq_mk
  rw [h1]
  filter_upwards [Measure.rnDeriv_withDensity μ hmk.measurable_mk, hmk.ae_eq_mk, hg.nonneg]
    with x h2 h3 h4
  rw [h2, ← h3, ENNReal.toReal_ofReal h4]

omit [IsProbabilityMeasure ν] in
/-- The entropy of the measure `g μ` relative to `μ` is `Ent_μ(g)` (for any `g` in the domain). -/
theorem measureEntropy_withDensity {g : α → ℝ} (hg : FiniteMassDomain μ g) :
    measureEntropy (μ.withDensity fun x => ENNReal.ofReal (g x)) μ = homEntropy μ g := by
  have hac : (μ.withDensity fun x => ENNReal.ofReal (g x)) ≪ μ := withDensity_absolutelyContinuous _ _
  simp only [measureEntropy, hac, ↓reduceIte]
  exact homEntropy_congr_ae (rnDeriv_withDensity_toReal hg)

/-- Bridge to Mathlib's Kullback–Leibler divergence (unit mass, both cases). -/
theorem measureEntropy_eq_klDiv : measureEntropy ν μ = klDiv ν μ := by
  by_cases hac : ν ≪ μ
  · simp only [measureEntropy, hac, ↓reduceIte]
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    have hm : ∫ x, (ν.rnDeriv μ x).toReal ∂μ = 1 := by
      rw [Measure.integral_toReal_rnDeriv hac]
      simp
    rw [homEntropy_of_mass_one hm]
    apply lintegral_congr
    intro x
    congr 1
    simp only [klFun_apply]
    ring
  · rw [measureEntropy_of_not_ac hac, klDiv_of_not_ac hac]

end BecknerOnofri.V2.Vocab
