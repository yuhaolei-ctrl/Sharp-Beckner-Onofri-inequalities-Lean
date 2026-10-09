module

public import BecknerOnofri.Entropy
public import BecknerOnofri.V2.Vocab.HomEntropy
public import BecknerOnofri.V2.Vocab.HomEntropyKL

@[expose] public section

/-! # Bridges from the homogeneous entropy to the existing torus entropy vocabulary

At mass one `homEntropy (torusMeasure d) ρ.value` is
* `ENNReal.ofReal (entropy ρ)` when `ρ.FiniteEntropy` (the existing real-valued `entropy`), and
* `⊤` when `¬ ρ.FiniteEntropy`;
and in all cases `extendedEntropy ρ = (homEntropy (torusMeasure d) ρ.value).toEReal`.
The proofs use only `BecknerOnofri.Entropy` / `Definitions` (the vocabulary of `Challenge.lean`)
and `HomEntropy`; in particular nothing from the low-dimensional endpoint development is
imported (the existing `extendedEntropy_eq`/`extendedEntropy_top` live in a module that is). -/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Vocab
open BecknerOnofri.HighDim

/-- A probability density of the repository is in the domain of the homogeneous entropy. -/
lemma finiteMassDomain_density {d : ℕ} (ρ : ProbabilityDensity d) :
    FiniteMassDomain (torusMeasure d) ρ.value :=
  ⟨ρ.nonneg, ρ.integrable⟩

/-- The homogeneous entropy on the torus with respect to normalized Haar measure. -/
abbrev torusEntropy {d : ℕ} (f : Torus d → ℝ) : ℝ≥0∞ := homEntropy (torusMeasure d) f

lemma torusEntropy_density_ne_top_iff {d : ℕ} (ρ : ProbabilityDensity d) :
    torusEntropy ρ.value ≠ ∞ ↔ ρ.FiniteEntropy := by
  rw [← integrable_mul_log_iff (finiteMassDomain_density ρ)]
  rfl

lemma torusEntropy_density_eq_top {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ¬ ρ.FiniteEntropy) :
    torusEntropy ρ.value = ∞ := by
  by_contra h
  exact hρ ((torusEntropy_density_ne_top_iff ρ).1 h)

/-- At mass one, under `FiniteEntropy`, the homogeneous entropy is the existing real `entropy`. -/
lemma torusEntropy_density_eq_ofReal_entropy {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    torusEntropy ρ.value = ENNReal.ofReal (entropy ρ) := by
  have h := homEntropy_eq_ofReal (finiteMassDomain_density ρ) hρ
  rw [ρ.mass, Real.log_one, mul_zero, sub_zero] at h
  exact h

lemma entropy_eq_toReal_torusEntropy {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) : entropy ρ = (torusEntropy ρ.value).toReal := by
  rw [torusEntropy_density_eq_ofReal_entropy ρ hρ, ENNReal.toReal_ofReal (entropy_nonneg ρ hρ)]

/-- `(x + 1) - 1 = x` in `EReal`, including `x = ⊤`. -/
lemma toEReal_add_one_sub_one (x : ℝ≥0∞) : ((x + 1 : ℝ≥0∞) : EReal) - 1 = (x : EReal) := by
  rcases eq_or_ne x ∞ with rfl | hx
  · rw [top_add]
    simpa using EReal.top_sub_coe (1 : ℝ)
  · have hr : 0 ≤ x.toReal := ENNReal.toReal_nonneg
    have e : x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
    have e1 : x + 1 = ENNReal.ofReal (x.toReal + 1) := by
      rw [ENNReal.ofReal_add hr zero_le_one, ENNReal.ofReal_one, ← e]
    rw [e1]
    conv_rhs => rw [e]
    rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, max_eq_left (by linarith),
      max_eq_left hr]
    norm_cast; ring

/-- Pointwise: `ρ log ρ + 1 = (ρ log ρ - ρ + 1) + ρ`, both summands nonnegative. -/
lemma lintegral_shifted_eq {d : ℕ} (ρ : ProbabilityDensity d) :
    ∫⁻ x, ENNReal.ofReal (ρ.value x * Real.log (ρ.value x) + 1) ∂torusMeasure d =
      torusEntropy ρ.value + 1 := by
  have hmass := ρ.mass
  unfold torusEntropy
  rw [homEntropy_of_mass_one hmass]
  have hpt : ∀ᵐ x ∂torusMeasure d,
      ENNReal.ofReal (ρ.value x * Real.log (ρ.value x) + 1) =
        ENNReal.ofReal (ρ.value x * Real.log (ρ.value x) - ρ.value x + 1) +
          ENNReal.ofReal (ρ.value x) := by
    filter_upwards [ρ.nonneg] with x hx
    have h1 : 0 ≤ ρ.value x * Real.log (ρ.value x) - ρ.value x + 1 := by
      have := Real.self_sub_one_le_mul_log hx
      linarith
    rw [← ENNReal.ofReal_add h1 hx]
    congr 1
    ring
  rw [lintegral_congr_ae hpt,
    lintegral_add_right' _ ρ.integrable.aemeasurable.ennreal_ofReal]
  congr 1
  rw [← ofReal_integral_eq_lintegral_ofReal ρ.integrable ρ.nonneg, hmass, ENNReal.ofReal_one]

/-- The existing `extendedEntropy` is the `EReal` image of the homogeneous entropy, on the whole
domain (finite or infinite entropy). -/
theorem extendedEntropy_eq_torusEntropy {d : ℕ} (ρ : ProbabilityDensity d) :
    extendedEntropy ρ = (torusEntropy ρ.value : EReal) := by
  unfold extendedEntropy
  rw [lintegral_shifted_eq ρ]
  exact toEReal_add_one_sub_one _


/-- The probability measure `ρ · torusMeasure d` of a probability density. -/
def densityMeasure {d : ℕ} (ρ : ProbabilityDensity d) : Measure (Torus d) :=
  (torusMeasure d).withDensity fun x => ENNReal.ofReal (ρ.value x)

instance {d : ℕ} (ρ : ProbabilityDensity d) : IsProbabilityMeasure (densityMeasure ρ) :=
  isProbabilityMeasure_withDensity (finiteMassDomain_density ρ) ρ.mass

/-- The entropy of the measure `ρ μ_unif` relative to `μ_unif` (the manuscript's convention for
`ν ≪ μ`) is the homogeneous entropy of its density. -/
theorem measureEntropy_densityMeasure {d : ℕ} (ρ : ProbabilityDensity d) :
    measureEntropy (densityMeasure ρ) (torusMeasure d) = torusEntropy ρ.value :=
  measureEntropy_withDensity (finiteMassDomain_density ρ)

/-- `extendedEntropy ρ` is Mathlib's `klDiv (ρ μ_unif) μ_unif`, cast to `EReal`. -/
theorem extendedEntropy_eq_klDiv {d : ℕ} (ρ : ProbabilityDensity d) :
    extendedEntropy ρ = (klDiv (densityMeasure ρ) (torusMeasure d) : EReal) := by
  rw [← measureEntropy_eq_klDiv, measureEntropy_densityMeasure, extendedEntropy_eq_torusEntropy]

/-- A probability measure that is not absolutely continuous has entropy `+∞` (and `klDiv = ⊤`). -/
theorem measureEntropy_torus_not_ac {d : ℕ} (ν : Measure (Torus d)) (h : ¬ ν ≪ torusMeasure d) :
    measureEntropy ν (torusMeasure d) = ∞ :=
  measureEntropy_of_not_ac h

end BecknerOnofri.V2.Vocab
