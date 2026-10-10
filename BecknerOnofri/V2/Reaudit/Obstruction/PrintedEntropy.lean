module

public import BecknerOnofri.V2.Vocab.HomEntropyKL
public import BecknerOnofri.V2.Vocab.HomEntropyTorus
public import Mathlib.Analysis.Convex.Integral

@[expose] public section

/-! # Row U01: the entropy `eq:section2-relative-entropy`, exactly as printed

The manuscript defines, for a probability measure `μ` and a nonnegative `f ∈ L¹(μ)` of mass
`m = ∫ f dμ`,
`Ent_μ(f) = ∫ f log f dμ - m log m ∈ [0, +∞]`,
with `0 log 0 = 0` and value `0` at zero mass, and it remarks that the negative part of
`f log f` is integrable (`t log t ≥ -1/e`, `μ` a probability measure), that Jensen gives
nonnegativity, that at unit mass the value is `∫ f log f`, and that for a probability measure
`ν ≪ μ` the entropy of `ν` relative to `μ` is the value at `dν/dμ`, `+∞` otherwise.

The repository works with `V2.Vocab.homEntropy`, the integral of the pointwise nonnegative
integrand `r log (r/m) - r + m`.  This file adds the printed definition itself, as an `EReal`
(the positive part of `f log f` has an extended nonnegative integral, the negative part a finite
one, so the difference `P - N` is formed in `EReal` and never as `∞ - ∞`), and proves, with the
printed justifications, the printed remarks and the identification with `homEntropy`,
`measureEntropy` and Mathlib's `klDiv`.  No new analytic argument beyond Jensen is used. -/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Reaudit.Obstruction
open BecknerOnofri.V2.Vocab

variable {α : Type*} [MeasurableSpace α]

/-- Integral of the positive part of `f log f`, in `[0, ∞]`. -/
def mulLogPos (μ : Measure α) (f : α → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (f x * Real.log (f x)) ∂μ

/-- Integral of the negative part of `f log f`, in `[0, ∞]` (finite on the domain, see
`mulLogNeg_lt_top`). -/
def mulLogNeg (μ : Measure α) (f : α → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (-(f x * Real.log (f x))) ∂μ

/-- `∫ f log f dμ` as an extended real: positive part minus negative part. -/
def extIntegralMulLog (μ : Measure α) (f : α → ℝ) : EReal :=
  (mulLogPos μ f : EReal) - (mulLogNeg μ f : EReal)

/-- The entropy exactly as printed in `eq:section2-relative-entropy`:
`∫ f log f dμ - (∫ f dμ) log (∫ f dμ)`, with `0 log 0 = 0` (Lean's `Real.log 0 = 0`). -/
def printedEntropy (μ : Measure α) (f : α → ℝ) : EReal :=
  extIntegralMulLog μ f - (((∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) : ℝ) : EReal)

section Pointwise

/-- The printed bound `t log t ≥ -1/e` for `t ≥ 0`. -/
lemma neg_mul_log_le_exp_neg_one {t : ℝ} (ht : 0 ≤ t) : -(t * Real.log t) ≤ Real.exp (-1) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0; simp [(Real.exp_pos (-1)).le]
  · have h := Real.log_le_sub_one_of_pos
      (by positivity : 0 < Real.exp (-1) / t)
    rw [Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp] at h
    -- h : -1 - log t ≤ exp (-1) / t - 1
    have h2 : -Real.log t ≤ Real.exp (-1) / t := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hpos.le
    rw [mul_div_cancel₀ _ hpos.ne'] at h3
    linarith

end Pointwise

section Basic
variable {μ : Measure α} {f g : α → ℝ}

/-- The negative part of `f log f` is integrable (printed: `t log t ≥ -1/e` and `μ` is a
probability measure); the bound `1/e` is the printed one. -/
lemma mulLogNeg_le [IsProbabilityMeasure μ] (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    mulLogNeg μ f ≤ ENNReal.ofReal (Real.exp (-1)) := by
  unfold mulLogNeg
  calc ∫⁻ x, ENNReal.ofReal (-(f x * Real.log (f x))) ∂μ
      ≤ ∫⁻ _x, ENNReal.ofReal (Real.exp (-1)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hf] with x hx
        exact ENNReal.ofReal_le_ofReal (neg_mul_log_le_exp_neg_one hx)
    _ = ENNReal.ofReal (Real.exp (-1)) := by simp

lemma mulLogNeg_lt_top [IsProbabilityMeasure μ] (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    mulLogNeg μ f < ∞ :=
  (mulLogNeg_le hf).trans_lt ENNReal.ofReal_lt_top

lemma printedEntropy_of_mass_zero (h : ∫ x, f x ∂μ = 0) :
    printedEntropy μ f = extIntegralMulLog μ f := by
  simp [printedEntropy, h]

/-- At unit mass the printed value is `∫ f log f` (extended). -/
lemma printedEntropy_of_mass_one (h : ∫ x, f x ∂μ = 1) :
    printedEntropy μ f = extIntegralMulLog μ f := by
  simp [printedEntropy, h]

end Basic

section Probability
variable {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}

/-- Jensen's inequality, as printed: `m log m ≤ ∫ f log f` when `f log f` is integrable. -/
theorem mul_log_integral_le_integral_mul_log (hf : FiniteMassDomain μ f)
    (hg : Integrable (fun x => f x * Real.log (f x)) μ) :
    (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) ≤ ∫ x, f x * Real.log (f x) ∂μ := by
  have := Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici (by filter_upwards [hf.nonneg] with x hx using hx) hf.integrable hg
  exact this

lemma extIntegralMulLog_eq_of_integrable (hf : FiniteMassDomain μ f)
    (hg : Integrable (fun x => f x * Real.log (f x)) μ) :
    extIntegralMulLog μ f = ((∫ x, f x * Real.log (f x) ∂μ : ℝ) : EReal) := by
  have hneg : mulLogNeg μ f ≠ ∞ := (mulLogNeg_lt_top hf.nonneg).ne
  have hpos : mulLogPos μ f ≠ ∞ := by
    have := hg.hasFiniteIntegral
    refine ne_of_lt (lt_of_le_of_lt ?_ this)
    unfold mulLogPos
    apply lintegral_mono
    intro x
    dsimp only
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  unfold extIntegralMulLog
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  rw [← EReal.coe_ennreal_toReal hpos, ← EReal.coe_ennreal_toReal hneg, ← EReal.coe_sub]
  rfl

lemma mulLogPos_eq_top_of_not_integrable (hf : FiniteMassDomain μ f)
    (hg : ¬ Integrable (fun x => f x * Real.log (f x)) μ) : mulLogPos μ f = ∞ := by
  by_contra hpos
  apply hg
  have hmeas := hf.aestronglyMeasurable_mul_log
  refine ⟨hmeas, ?_⟩
  have hneg := mulLogNeg_lt_top hf.nonneg
  have hle : ∀ x, ‖f x * Real.log (f x)‖ₑ ≤
      ENNReal.ofReal (f x * Real.log (f x)) + ENNReal.ofReal (-(f x * Real.log (f x))) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_total 0 (f x * Real.log (f x)) with h | h
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h)]
      simp
    · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h]
      simp
  calc ∫⁻ x, ‖f x * Real.log (f x)‖ₑ ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (f x * Real.log (f x)) +
          ENNReal.ofReal (-(f x * Real.log (f x)))) ∂μ := lintegral_mono hle
    _ = mulLogPos μ f + mulLogNeg μ f := by
        rw [lintegral_add_right']
        · rfl
        · exact hmeas.aemeasurable.neg.ennreal_ofReal
    _ < ∞ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hpos, hneg⟩

/-- **Bridge (U01).**  On the domain of the definition, the printed entropy is the extended value
of the repository's `homEntropy`, including the case where it is `+∞`. -/
theorem printedEntropy_eq_homEntropy (hf : FiniteMassDomain μ f) :
    printedEntropy μ f = (homEntropy μ f : EReal) := by
  by_cases hg : Integrable (fun x => f x * Real.log (f x)) μ
  · rw [printedEntropy, extIntegralMulLog_eq_of_integrable hf hg, homEntropy_eq_ofReal hf hg,
      ← EReal.coe_sub, EReal.coe_ennreal_ofReal]
    have := mul_log_integral_le_integral_mul_log hf hg
    rw [max_eq_left (by linarith)]
  · have htop : homEntropy μ f = ∞ := by
      by_contra h
      exact hg ((integrable_mul_log_iff hf).2 h)
    rw [htop, printedEntropy, extIntegralMulLog, mulLogPos_eq_top_of_not_integrable hf hg]
    have hneg : mulLogNeg μ f ≠ ∞ := (mulLogNeg_lt_top hf.nonneg).ne
    rw [← EReal.coe_ennreal_toReal hneg, EReal.coe_ennreal_top, EReal.top_sub_coe,
      EReal.top_sub_coe]

/-- Printed remark: `Ent_μ(f) ≥ 0`, here by the printed route (Jensen), not through the bridge. -/
theorem printedEntropy_nonneg (hf : FiniteMassDomain μ f) : 0 ≤ printedEntropy μ f := by
  by_cases hg : Integrable (fun x => f x * Real.log (f x)) μ
  · rw [printedEntropy, extIntegralMulLog_eq_of_integrable hf hg, ← EReal.coe_sub]
    exact_mod_cast sub_nonneg.2 (mul_log_integral_le_integral_mul_log hf hg)
  · rw [printedEntropy, extIntegralMulLog, mulLogPos_eq_top_of_not_integrable hf hg]
    have hneg : mulLogNeg μ f ≠ ∞ := (mulLogNeg_lt_top hf.nonneg).ne
    rw [← EReal.coe_ennreal_toReal hneg, EReal.coe_ennreal_top, EReal.top_sub_coe,
      EReal.top_sub_coe]
    exact le_top

/-- Printed remark: the value is `+∞` exactly when `f log f` is not integrable (the positive part
carries the whole divergence). -/
theorem printedEntropy_eq_top_iff (hf : FiniteMassDomain μ f) :
    printedEntropy μ f = ⊤ ↔ ¬ Integrable (fun x => f x * Real.log (f x)) μ := by
  rw [printedEntropy_eq_homEntropy hf, integrable_mul_log_iff hf]
  simp

/-- Printed remark: the zero-mass value is zero. -/
theorem printedEntropy_of_mass_zero' (hf : FiniteMassDomain μ f) (h : ∫ x, f x ∂μ = 0) :
    printedEntropy μ f = 0 := by
  rw [printedEntropy_eq_homEntropy hf, homEntropy_of_mass_zero h]
  rfl

/-- Printed remark: at unit mass the value is `∫ f log f`, i.e. the real integral when it is
integrable and `+∞` otherwise. -/
theorem printedEntropy_unit_mass (hf : FiniteMassDomain μ f) (h : ∫ x, f x ∂μ = 1) :
    (Integrable (fun x => f x * Real.log (f x)) μ →
      printedEntropy μ f = ((∫ x, f x * Real.log (f x) ∂μ : ℝ) : EReal)) ∧
    (¬ Integrable (fun x => f x * Real.log (f x)) μ → printedEntropy μ f = ⊤) := by
  refine ⟨fun hg => ?_, fun hg => (printedEntropy_eq_top_iff hf).2 hg⟩
  rw [printedEntropy_of_mass_one h, extIntegralMulLog_eq_of_integrable hf hg]

end Probability

section Relative
open scoped Classical in
/-- The entropy of `ν` relative to `μ`, as printed: the printed entropy of the
Radon–Nikodym density if `ν ≪ μ`, and `+∞` otherwise. -/
def printedRelativeEntropy (ν μ : Measure α) : EReal :=
  if ν ≪ μ then printedEntropy μ (fun x => (ν.rnDeriv μ x).toReal) else ⊤

variable {μ ν : Measure α}

theorem printedRelativeEntropy_of_not_ac (h : ¬ ν ≪ μ) : printedRelativeEntropy ν μ = ⊤ := by
  simp only [printedRelativeEntropy, h, ↓reduceIte]

lemma finiteMassDomain_rnDeriv [IsFiniteMeasure ν] [SigmaFinite μ] :
    FiniteMassDomain μ (fun x => (ν.rnDeriv μ x).toReal) :=
  ⟨Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg, Measure.integrable_toReal_rnDeriv⟩

/-- The printed entropy relative to `μ` is the repository's `measureEntropy`, in both cases. -/
theorem printedRelativeEntropy_eq_measureEntropy [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : printedRelativeEntropy ν μ = (measureEntropy ν μ : EReal) := by
  by_cases hac : ν ≪ μ
  · simp only [printedRelativeEntropy, measureEntropy, hac, ↓reduceIte]
    exact printedEntropy_eq_homEntropy finiteMassDomain_rnDeriv
  · rw [printedRelativeEntropy_of_not_ac hac, measureEntropy_of_not_ac hac]
    rfl

/-- ... and Mathlib's Kullback–Leibler divergence. -/
theorem printedRelativeEntropy_eq_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    printedRelativeEntropy ν μ = (klDiv ν μ : EReal) := by
  rw [printedRelativeEntropy_eq_measureEntropy, measureEntropy_eq_klDiv]

end Relative

section Torus
open BecknerOnofri.HighDim

/-- The printed entropy of a probability density on `𝕋^d` (with respect to normalized Haar
measure) is the repository's `extendedEntropy`. -/
theorem printedEntropy_torus_density {d : ℕ} (ρ : ProbabilityDensity d) :
    printedEntropy (torusMeasure d) ρ.value = extendedEntropy ρ := by
  rw [printedEntropy_eq_homEntropy (finiteMassDomain_density ρ),
    extendedEntropy_eq_torusEntropy]

end Torus

end BecknerOnofri.V2.Reaudit.Obstruction
