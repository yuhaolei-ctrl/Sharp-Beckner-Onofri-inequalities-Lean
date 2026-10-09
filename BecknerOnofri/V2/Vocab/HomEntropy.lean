module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

/-! # The homogeneous (finite-mass) entropy of the v2 manuscript

`eq:section2-relative-entropy`: for a probability measure `μ` and a nonnegative integrable `f`
of mass `m = ∫ f dμ`,
`Ent_μ(f) = ∫ f log f dμ - m log m ∈ [0, ∞]`, with `0 log 0 = 0` and value `0` at mass zero.

Implementation (extended nonnegative): for `m > 0` the integral of
`entropyIntegrand m (f x) = f x * log (f x / m) - f x + m`, a pointwise nonnegative function which
vanishes exactly at `f x = m`; at mass zero the value is `0`. This is the same functional:
`homEntropy_eq_ofReal` (finite case) and `integrable_mul_log_iff` (the value is `⊤` exactly when
`f log f` is not integrable) identify it with the manuscript's `∫ f log f - m log m`.
No `∞ - ∞` is ever formed and no Bochner integral of a nonintegrable function is used as `⊤`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Vocab

variable {α : Type*} [MeasurableSpace α]

/-- The pointwise integrand `r log (r/m) - r + m` (equal to `m * klFun (r/m)` for `m > 0`). -/
def entropyIntegrand (m r : ℝ) : ℝ := r * Real.log (r / m) - r + m

lemma entropyIntegrand_eq {m : ℝ} (hm : 0 < m) (r : ℝ) :
    entropyIntegrand m r = r * Real.log r - r * Real.log m - r + m := by
  unfold entropyIntegrand
  by_cases hr : r = 0
  · simp [hr]
  · rw [Real.log_div hr hm.ne']
    ring

lemma continuous_entropyIntegrand {m : ℝ} (hm : 0 < m) : Continuous (entropyIntegrand m) := by
  have h : entropyIntegrand m = fun r => r * Real.log r - r * Real.log m - r + m :=
    funext (entropyIntegrand_eq hm)
  rw [h]
  exact (((Real.continuous_mul_log).sub (continuous_id.mul continuous_const)).sub
    continuous_id).add continuous_const

lemma log_div_eq_neg (m r : ℝ) :
    Real.log (r / m) = -Real.log (m / r) := by
  rw [← Real.log_inv, inv_div]

lemma entropyIntegrand_nonneg {m r : ℝ} (hm : 0 < m) (hr : 0 ≤ r) :
    0 ≤ entropyIntegrand m r := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    simp [entropyIntegrand, hm.le]
  · have h := Real.log_le_sub_one_of_pos (div_pos hm hpos)
    have hr0 : r ≠ 0 := hpos.ne'
    have h2 : r * Real.log (m / r) ≤ m - r := by
      calc r * Real.log (m / r) ≤ r * (m / r - 1) := mul_le_mul_of_nonneg_left h hr
        _ = m - r := by rw [mul_sub, mul_div_cancel₀ _ hr0, mul_one]
    unfold entropyIntegrand
    rw [log_div_eq_neg m r, mul_neg]
    linarith

lemma entropyIntegrand_eq_zero_iff {m r : ℝ} (hm : 0 < m) (hr : 0 ≤ r) :
    entropyIntegrand m r = 0 ↔ r = m := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    have : entropyIntegrand m 0 = m := by simp [entropyIntegrand]
    rw [this]
    constructor <;> intro h <;> linarith
  · have hr0 : r ≠ 0 := hpos.ne'
    constructor
    · intro h
      by_contra hne
      have hne' : m / r ≠ 1 := by
        intro h1
        exact hne ((div_eq_one_iff_eq hr0).1 h1).symm
      have hlt := Real.log_lt_sub_one_of_pos (div_pos hm hpos) hne'
      have h2 : r * Real.log (m / r) < m - r := by
        calc r * Real.log (m / r) < r * (m / r - 1) := mul_lt_mul_of_pos_left hlt hpos
          _ = m - r := by rw [mul_sub, mul_div_cancel₀ _ hr0, mul_one]
      unfold entropyIntegrand at h
      rw [log_div_eq_neg m r, mul_neg] at h
      linarith
    · intro h
      rw [h]
      unfold entropyIntegrand
      rw [div_self hm.ne']
      simp

/-- `r log r ≥ -1` for `r ≥ 0` (the manuscript uses the sharper `-1/e`). -/
lemma neg_mul_log_le_one {r : ℝ} (hr : 0 ≤ r) : -(r * Real.log r) ≤ 1 := by
  have := Real.self_sub_one_le_mul_log hr
  linarith

/-- The domain of the homogeneous entropy: a.e. nonnegative and integrable. -/
structure FiniteMassDomain (μ : Measure α) (f : α → ℝ) : Prop where
  nonneg : ∀ᵐ x ∂μ, 0 ≤ f x
  integrable : Integrable f μ

namespace FiniteMassDomain
variable {μ : Measure α} {f g : α → ℝ}

lemma mass_nonneg (hf : FiniteMassDomain μ f) : 0 ≤ ∫ x, f x ∂μ :=
  integral_nonneg_of_ae hf.nonneg

/-- Zero mass forces `f = 0` almost everywhere. -/
lemma ae_eq_zero_of_mass_zero (hf : FiniteMassDomain μ f) (h : ∫ x, f x ∂μ = 0) :
    f =ᵐ[μ] 0 :=
  (integral_eq_zero_iff_of_nonneg_ae hf.nonneg hf.integrable).1 h

lemma congr_ae (hf : FiniteMassDomain μ f) (h : f =ᵐ[μ] g) : FiniteMassDomain μ g :=
  ⟨by filter_upwards [h, hf.nonneg] with x h1 h2; rwa [← h1], hf.integrable.congr h⟩

lemma const_mul (hf : FiniteMassDomain μ f) {c : ℝ} (hc : 0 ≤ c) :
    FiniteMassDomain μ (fun x => c * f x) :=
  ⟨by filter_upwards [hf.nonneg] with x hx; exact mul_nonneg hc hx, hf.integrable.const_mul c⟩

lemma const [IsFiniteMeasure μ] {c : ℝ} (hc : 0 ≤ c) : FiniteMassDomain μ (fun _ => c) :=
  ⟨Filter.Eventually.of_forall fun _ => hc, integrable_const c⟩

end FiniteMassDomain

open scoped Classical in
/-- The homogeneous entropy `Ent_μ(f) ∈ [0, ∞]` of the manuscript. Meaningful (and equal to
`∫ f log f - m log m`) on `FiniteMassDomain μ f` for a probability measure `μ`. -/
def homEntropy (μ : Measure α) (f : α → ℝ) : ℝ≥0∞ :=
  if ∫ x, f x ∂μ = 0 then 0
  else ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, f y ∂μ) (f x)) ∂μ

section Basic
variable {μ : Measure α} {f g : α → ℝ}

lemma homEntropy_of_mass_zero (h : ∫ x, f x ∂μ = 0) : homEntropy μ f = 0 := by
  simp only [homEntropy, h, ↓reduceIte]

lemma homEntropy_of_mass_ne_zero (h : ∫ x, f x ∂μ ≠ 0) :
    homEntropy μ f = ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, f y ∂μ) (f x)) ∂μ := by
  simp only [homEntropy, h, ↓reduceIte]

/-- Unit mass: the usual `∫ f log f` (as an extended nonnegative integral). -/
lemma homEntropy_of_mass_one (h : ∫ x, f x ∂μ = 1) :
    homEntropy μ f = ∫⁻ x, ENNReal.ofReal (f x * Real.log (f x) - f x + 1) ∂μ := by
  have h1 : ∫ x, f x ∂μ ≠ 0 := by rw [h]; exact one_ne_zero
  rw [homEntropy_of_mass_ne_zero h1, h]
  simp only [entropyIntegrand, div_one]

lemma homEntropy_congr_ae (h : f =ᵐ[μ] g) : homEntropy μ f = homEntropy μ g := by
  have hm : ∫ x, f x ∂μ = ∫ x, g x ∂μ := integral_congr_ae h
  by_cases h0 : ∫ x, g x ∂μ = 0
  · rw [homEntropy_of_mass_zero (hm ▸ h0), homEntropy_of_mass_zero h0]
  · rw [homEntropy_of_mass_ne_zero (hm ▸ h0), homEntropy_of_mass_ne_zero h0, hm]
    apply lintegral_congr_ae
    filter_upwards [h] with x hx
    rw [hx]

@[simp] lemma homEntropy_zero : homEntropy μ (fun _ => (0 : ℝ)) = 0 :=
  homEntropy_of_mass_zero (by simp)

/-- Positive homogeneity, for every scalar `c ≥ 0` (no domain hypothesis is needed). -/
lemma homEntropy_const_mul {c : ℝ} (hc : 0 ≤ c) (f : α → ℝ) :
    homEntropy μ (fun x => c * f x) = ENNReal.ofReal c * homEntropy μ f := by
  have hmass : ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ := integral_const_mul c f
  rcases hc.eq_or_lt with h0 | hc'
  · subst h0
    have h1 : ∫ x, (0 : ℝ) * f x ∂μ = 0 := by simp
    rw [homEntropy_of_mass_zero h1, ENNReal.ofReal_zero, zero_mul]
  · by_cases hm : ∫ x, f x ∂μ = 0
    · have h1 : ∫ x, c * f x ∂μ = 0 := by rw [hmass, hm, mul_zero]
      rw [homEntropy_of_mass_zero h1, homEntropy_of_mass_zero hm, mul_zero]
    · have hm' : ∫ x, c * f x ∂μ ≠ 0 := by rw [hmass]; exact mul_ne_zero hc'.ne' hm
      rw [homEntropy_of_mass_ne_zero hm', homEntropy_of_mass_ne_zero hm, hmass,
        ← lintegral_const_mul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul hc'.le]
      congr 1
      unfold entropyIntegrand
      rw [mul_div_mul_left _ _ hc'.ne']
      ring

end Basic

section Probability
variable {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}

lemma integral_const_prob (c : ℝ) : ∫ _x, c ∂μ = c := by simp

/-- Constants (of any finite nonnegative mass) have zero entropy. -/
lemma homEntropy_const {c : ℝ} (_hc : 0 ≤ c) : homEntropy μ (fun _ => c) = 0 := by
  by_cases h0 : c = 0
  · exact homEntropy_of_mass_zero (by simp [h0])
  · have h1 : ∫ _x : α, c ∂μ ≠ 0 := by rw [integral_const_prob]; exact h0
    rw [homEntropy_of_mass_ne_zero h1, integral_const_prob]
    simp [entropyIntegrand, div_self h0]

omit [IsProbabilityMeasure μ] in
lemma mass_normalized {m : ℝ} (hm : m ≠ 0) (hmass : ∫ x, f x ∂μ = m) :
    ∫ x, f x / m ∂μ = 1 := by
  rw [integral_div, hmass, div_self hm]

omit [IsProbabilityMeasure μ] in
/-- The normalized-density formula: `Ent(f) = m · Ent(f/m)` with `f/m` of unit mass. -/
lemma homEntropy_eq_mass_mul_normalized (hm : 0 < ∫ x, f x ∂μ) :
    homEntropy μ f = ENNReal.ofReal (∫ x, f x ∂μ) *
      homEntropy μ (fun x => f x / ∫ y, f y ∂μ) := by
  have h : homEntropy μ (fun x => (∫ y, f y ∂μ) * (f x / ∫ y, f y ∂μ)) =
      ENNReal.ofReal (∫ x, f x ∂μ) * homEntropy μ (fun x => f x / ∫ y, f y ∂μ) :=
    homEntropy_const_mul hm.le _
  have hne : (∫ y, f y ∂μ) ≠ 0 := hm.ne'
  have e : (fun x => (∫ y, f y ∂μ) * (f x / ∫ y, f y ∂μ)) = f := by
    funext x
    exact mul_div_cancel₀ _ hne
  rw [e] at h
  exact h

namespace FiniteMassDomain

omit [IsProbabilityMeasure μ] in
lemma aestronglyMeasurable_integrand (hf : FiniteMassDomain μ f) {m : ℝ} (hm : 0 < m) :
    AEStronglyMeasurable (fun x => entropyIntegrand m (f x)) μ :=
  (continuous_entropyIntegrand hm).comp_aestronglyMeasurable hf.integrable.aestronglyMeasurable

omit [IsProbabilityMeasure μ] in
lemma aestronglyMeasurable_mul_log (hf : FiniteMassDomain μ f) :
    AEStronglyMeasurable (fun x => f x * Real.log (f x)) μ :=
  Real.continuous_mul_log.comp_aestronglyMeasurable hf.integrable.aestronglyMeasurable

/-- The negative part of `f log f` has integral at most `1`: no `∞ - ∞`. -/
lemma lintegral_neg_mul_log_lt_top (hf : FiniteMassDomain μ f) :
    ∫⁻ x, ENNReal.ofReal (-(f x * Real.log (f x))) ∂μ < ∞ := by
  calc ∫⁻ x, ENNReal.ofReal (-(f x * Real.log (f x))) ∂μ ≤ ∫⁻ _x, 1 ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hf.nonneg] with x hx
        calc ENNReal.ofReal (-(f x * Real.log (f x))) ≤ ENNReal.ofReal 1 :=
              ENNReal.ofReal_le_ofReal (neg_mul_log_le_one hx)
          _ = 1 := ENNReal.ofReal_one
    _ = 1 := by simp
    _ < ∞ := ENNReal.one_lt_top

lemma integrable_integrand_iff (hf : FiniteMassDomain μ f) (hm : 0 < ∫ x, f x ∂μ) :
    Integrable (fun x => entropyIntegrand (∫ y, f y ∂μ) (f x)) μ ↔
      Integrable (fun x => f x * Real.log (f x)) μ := by
  set m := ∫ y, f y ∂μ with hmdef
  have hk : Integrable (fun x => f x * (Real.log m + 1) - m) μ :=
    (hf.integrable.mul_const _).sub (integrable_const m)
  have hsum : ∀ x, entropyIntegrand m (f x) + (f x * (Real.log m + 1) - m) =
      f x * Real.log (f x) := by
    intro x
    rw [entropyIntegrand_eq hm]
    ring
  constructor
  · intro h
    refine (h.add hk).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    exact hsum x
  · intro h
    refine (h.sub hk).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    linarith [hsum x]

end FiniteMassDomain

/-- The value is `⊤` exactly when `f log f` is not integrable (positive part infinite). -/
theorem integrable_mul_log_iff (hf : FiniteMassDomain μ f) :
    Integrable (fun x => f x * Real.log (f x)) μ ↔ homEntropy μ f ≠ ∞ := by
  by_cases hm : ∫ x, f x ∂μ = 0
  · rw [homEntropy_of_mass_zero hm]
    refine ⟨fun _ => ENNReal.zero_ne_top, fun _ => ?_⟩
    have h0 := hf.ae_eq_zero_of_mass_zero hm
    refine (integrable_zero α ℝ μ).congr ?_
    filter_upwards [h0] with x hx
    simp [hx]
  · have hpos : 0 < ∫ x, f x ∂μ := lt_of_le_of_ne hf.mass_nonneg (Ne.symm hm)
    rw [homEntropy_of_mass_ne_zero hm, ← hf.integrable_integrand_iff hpos]
    symm
    refine lintegral_ofReal_ne_top_iff_integrable (hf.aestronglyMeasurable_integrand hpos) ?_
    filter_upwards [hf.nonneg] with x hx
    exact entropyIntegrand_nonneg hpos hx

/-- The manuscript formula `∫ f log f - m log m` when `f log f` is integrable. -/
theorem homEntropy_eq_ofReal (hf : FiniteMassDomain μ f)
    (hg : Integrable (fun x => f x * Real.log (f x)) μ) :
    homEntropy μ f = ENNReal.ofReal ((∫ x, f x * Real.log (f x) ∂μ) -
      (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)) := by
  by_cases hm : ∫ x, f x ∂μ = 0
  · rw [homEntropy_of_mass_zero hm, hm]
    have h0 := hf.ae_eq_zero_of_mass_zero hm
    have : ∫ x, f x * Real.log (f x) ∂μ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [h0] with x hx
      simp [hx]
    rw [this]
    simp
  · have hpos : 0 < ∫ x, f x ∂μ := lt_of_le_of_ne hf.mass_nonneg (Ne.symm hm)
    set m := ∫ y, f y ∂μ with hmdef
    have hI : Integrable (fun x => entropyIntegrand m (f x)) μ :=
      (hf.integrable_integrand_iff hpos).2 hg
    have hnn : 0 ≤ᵐ[μ] fun x => entropyIntegrand m (f x) := by
      filter_upwards [hf.nonneg] with x hx
      exact entropyIntegrand_nonneg hpos hx
    rw [homEntropy_of_mass_ne_zero hm, ← ofReal_integral_eq_lintegral_ofReal hI hnn]
    congr 1
    have hint : ∫ x, entropyIntegrand m (f x) ∂μ =
        ∫ x, (f x * Real.log (f x) - (f x * (Real.log m + 1) - m)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        show entropyIntegrand m (f x) =
          f x * Real.log (f x) - (f x * (Real.log m + 1) - m)
        rw [entropyIntegrand_eq hpos]
        ring)
    have hk1 : Integrable (fun x => f x * (Real.log m + 1)) μ := hf.integrable.mul_const _
    have hk2 : ∫ x, (f x * (Real.log m + 1) - m) ∂μ = m * (Real.log m + 1) - m := by
      rw [integral_sub hk1 (integrable_const m), integral_mul_const, integral_const_prob]
    have hk3 : Integrable (fun x => f x * (Real.log m + 1) - m) μ :=
      hk1.sub (integrable_const m)
    have hk4 := integral_sub hg hk3
    rw [hint, hk4, hk2]
    ring

omit [IsProbabilityMeasure μ] in
/-- A.e.-constants (of any finite nonnegative mass) are exactly the zero-entropy functions. -/
theorem homEntropy_eq_zero_iff (hf : FiniteMassDomain μ f) :
    homEntropy μ f = 0 ↔ f =ᵐ[μ] fun _ => ∫ y, f y ∂μ := by
  by_cases hm : ∫ x, f x ∂μ = 0
  · rw [homEntropy_of_mass_zero hm]
    simp only [true_iff]
    rw [hm]
    exact hf.ae_eq_zero_of_mass_zero hm
  · have hpos : 0 < ∫ x, f x ∂μ := lt_of_le_of_ne hf.mass_nonneg (Ne.symm hm)
    rw [homEntropy_of_mass_ne_zero hm]
    set m := ∫ y, f y ∂μ with hmdef
    have hmeas : AEMeasurable (fun x => ENNReal.ofReal (entropyIntegrand m (f x))) μ :=
      (hf.aestronglyMeasurable_integrand hpos).aemeasurable.ennreal_ofReal
    rw [lintegral_eq_zero_iff' hmeas]
    constructor
    · intro h
      filter_upwards [h, hf.nonneg] with x hx hx0
      have hle : entropyIntegrand m (f x) ≤ 0 := by
        simpa [ENNReal.ofReal_eq_zero] using hx
      exact (entropyIntegrand_eq_zero_iff hpos hx0).1
        (le_antisymm hle (entropyIntegrand_nonneg hpos hx0))
    · intro h
      filter_upwards [h, hf.nonneg] with x hx hx0
      have : entropyIntegrand m (f x) = 0 := (entropyIntegrand_eq_zero_iff hpos hx0).2 hx
      simp [this]

end Probability

end BecknerOnofri.V2.Vocab
