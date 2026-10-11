module

public import BecknerOnofri.V2.Reaudit.ExternalInputs.CriticalAdams
public import BecknerOnofri.V2.Reaudit.Attainment.Basic
public import BecknerOnofri.V2.Vocab.ExternalInputs

@[expose] public section

/-! # An independent proof of `PositiveThresholdInput d` (S007, U24)

The manuscript takes `eq:section2-positive-threshold-input`
(`Ent ρ ≥ (β₀ c_d / 2) ‖ρ‖²_{Ḣ^{-d/2}}` for some `β₀ > 0`) from [CdCRS2025, Thm 3] for `d ≥ 2`.
`ExternalInputs.positiveThreshold` derives it from the final threshold theorems (reverse order).  Here it is
proved **from the sharp critical Adams inequality with additive constant**
(`ExternalInputs.criticalAdams`) and elementary estimates only.  This is a *route difference*: a different
proof of the displayed inequality; it replaces the citation of [CdCRS2025, Thm 3] for `d ≥ 2`.

Route.

1. (`exists_weak_beckner_onofri`) There is a finite `A₀ > 0` with
   `log ∫ e^{u-ū} ≤ A₀ ‖u‖²_{Ḣ^{d/2}}` for **all** `u ∈ H^{d/2}` (no additive constant).
   * If `‖u‖² ≥ 1`: critical Adams gives `≤ A_crit ‖u‖² + B ≤ (A_crit + B) ‖u‖²`.
   * If `‖u‖² = E ≤ 1`, with `v = u - ū` (mean zero): `Z - 1 = ∫ (e^v - 1 - v)`,
     `e^v - 1 - v ≤ v² e^{|v|}` (`exp_sub_one_sub_le`), `v² ≤ (2/λ²) e^{λ|v|}`, hence
     `e^v - 1 - v ≤ (2/λ²)(e^{μ v} + e^{-μ v})`, `μ = 1 + λ`; integrating and using critical Adams for
     `±μ u` gives `Z - 1 ≤ (4/λ²) exp(A_crit μ² E + B)`.  For `E > 0` take `λ = E^{-1/2}`
     (`μ² E = (1 + √E)² ≤ 4`), which gives `Z - 1 ≤ 4 e^{4 A_crit + B} E`; for `E = 0` let `λ → ∞`.
     Finally `log Z ≤ Z - 1`.
   No Sobolev embedding `H^{d/2} ⊂ L⁴` and no Cauchy-Schwarz is needed: the factor `v²` is absorbed
   into the exponential by the elementary bound `y²/2 ≤ e^{y}`, at the price of the exponent `(1+λ)`.
2. (`pressure_zero_of_weak`) `coefficientDefect d A₀ ≤ 0`, so by `pressure_eq_coefficientDefect`
   `pressure d β₀ = 0` for `β₀ = β_s(d)/(2 A₀ (2π)^d) > 0`, which is the competitor inequality
   `β₀ · interaction ρ ≤ Ent ρ` (`pressure_zero_iff_competitors`).
3. (`positiveThreshold_independent`) `interaction ρ = c_d ‖ρ‖²/2` converts this to the Prop.

Nothing from the endpoint chain, from `ExternalInputs.positiveThreshold`, or from any final threshold
theorem is used (see the dependency trace in the report). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory

namespace BecknerOnofri.V2.Reaudit.ExternalInputs
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-! ### Elementary real inequalities -/

/-- `e^x - 1 - x ≤ x² e^{|x|}`. -/
theorem exp_sub_one_sub_le (x : ℝ) : Real.exp x - 1 - x ≤ x ^ 2 * Real.exp |x| := by
  have h1 : Real.exp x - 1 ≤ x * Real.exp x := by
    have h := Real.add_one_le_exp (-x)
    have hx : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos x]
  have h2 : Real.exp x - 1 - x ≤ x * (Real.exp x - 1) := by nlinarith
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    calc Real.exp x - 1 - x ≤ x * (Real.exp x - 1) := h2
      _ ≤ x * (x * Real.exp x) := mul_le_mul_of_nonneg_left h1 hx
      _ = x ^ 2 * Real.exp x := by ring
  · rw [abs_of_nonpos hx]
    have h3 : 1 - Real.exp x ≤ -x := by linarith [Real.add_one_le_exp x]
    have h4 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    have h5 : 0 < 1 - Real.exp x ∨ Real.exp x = 1 ∨ 1 < Real.exp x := by
      rcases lt_trichotomy (Real.exp x) 1 with h | h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    calc Real.exp x - 1 - x ≤ x * (Real.exp x - 1) := h2
      _ = (-x) * (1 - Real.exp x) := by ring
      _ ≤ (-x) * (-x) := mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = x ^ 2 := by ring
      _ = x ^ 2 * 1 := by ring
      _ ≤ x ^ 2 * Real.exp (-x) := mul_le_mul_of_nonneg_left h4 (sq_nonneg x)

/-- `v² ≤ (2/λ²) e^{λ|v|}` for `λ > 0`. -/
theorem sq_le_two_div_mul_exp {l : ℝ} (hl : 0 < l) (v : ℝ) :
    v ^ 2 ≤ 2 / l ^ 2 * Real.exp (l * |v|) := by
  have hy := Real.quadratic_le_exp_of_nonneg (mul_nonneg hl.le (abs_nonneg v))
  have hl2 : 0 < l ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  have h0 : 0 ≤ l * |v| := mul_nonneg hl.le (abs_nonneg v)
  have : (l * |v|) ^ 2 = l ^ 2 * v ^ 2 := by rw [mul_pow, sq_abs]
  rw [this] at hy
  nlinarith [this]

/-- Pointwise bound used for the small-norm regime. -/
theorem exp_sub_one_sub_le_cosh {l : ℝ} (hl : 0 < l) (v : ℝ) :
    Real.exp v - 1 - v ≤
      2 / l ^ 2 * (Real.exp ((1 + l) * v) + Real.exp ((-(1 + l)) * v)) := by
  have h1 := exp_sub_one_sub_le v
  have h2 := sq_le_two_div_mul_exp hl v
  have h3 : v ^ 2 * Real.exp |v| ≤ 2 / l ^ 2 * Real.exp (l * |v|) * Real.exp |v| :=
    mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have h4 : Real.exp (l * |v|) * Real.exp |v| = Real.exp ((1 + l) * |v|) := by
    rw [← Real.exp_add]; congr 1; ring
  have h5 : Real.exp ((1 + l) * |v|) ≤
      Real.exp ((1 + l) * v) + Real.exp ((-(1 + l)) * v) := by
    rcases le_total 0 v with hv | hv
    · rw [abs_of_nonneg hv]; linarith [Real.exp_pos ((-(1 + l)) * v)]
    · rw [abs_of_nonpos hv, mul_neg, ← neg_mul]; linarith [Real.exp_pos ((1 + l) * v)]
  have h6 : 0 ≤ 2 / l ^ 2 := by positivity
  calc Real.exp v - 1 - v ≤ v ^ 2 * Real.exp |v| := h1
    _ ≤ 2 / l ^ 2 * Real.exp (l * |v|) * Real.exp |v| := h3
    _ = 2 / l ^ 2 * Real.exp ((1 + l) * |v|) := by rw [mul_assoc, h4]
    _ ≤ _ := mul_le_mul_of_nonneg_left h5 h6

/-! ### Critical Adams in real form, and scaling -/

variable {d : ℕ}

/-- Real form of critical Adams with a nonnegative additive constant. -/
theorem criticalAdams_real (hd : 0 < d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : Torus d → ℝ, InCriticalSobolev u →
      Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤
        collapseCoefficient d * potentialEnergy u + B := by
  obtain ⟨B, hB⟩ := (criticalAdamsInput_iff hd).1 (criticalAdams hd)
  refine ⟨|B|, abs_nonneg B, fun u hu => ?_⟩
  have h := hB u hu
  rw [logPartition_eq_log_integral hd u hu] at h
  have h' := EReal.coe_le_coe_iff.mp h
  linarith [le_abs_self B]

theorem centered_const_mul (c : ℝ) (u : Torus d → ℝ) (x : Torus d) :
    centered (fun y => c * u y) x = c * centered u x := by
  unfold centered
  rw [integral_const_mul]; ring

/-- The partition function `∫ e^{u-ū}` at `c u`, bounded by critical Adams. -/
theorem partition_const_mul_le (hd : 0 < d) {A B : ℝ}
    (hAB : ∀ u : Torus d → ℝ, InCriticalSobolev u →
      Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤ A * potentialEnergy u + B)
    (c : ℝ) {u : Torus d → ℝ} (hu : InCriticalSobolev u) :
    (∫ x, Real.exp (c * centered u x) ∂torusMeasure d) ≤
      Real.exp (A * (c ^ 2 * potentialEnergy u) + B) := by
  have hcu := Attainment.inCriticalSobolev_const_mul c hu
  have h := hAB _ hcu
  rw [Attainment.potentialEnergy_const_mul] at h
  simp_rw [centered_const_mul] at h
  have hpos := integral_exp_pos (exp_centered_integrable hd _ hcu)
  simp_rw [centered_const_mul] at hpos
  calc _ = Real.exp (Real.log (∫ x, Real.exp (c * centered u x) ∂torusMeasure d)) :=
        (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr h

/-! ### The small-norm estimate -/

/-- `Z(u) - 1 ≤ (4/λ²) exp(A μ² E + B)` for every `λ > 0`, `μ = 1 + λ`. -/
theorem partition_sub_one_le (hd : 0 < d) {A B : ℝ}
    (hAB : ∀ u : Torus d → ℝ, InCriticalSobolev u →
      Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤ A * potentialEnergy u + B)
    {u : Torus d → ℝ} (hu : InCriticalSobolev u) {l : ℝ} (hl : 0 < l) :
    (∫ x, Real.exp (centered u x) ∂torusMeasure d) - 1 ≤
      4 / l ^ 2 * Real.exp (A * ((1 + l) ^ 2 * potentialEnergy u) + B) := by
  have hint := hu.1.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hc : Integrable (centered u) (torusMeasure d) := hint.sub (integrable_const _)
  have hexp := exp_centered_integrable hd u hu
  have hp : Integrable (fun x => Real.exp ((1 + l) * centered u x)) (torusMeasure d) := by
    have := exp_centered_integrable hd _ (Attainment.inCriticalSobolev_const_mul (1 + l) hu)
    simpa [centered_const_mul] using this
  have hm : Integrable (fun x => Real.exp ((-(1 + l)) * centered u x)) (torusMeasure d) := by
    have := exp_centered_integrable hd _ (Attainment.inCriticalSobolev_const_mul (-(1 + l)) hu)
    simpa only [centered_const_mul] using this
  have hlhs : Integrable (fun x => Real.exp (centered u x) - 1 - centered u x) (torusMeasure d) :=
    (hexp.sub (integrable_const _)).sub hc
  have hrhs : Integrable (fun x => 2 / l ^ 2 *
      (Real.exp ((1 + l) * centered u x) + Real.exp ((-(1 + l)) * centered u x)))
      (torusMeasure d) := (hp.add hm).const_mul _
  have hmono := integral_mono hlhs hrhs
    (fun x => exp_sub_one_sub_le_cosh hl (centered u x))
  have hL : (∫ x, (Real.exp (centered u x) - 1 - centered u x) ∂torusMeasure d) =
      (∫ x, Real.exp (centered u x) ∂torusMeasure d) - 1 := by
    rw [integral_sub (f := fun x => Real.exp (centered u x) - 1) (g := centered u)
      (hexp.sub (integrable_const _)) hc,
      integral_sub (f := fun x => Real.exp (centered u x)) (g := fun _ => (1 : ℝ))
      hexp (integrable_const _), centered_integral u hint]
    simp
  have hR : (∫ x, 2 / l ^ 2 *
      (Real.exp ((1 + l) * centered u x) + Real.exp ((-(1 + l)) * centered u x))
        ∂torusMeasure d) =
      2 / l ^ 2 * ((∫ x, Real.exp ((1 + l) * centered u x) ∂torusMeasure d) +
        ∫ x, Real.exp ((-(1 + l)) * centered u x) ∂torusMeasure d) := by
    rw [integral_const_mul, integral_add hp hm]
  rw [hL, hR] at hmono
  have h1 := partition_const_mul_le hd hAB (1 + l) hu
  have h2 := partition_const_mul_le hd hAB (-(1 + l)) hu
  rw [neg_sq] at h2
  have hl2 : 0 < 2 / l ^ 2 := by positivity
  calc _ ≤ _ := hmono
    _ ≤ 2 / l ^ 2 * (Real.exp (A * ((1 + l) ^ 2 * potentialEnergy u) + B) +
        Real.exp (A * ((1 + l) ^ 2 * potentialEnergy u) + B)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) hl2.le
    _ = _ := by ring

/-- For `E ≤ 1`: `Z(u) - 1 ≤ 4 e^{4A + B} E`, where `A ≥ 0`. -/
theorem partition_sub_one_le_small (hd : 0 < d) {A B : ℝ} (hA : 0 ≤ A)
    (hAB : ∀ u : Torus d → ℝ, InCriticalSobolev u →
      Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤ A * potentialEnergy u + B)
    {u : Torus d → ℝ} (hu : InCriticalSobolev u) (hE : potentialEnergy u ≤ 1) :
    (∫ x, Real.exp (centered u x) ∂torusMeasure d) - 1 ≤
      4 * Real.exp (4 * A + B) * potentialEnergy u := by
  have hE0 : 0 ≤ potentialEnergy u := Attainment.potentialEnergy_nonneg u
  rcases hE0.eq_or_lt with hz | hpos
  · -- `E = 0`: let `λ → ∞`
    rw [← hz, mul_zero]
    by_contra hcon
    replace hcon := not_le.mp hcon
    set c := (∫ x, Real.exp (centered u x) ∂torusMeasure d) - 1 with hc
    have hcpos : 0 < c := hcon
    set l := Real.sqrt (8 * Real.exp B / c) with hl
    have hlpos : 0 < l := Real.sqrt_pos.mpr (by positivity)
    have hl2 : l ^ 2 = 8 * Real.exp B / c := Real.sq_sqrt (by positivity)
    have h := partition_sub_one_le hd hAB hu hlpos
    rw [← hz] at h
    simp only [mul_zero, zero_add] at h
    rw [← hc, hl2] at h
    have : 4 / (8 * Real.exp B / c) * Real.exp B = c / 2 := by
      field_simp; ring
    rw [this] at h
    linarith
  · set s := Real.sqrt (potentialEnergy u) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
    have hs2 : s ^ 2 = potentialEnergy u := Real.sq_sqrt hpos.le
    have hs1 : s ≤ 1 := by
      rw [hs]; exact Real.sqrt_le_one.mpr hE  -- placeholder name check
    set l := 1 / s with hl
    have hlpos : 0 < l := by positivity
    have h := partition_sub_one_le hd hAB hu hlpos
    have e1 : (1 + l) ^ 2 * potentialEnergy u = (s + 1) ^ 2 := by
      rw [← hs2, hl]; field_simp
    have e2 : 4 / l ^ 2 = 4 * potentialEnergy u := by
      rw [← hs2, hl]; field_simp
    rw [e1, e2] at h
    have hb : A * (s + 1) ^ 2 + B ≤ 4 * A + B := by
      have : (s + 1) ^ 2 ≤ 4 := by nlinarith
      nlinarith
    calc _ ≤ _ := h
      _ ≤ 4 * potentialEnergy u * Real.exp (4 * A + B) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) (by positivity)
      _ = _ := by ring

/-! ### The weak Beckner-Onofri inequality -/

/-- **Weak Beckner-Onofri inequality** (no additive constant): there is `A₀ > 0` with
`log ∫ e^{u-ū} ≤ A₀ ‖u‖²_{Ḣ^{d/2}}` for all `u ∈ H^{d/2}`. -/
theorem exists_weak_beckner_onofri (hd : 0 < d) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ u : Torus d → ℝ, InCriticalSobolev u →
      Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤ A₀ * potentialEnergy u := by
  obtain ⟨B, hB0, hB⟩ := criticalAdams_real hd
  have hA : 0 < collapseCoefficient d := by
    rw [collapseCoefficient_eq hd]
    have := kernelConstant_pos hd
    have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    positivity
  set A := collapseCoefficient d with hAdef
  refine ⟨A + B + 4 * Real.exp (4 * A + B), by positivity, fun u hu => ?_⟩
  have hE0 : 0 ≤ potentialEnergy u := Attainment.potentialEnergy_nonneg u
  have hexp := exp_centered_integrable hd u hu
  have hZpos := integral_exp_pos hexp
  rcases le_total (potentialEnergy u) 1 with hE | hE
  · have h := partition_sub_one_le_small hd hA.le hB hu hE
    have hlog := Real.log_le_sub_one_of_pos hZpos
    have : 4 * Real.exp (4 * A + B) * potentialEnergy u ≤
        (A + B + 4 * Real.exp (4 * A + B)) * potentialEnergy u := by
      apply mul_le_mul_of_nonneg_right _ hE0
      linarith
    linarith
  · have h := hB u hu
    have : B ≤ B * potentialEnergy u := by nlinarith
    have h2 : 0 ≤ 4 * Real.exp (4 * A + B) * potentialEnergy u := by positivity
    nlinarith

/-! ### From the weak inequality to the pressure and the Prop -/

theorem coefficientDefect_nonpos_of_weak (hd : 0 < d) {A₀ : ℝ}
    (h : ∀ u : Torus d → ℝ, InCriticalSobolev u →
      Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤ A₀ * potentialEnergy u) :
    coefficientDefect d A₀ ≤ 0 := by
  refine iSup_le fun u => iSup_le fun hu => ?_
  rw [logPartition_eq_log_integral hd u hu, ← EReal.coe_sub]
  have := h u hu
  exact_mod_cast sub_nonpos.mpr this

/-- **`eq:section2-positive-threshold-input`, independent proof**, for all `d ≥ 1`, from critical Adams
and elementary estimates (see the module doc). -/
theorem positiveThreshold_independent (hd : 0 < d) : PositiveThresholdInput d := by
  obtain ⟨A₀, hA₀, hweak⟩ := exists_weak_beckner_onofri hd
  have hσ := spectralThreshold_pos hd
  have hpi : 0 < (2 * Real.pi) ^ d := by positivity
  set β := spectralThreshold d / (2 * A₀ * (2 * Real.pi) ^ d) with hβdef
  have hβ : 0 < β := by positivity
  have hA : spectralThreshold d / (2 * β * (2 * Real.pi) ^ d) = A₀ := by
    rw [hβdef]; field_simp
  have hp0 : pressure d β = 0 := by
    apply le_antisymm
    · rw [pressure_eq_coefficientDefect hd hβ, hA]
      exact coefficientDefect_nonpos_of_weak hd hweak
    · exact pressure_nonneg d β
  refine ⟨β, hβ, fun ρ hρ => ?_⟩
  have hc := (VariationalCurves.pressure_zero_iff_competitors hd β).1 hp0 ρ hρ
  rw [interaction_eq_kernelConstant_mul hd ρ hρ, entropy_eq_toReal_torusEntropy ρ hρ] at hc
  linarith

/-- `0 < β_gm(d)` for every `d ≥ 1`, from `positiveThreshold_independent` (no endpoint theorems). -/
theorem globalTransition_pos_independent (hd : 0 < d) : 0 < VariationalCurves.globalTransition d :=
  globalTransition_pos_of_input hd (positiveThreshold_independent hd)

end BecknerOnofri.V2.Reaudit.ExternalInputs

#print axioms BecknerOnofri.V2.Reaudit.ExternalInputs.exists_weak_beckner_onofri
#print axioms BecknerOnofri.V2.Reaudit.ExternalInputs.positiveThreshold_independent
#print axioms BecknerOnofri.V2.Reaudit.ExternalInputs.globalTransition_pos_independent
