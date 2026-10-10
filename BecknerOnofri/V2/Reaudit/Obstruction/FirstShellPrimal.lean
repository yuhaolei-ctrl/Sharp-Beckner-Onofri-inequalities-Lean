module

public import BecknerOnofri.V2.Transfer.Characters
public import BecknerOnofri.Definitions
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! # Row S006, part (ii): the first-shell test density `ρ_t = 1 + t cos(2π x_j)`

Printed (`eq:section2-first-shell-density`, `-interaction`): `ρ_t(x) = 1 + t cos(2π x_1)`, `|t| < 1`;
the only nonzero Fourier coefficients of `ρ_t` at frequencies `k ≠ 0` are `ρ̂_t(±e_1) = t/2`, so
`∑_{k ≠ 0} |k|^{-d} |ρ̂_t(k)|² = t²/2` (this is `(2π)^d ‖ρ_t‖²_{Ḣ^{-d/2}}`).

This file constructs `ρ_t` as a probability density, computes its Fourier coefficients and the
spectral energy from the orthogonality `∫ e^{2π i n·x} dx = 1_{n=0}` of the characters, and proves
the entropy upper bound `Ent(ρ_t) ≤ t²/4 + 2|t|³` for `|t| ≤ 1/2` (printed:
`Ent(ρ_t) = t²/4 + O(t⁴)`; only the upper bound with remainder `O(|t|³)` is proved, which suffices
for the sign of `t²/4 (1 - β/β_s) + O(|t|³)`; see the report). -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace BecknerOnofri.V2.Reaudit.Obstruction

open BecknerOnofri.HighDim BecknerOnofri.V2.Transfer

variable {d : ℕ}

lemma mFourier_axis (j : Fin d) (x : Torus d) :
    UnitAddTorus.mFourier (axisFrequency j) x = fourier 1 (x j) := by
  classical
  have h : axisFrequency j = Pi.single j 1 := by
    ext i
    by_cases hi : i = j <;> simp [axisFrequency, hi]
  rw [h]
  exact UnitAddTorus.mFourier_single x j

/-- The function `x ↦ 1 + t cos(2π x_j)`. -/
def firstShellValue (j : Fin d) (t : ℝ) (x : Torus d) : ℝ :=
  1 + t * (fourier 1 (x j)).re

lemma firstShellValue_complex (j : Fin d) (t : ℝ) (x : Torus d) :
    ((firstShellValue j t x : ℝ) : ℂ) =
      1 + (t / 2 : ℂ) * UnitAddTorus.mFourier (axisFrequency j) x +
        (t / 2 : ℂ) * UnitAddTorus.mFourier (-axisFrequency j) x := by
  rw [UnitAddTorus.mFourier_neg, mFourier_axis]
  unfold firstShellValue
  have h := Complex.re_eq_add_conj (fourier 1 (x j))
  push_cast
  rw [h]
  ring

lemma continuous_firstShellValue (j : Fin d) (t : ℝ) : Continuous (firstShellValue j t) := by
  unfold firstShellValue
  have h1 : Continuous (fun x : Torus d => fourier 1 (x j)) :=
    (fourier 1).continuous.comp (continuous_apply j)
  exact continuous_const.add (continuous_const.mul (Complex.continuous_re.comp h1))

lemma firstShellValue_pos (j : Fin d) {t : ℝ} (ht : |t| < 1) (x : Torus d) :
    0 < firstShellValue j t x := by
  unfold firstShellValue
  have h1 : |(fourier 1 (x j)).re| ≤ 1 := by
    have := Complex.abs_re_le_norm (fourier 1 (x j))
    simpa [fourier_norm] using this
  have h2 : |t * (fourier 1 (x j)).re| ≤ |t| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  have := (abs_le.mp h2).1
  linarith

/-- The Fourier coefficients of the first-shell function. -/
theorem fourierCoeff_firstShell (j : Fin d) (t : ℝ) (k : Frequency d) :
    HighDim.fourierCoeff (firstShellValue j t) k =
      (if k = 0 then 1 else 0) + (t / 2 : ℂ) * (if k = axisFrequency j then 1 else 0) +
        (t / 2 : ℂ) * (if k = -axisFrequency j then 1 else 0) := by
  have hpt : ∀ x : Torus d, UnitAddTorus.mFourier (-k) x * ((firstShellValue j t x : ℝ) : ℂ) =
      UnitAddTorus.mFourier (-k) x + (t / 2 : ℂ) * UnitAddTorus.mFourier (axisFrequency j + -k) x +
        (t / 2 : ℂ) * UnitAddTorus.mFourier (-axisFrequency j + -k) x := by
    intro x
    rw [firstShellValue_complex, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_add]
    ring
  unfold HighDim.fourierCoeff
  simp_rw [hpt]
  have c1 : Integrable (fun x : Torus d => UnitAddTorus.mFourier (-k) x) (torusMeasure d) :=
    integrable_of_continuous_torus (continuous_mFourier' (-k))
  have c2 : Integrable (fun x : Torus d => (t / 2 : ℂ) * UnitAddTorus.mFourier (axisFrequency j + -k) x)
      (torusMeasure d) :=
    (integrable_of_continuous_torus (continuous_mFourier' (axisFrequency j + -k))).const_mul _
  have c3 : Integrable (fun x : Torus d =>
      (t / 2 : ℂ) * UnitAddTorus.mFourier (-axisFrequency j + -k) x) (torusMeasure d) :=
    (integrable_of_continuous_torus (continuous_mFourier' (-axisFrequency j + -k))).const_mul _
  have c12 : Integrable (fun x : Torus d => UnitAddTorus.mFourier (-k) x +
      (t / 2 : ℂ) * UnitAddTorus.mFourier (axisFrequency j + -k) x) (torusMeasure d) := c1.add c2
  rw [integral_add c12 c3, integral_add c1 c2,
    integral_const_mul, integral_const_mul, integral_mFourier, integral_mFourier, integral_mFourier]
  simp only [neg_eq_zero, add_neg_eq_zero]
  congr 3
  · simp [eq_comm]
  · simp [eq_comm]

lemma axisFrequency_ne_zero' (j : Fin d) : axisFrequency j ≠ 0 := by
  intro h
  have := congrFun h j
  simp [axisFrequency] at this

lemma axisFrequency_ne_neg (j : Fin d) : axisFrequency j ≠ -axisFrequency j := by
  intro h
  have := congrFun h j
  simp [axisFrequency] at this

lemma frequencyLength_axis (j : Fin d) : frequencyLength (axisFrequency j) = 1 := by
  classical
  simp [frequencyLength, axisFrequency]

lemma frequencyLength_neg_axis (j : Fin d) : frequencyLength (-axisFrequency j) = 1 := by
  classical
  simp [frequencyLength, axisFrequency]

lemma integral_firstShellValue (j : Fin d) (t : ℝ) :
    ∫ x, firstShellValue j t x ∂torusMeasure d = 1 := by
  have h := fourierCoeff_firstShell j t 0
  have h0 : HighDim.fourierCoeff (firstShellValue j t) 0 =
      ((∫ x, firstShellValue j t x ∂torusMeasure d : ℝ) : ℂ) := by
    unfold HighDim.fourierCoeff
    simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_mul]
    exact integral_complex_ofReal
  rw [h0] at h
  simp only [ite_true, if_neg (Ne.symm (axisFrequency_ne_zero' j)),
    if_neg (Ne.symm (neg_ne_zero.mpr (axisFrequency_ne_zero' j))), mul_zero, add_zero] at h
  exact_mod_cast h

/-- The first-shell function `1 + t cos(2π x_j)`, `|t| < 1`, as a probability density. -/
def firstShellDensity (j : Fin d) {t : ℝ} (ht : |t| < 1) : ProbabilityDensity d where
  value := firstShellValue j t
  nonneg := Filter.Eventually.of_forall fun x => (firstShellValue_pos j ht x).le
  integrable := (continuous_firstShellValue j t).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  mass := integral_firstShellValue j t

/-- **Printed `eq:section2-first-shell-interaction`:** the spectral energy of the first-shell density
is `∑_{k ≠ 0} |k|^{-d} |ρ̂_t(k)|² = t²/2`. -/
theorem spectralEnergy_firstShell (j : Fin d) {t : ℝ} (ht : |t| < 1) :
    spectralEnergy (firstShellDensity j ht) = ENNReal.ofReal (t ^ 2 / 2) := by
  classical
  set e := axisFrequency j with he
  have he0 : e ≠ 0 := axisFrequency_ne_zero' j
  have hn0 : -e ≠ 0 := neg_ne_zero.mpr he0
  set a : NonzeroFrequency d := ⟨e, he0⟩ with ha
  set b : NonzeroFrequency d := ⟨-e, hn0⟩ with hb
  have hab : a ≠ b := fun h => axisFrequency_ne_neg j (congrArg Subtype.val h)
  have hcoef : ∀ k : NonzeroFrequency d, HighDim.fourierCoeff (firstShellDensity j ht).value k.val =
      (if k.val = e then (t / 2 : ℂ) else 0) + (if k.val = -e then (t / 2 : ℂ) else 0) := by
    intro k
    change HighDim.fourierCoeff (firstShellValue j t) k.val = _
    rw [fourierCoeff_firstShell, if_neg k.property]
    simp only [zero_add]
    split_ifs <;> simp
  unfold spectralEnergy
  rw [tsum_eq_sum (s := {a, b})]
  · rw [Finset.sum_pair hab]
    have h1 : spectralTerm (firstShellDensity j ht) a = (t / 2) ^ 2 := by
      unfold spectralTerm
      rw [hcoef a]
      simp only [ha, ite_true, if_neg (axisFrequency_ne_neg j), add_zero, he, frequencyLength_axis]
      simp [Complex.norm_real, div_pow, sq_abs]
    have h2 : spectralTerm (firstShellDensity j ht) b = (t / 2) ^ 2 := by
      unfold spectralTerm
      rw [hcoef b]
      simp only [hb, ite_true, if_neg (Ne.symm (axisFrequency_ne_neg j)), zero_add, he,
        frequencyLength_neg_axis]
      simp [Complex.norm_real, div_pow, sq_abs]
    rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have hk1 : k.val ≠ e := fun h => hk.1 (Subtype.ext h)
    have hk2 : k.val ≠ -e := fun h => hk.2 (Subtype.ext h)
    have : spectralTerm (firstShellDensity j ht) k = 0 := by
      unfold spectralTerm
      rw [hcoef k, if_neg hk1, if_neg hk2]
      simp
    rw [this, ENNReal.ofReal_zero]

/-! ### The entropy of the first-shell density -/

/-- Third-order upper bound for `(1+x) log (1+x)` near `0`. -/
lemma mul_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    (1 + x) * Real.log (1 + x) ≤ x + x ^ 2 / 2 + 2 * |x| ^ 3 := by
  have hx1 : |-x| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 3
  have e : (∑ i ∈ Finset.range 3, (-x) ^ (i + 1) / ((i : ℝ) + 1)) = -x + x ^ 2 / 2 - x ^ 3 / 3 := by
    simp [Finset.sum_range_succ]
    ring
  rw [abs_neg, sub_neg_eq_add, e] at h
  have hlog : Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 + 2 * x ^ 4 := by
    have h1 := (abs_le.mp h).2
    have h2 : |x| ^ (3 + 1) / (1 - |x|) ≤ 2 * x ^ 4 := by
      have ha : 0 ≤ |x| := abs_nonneg x
      rw [div_le_iff₀ (by linarith)]
      have : |x| ^ (3 + 1) = x ^ 4 := by rw [show (3 + 1 : ℕ) = 4 from rfl, pow_abs, abs_of_nonneg (by positivity)]
      rw [this]
      nlinarith [sq_nonneg (x ^ 2)]
    nlinarith
  have hpos : 0 ≤ 1 + x := by
    have := (abs_le.mp hx).1
    linarith
  have h3 := mul_le_mul_of_nonneg_left hlog hpos
  refine le_trans h3 ?_
  set a := |x| with ha
  have ha0 : 0 ≤ a := abs_nonneg x
  have ha1 : a ≤ 1 / 2 := hx
  have hx3 : -a ^ 3 ≤ x ^ 3 := by
    have h := (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).monotone (neg_abs_le x)
    simpa [Odd.neg_pow (by decide : Odd 3)] using h
  have hx5 : x ^ 5 ≤ a ^ 5 :=
    (Odd.strictMono_pow (R := ℝ) (by decide : Odd 5)).monotone (le_abs_self x)
  have hx4 : x ^ 4 = a ^ 4 := by rw [ha, pow_abs, abs_of_nonneg (by positivity)]
  have ha3 : a ^ 4 ≤ a ^ 3 / 2 := by nlinarith [pow_nonneg ha0 3]
  have ha5 : a ^ 5 ≤ a ^ 3 / 4 := by nlinarith [pow_nonneg ha0 3, pow_nonneg ha0 4]
  nlinarith [pow_nonneg ha0 3, pow_nonneg ha0 4]

/-- The cosine factor has integral `0`. -/
lemma integral_cos_factor (j : Fin d) :
    ∫ x : Torus d, (fourier 1 (x j)).re ∂torusMeasure d = 0 := by
  have hz : Integrable (fun x : Torus d => UnitAddTorus.mFourier (axisFrequency j) x)
      (torusMeasure d) := integrable_of_continuous_torus (continuous_mFourier' _)
  have h := integral_re hz
  rw [integral_mFourier, if_neg (axisFrequency_ne_zero' j)] at h
  simp only [mFourier_axis, RCLike.re_to_complex, Complex.zero_re] at h
  exact h

/-- The square of the cosine factor has integral `1/2`. -/
lemma integral_cos_factor_sq (j : Fin d) :
    ∫ x : Torus d, ((fourier 1 (x j)).re) ^ 2 ∂torusMeasure d = 1 / 2 := by
  have hz : Integrable (fun x : Torus d => UnitAddTorus.mFourier (axisFrequency j + axisFrequency j) x)
      (torusMeasure d) := integrable_of_continuous_torus (continuous_mFourier' _)
  have h := integral_re hz
  have hne : axisFrequency j + axisFrequency j ≠ 0 := by
    intro h0
    have := congrFun h0 j
    simp [axisFrequency] at this
  rw [integral_mFourier, if_neg hne] at h
  simp only [RCLike.re_to_complex, Complex.zero_re] at h
  have hpt : ∀ x : Torus d, ((fourier 1 (x j)).re) ^ 2 =
      (1 + (UnitAddTorus.mFourier (axisFrequency j + axisFrequency j) x).re) / 2 := by
    intro x
    rw [UnitAddTorus.mFourier_add, mFourier_axis]
    have hn : (fourier 1 (x j)).re ^ 2 + (fourier 1 (x j)).im ^ 2 = 1 := by
      have h1 := Complex.sq_norm (fourier 1 (x j))
      have hn1 : ‖fourier 1 (x j)‖ = 1 := by simp
      rw [hn1, Complex.normSq_apply] at h1
      nlinarith
    simp only [Complex.mul_re]
    nlinarith
  simp_rw [hpt]
  have hi : Integrable (fun x : Torus d => (UnitAddTorus.mFourier (axisFrequency j + axisFrequency j) x).re)
      (torusMeasure d) := hz.re
  rw [integral_div, integral_add (integrable_const _) hi]
  simp only [integral_const, probReal_univ, one_smul]
  rw [h]
  norm_num

/-- **Printed `eq:section2-first-shell-entropy` (upper bound):** for `|t| ≤ 1/2`,
`Ent(ρ_t) ≤ t²/4 + 2|t|³`. -/
theorem entropy_firstShell_le (j : Fin d) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    entropy (firstShellDensity j (by linarith : |t| < 1)) ≤ t ^ 2 / 4 + 2 * |t| ^ 3 := by
  have hC : ∀ x : Torus d, |(fourier 1 (x j)).re| ≤ 1 := fun x => by
    have := Complex.abs_re_le_norm (fourier 1 (x j))
    simpa [fourier_norm] using this
  have hcont : Continuous (fun x : Torus d => (fourier 1 (x j)).re) :=
    Complex.continuous_re.comp ((fourier 1).continuous.comp (continuous_apply j))
  have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f (torusMeasure d) :=
    fun hf => hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvc : Continuous (fun x => firstShellValue j t x * Real.log (firstShellValue j t x)) :=
    Real.continuous_mul_log.comp (continuous_firstShellValue j t)
  unfold entropy
  change ∫ x, firstShellValue j t x * Real.log (firstShellValue j t x) ∂torusMeasure d ≤ _
  have hbound : ∀ x : Torus d, firstShellValue j t x * Real.log (firstShellValue j t x) ≤
      t * (fourier 1 (x j)).re + t ^ 2 / 2 * ((fourier 1 (x j)).re) ^ 2 + 2 * |t| ^ 3 := by
    intro x
    have hxabs : |t * (fourier 1 (x j)).re| ≤ 1 / 2 := by
      rw [abs_mul]
      calc |t| * |(fourier 1 (x j)).re| ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg t)
        _ ≤ 1 / 2 := by linarith
    have h := mul_log_one_add_le hxabs
    have hx3 : |t * (fourier 1 (x j)).re| ^ 3 ≤ |t| ^ 3 := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_mul]
      calc |t| * |(fourier 1 (x j)).re| ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg t)
        _ = |t| := mul_one _
    change (1 + t * (fourier 1 (x j)).re) * Real.log (1 + t * (fourier 1 (x j)).re) ≤ _
    nlinarith [h, hx3]
  have i1 : Integrable (fun x : Torus d => t * (fourier 1 (x j)).re) (torusMeasure d) :=
    hint (continuous_const.mul hcont)
  have i2 : Integrable (fun x : Torus d => t ^ 2 / 2 * ((fourier 1 (x j)).re) ^ 2)
      (torusMeasure d) := hint (continuous_const.mul (hcont.pow 2))
  have i3 : Integrable (fun _ : Torus d => 2 * |t| ^ 3) (torusMeasure d) := integrable_const _
  have i12 : Integrable (fun x : Torus d => t * (fourier 1 (x j)).re +
      t ^ 2 / 2 * ((fourier 1 (x j)).re) ^ 2) (torusMeasure d) := i1.add i2
  calc _ ≤ ∫ x : Torus d, (t * (fourier 1 (x j)).re + t ^ 2 / 2 * ((fourier 1 (x j)).re) ^ 2 +
        2 * |t| ^ 3) ∂torusMeasure d :=
        integral_mono (hint hvc) (i12.add i3) hbound
    _ = t ^ 2 / 4 + 2 * |t| ^ 3 := by
        rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
          integral_cos_factor, integral_cos_factor_sq]
        simp only [integral_const, probReal_univ, one_smul]
        ring

/-- The first-shell density has finite entropy. -/
lemma firstShellDensity_finiteEntropy (j : Fin d) {t : ℝ} (ht : |t| < 1) :
    (firstShellDensity j ht).FiniteEntropy := by
  have hvc : Continuous (fun x => firstShellValue j t x * Real.log (firstShellValue j t x)) :=
    Real.continuous_mul_log.comp (continuous_firstShellValue j t)
  exact hvc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end BecknerOnofri.V2.Reaudit.Obstruction
