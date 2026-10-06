module

public import BecknerOnofri.SpinReferenceDefinitions
public import BecknerOnofri.SpinBinaryCost
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Arsinh

@[expose] public section

/-!
# A Jensen remainder (Lemma 5.20, lem:section5-jensen-remainder)

For `0 ≤ t < 1` and `s ∈ [0,1]`, the Bregman gaps of `ψ` and of the binary entropy `I_B`
satisfy `D_ψ(s,t) ≥ η(t) D_{I_B}(s,t)`. Taking expectations gives
`E ψ(S) - ψ(t) ≥ η(t) (E I_B(S) - I_B(t))` whenever `E S = t`.

The proof follows the manuscript: `φ'' = I_B'' (𝓡 - η(t))` with `𝓡 = ψ''/I_B''`
quasi-concave, so `φ` is convex near `t` and concave near the endpoints; it remains to check
`φ(0) ≥ 0` and `φ(1) ≥ 0`.
-/

noncomputable section

open Set

namespace BecknerOnofri.HighDim.Spin

/-! ### A sign-pattern lemma -/

/-- If `f(t) = f'(t) = 0`, `f(b) ≥ 0`, and `f''` stays nonpositive once it is nonpositive on
`(t,b)`, then `f ≥ 0` on `[t,b]`. -/
theorem nonneg_of_second_derivative_pattern {f f' f'' : ℝ → ℝ} {t b : ℝ}
    (hcont : ContinuousOn f (Icc t b))
    (hf : ∀ s ∈ Ico t b, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Ico t b, HasDerivAt f' (f'' s) s)
    (h0 : f t = 0) (h1 : f' t = 0) (hb : 0 ≤ f b)
    (hpat : ∀ s ∈ Ioo t b, f'' s ≤ 0 → ∀ u ∈ Ioo s b, f'' u ≤ 0) :
    ∀ s ∈ Icc t b, 0 ≤ f s := by
  intro s hs
  by_contra hneg
  push Not at hneg
  have hst : t < s := lt_of_le_of_ne hs.1 (by rintro rfl; linarith)
  have hsb : s < b := lt_of_le_of_ne hs.2 (by rintro rfl; linarith)
  -- a point of negative slope
  obtain ⟨c, hc, hfc⟩ := exists_hasDerivAt_eq_slope f f' hst
    (hcont.mono (Icc_subset_Icc le_rfl hsb.le))
    (fun x hx => hf x ⟨hx.1.le, hx.2.trans hsb⟩)
  have hc' : f' c < 0 := by
    rw [hfc, h0, sub_zero]
    exact div_neg_of_neg_of_pos hneg (by linarith)
  -- a point of negative curvature before it
  have hcont' : ContinuousOn f' (Icc t c) := fun x hx =>
    (hf' x ⟨hx.1, hx.2.trans_lt (hc.2.trans hsb)⟩).continuousAt.continuousWithinAt
  obtain ⟨d, hd, hfd⟩ := exists_hasDerivAt_eq_slope f' f'' hc.1 hcont'
    (fun x hx => hf' x ⟨hx.1.le, hx.2.trans (hc.2.trans hsb)⟩)
  have hd' : f'' d ≤ 0 := by
    rw [hfd, h1, sub_zero]
    exact (div_neg_of_neg_of_pos hc' (by linarith [hc.1])).le
  have hneg2 : ∀ u ∈ Ioo d b, f'' u ≤ 0 :=
    hpat d ⟨hd.1, hd.2.trans (hc.2.trans hsb)⟩ hd'
  -- `f'` stays negative after `c`
  have hfneg : ∀ u ∈ Ico c b, f' u < 0 := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]; exact hc'
    have hcu : ContinuousOn f' (Icc c u) := fun x hx =>
      (hf' x ⟨hc.1.le.trans hx.1, hx.2.trans_lt hu.2⟩).continuousAt.continuousWithinAt
    obtain ⟨e, he, hfe⟩ := exists_hasDerivAt_eq_slope f' f'' h hcu
      (fun x hx => hf' x ⟨hc.1.le.trans hx.1.le, hx.2.trans hu.2⟩)
    have hle := hneg2 e ⟨hd.2.trans he.1, he.2.trans hu.2⟩
    rw [hfe] at hle
    have : f' u - f' c ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have := div_pos hpos (sub_pos.mpr h)
      linarith
    linarith
  -- hence `f b < f s < 0`
  obtain ⟨e, he, hfe⟩ := exists_hasDerivAt_eq_slope f f' hsb
    (hcont.mono (Icc_subset_Icc hst.le le_rfl))
    (fun x hx => hf x ⟨hst.le.trans hx.1.le, hx.2⟩)
  have hfe' := hfneg e ⟨(hc.2.trans he.1).le, he.2⟩
  rw [hfe] at hfe'
  have : f b - f s < 0 := by
    by_contra hpos
    push Not at hpos
    have := div_nonneg hpos (sub_pos.mpr hsb).le
    linarith
  linarith

/-- The mirror image of `nonneg_of_second_derivative_pattern` on `[a,t]`. -/
theorem nonneg_of_second_derivative_pattern_left {f f' f'' : ℝ → ℝ} {a t : ℝ}
    (hcont : ContinuousOn f (Icc a t))
    (hf : ∀ s ∈ Ioc a t, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Ioc a t, HasDerivAt f' (f'' s) s)
    (h0 : f t = 0) (h1 : f' t = 0) (ha : 0 ≤ f a)
    (hpat : ∀ s ∈ Ioo a t, f'' s ≤ 0 → ∀ u ∈ Ioo a s, f'' u ≤ 0) :
    ∀ s ∈ Icc a t, 0 ≤ f s := by
  intro s hs
  have h := nonneg_of_second_derivative_pattern (f := fun x => f (-x)) (f' := fun x => -f' (-x))
    (f'' := fun x => f'' (-x)) (t := -t) (b := -a)
    (hcont.comp continuous_neg.continuousOn (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩))
    (fun x hx => by
      have := (hf (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩).comp x (hasDerivAt_neg x)
      simpa [Function.comp_def] using this)
    (fun x hx => by
      have := ((hf' (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩).comp x (hasDerivAt_neg x)).neg
      simp only [Function.comp_def, mul_neg, mul_one, neg_neg] at this
      exact this)
    (by simpa using h0) (by simp [h1]) (by simpa using ha)
    (fun x hx hx0 u hu => hpat (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ hx0 (-u)
      ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  simpa using h

/-! ### The functions `ψ`, `η`, `𝓡` -/

/-- `ψ'(t)`. -/
def psiSlope (t : ℝ) : ℝ := 3 / 10 * t ^ 3 + 33 / 20 * t ^ 9

/-- `ψ''(t)`. -/
def psiHessian (t : ℝ) : ℝ := 9 / 10 * t ^ 2 + 297 / 20 * t ^ 8

theorem psi_hasDerivAt (t : ℝ) : HasDerivAt psi (psiSlope t) t := by
  have h := (((hasDerivAt_id t).pow 4).const_mul (3 / 40 : ℝ)).add
    (((hasDerivAt_id t).pow 10).const_mul (33 / 200 : ℝ))
  convert h using 1
  · ext x; simp [psi]
  · simp [psiSlope]; try ring

theorem psiSlope_hasDerivAt (t : ℝ) : HasDerivAt psiSlope (psiHessian t) t := by
  have h := (((hasDerivAt_id t).pow 3).const_mul (3 / 10 : ℝ)).add
    (((hasDerivAt_id t).pow 9).const_mul (33 / 20 : ℝ))
  convert h using 1
  · ext x; simp [psiSlope]
  · simp [psiHessian]; try ring

/-- The ratio `𝓡(s) = ψ''(s)/I_B''(s) = (1-s²)(9s²/10 + 297s⁸/20)`, as a function of `y = s²`. -/
def ratioPoly (y : ℝ) : ℝ := (1 - y) * (9 / 10 * y + 297 / 20 * y ^ 4)

/-- `d𝓡/dy`. -/
def ratioSlope (y : ℝ) : ℝ := 9 / 10 - 9 / 5 * y + 297 / 5 * y ^ 3 - 297 / 4 * y ^ 4

/-- `d²𝓡/dy²`. -/
def ratioHessian (y : ℝ) : ℝ := -9 / 5 + 891 / 5 * y ^ 2 - 297 * y ^ 3

theorem ratioPoly_hasDerivAt (y : ℝ) : HasDerivAt ratioPoly (ratioSlope y) y := by
  have h := ((hasDerivAt_id y).const_sub (1 : ℝ)).mul
    (((hasDerivAt_id y).const_mul (9 / 10 : ℝ)).add
      (((hasDerivAt_id y).pow 4).const_mul (297 / 20 : ℝ)))
  convert h using 1
  · ext x; simp [ratioPoly]
  · simp [ratioSlope]; ring

theorem ratioSlope_hasDerivAt (y : ℝ) : HasDerivAt ratioSlope (ratioHessian y) y := by
  have h := ((((hasDerivAt_id y).const_mul (9 / 5 : ℝ)).const_sub (9 / 10 : ℝ)).add
    (((hasDerivAt_id y).pow 3).const_mul (297 / 5 : ℝ))).sub
    (((hasDerivAt_id y).pow 4).const_mul (297 / 4 : ℝ))
  convert h using 1
  · ext x; simp [ratioSlope]; try ring
  · simp [ratioHessian]; ring

theorem ratioPoly_continuous : Continuous ratioPoly := by
  unfold ratioPoly; fun_prop

theorem ratioPoly_monotoneOn : MonotoneOn ratioPoly (Icc 0 (3 / 5)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := ratioSlope) (convex_Icc _ _)
    ratioPoly_continuous.continuousOn
    (fun y _ => (ratioPoly_hasDerivAt y).hasDerivWithinAt)
  intro y hy
  rw [interior_Icc] at hy
  have h1 := hy.1
  have h2 := hy.2
  unfold ratioSlope
  nlinarith [mul_pos h1 h1, pow_pos h1 3, pow_pos h1 4, mul_pos (mul_pos h1 h1) (sub_pos.mpr h2),
    mul_pos (pow_pos h1 3) (sub_pos.mpr h2)]

theorem ratioPoly_concaveOn : ConcaveOn ℝ (Icc (3 / 5) 1) ratioPoly := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := ratioSlope) (f'' := ratioHessian)
    (convex_Icc _ _) ratioPoly_continuous.continuousOn
    (fun y _ => (ratioPoly_hasDerivAt y).hasDerivWithinAt)
    (fun y _ => (ratioSlope_hasDerivAt y).hasDerivWithinAt)
  intro y hy
  rw [interior_Icc] at hy
  have h1 := hy.1
  unfold ratioHessian
  nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ y by linarith))
    (show (0 : ℝ) ≤ 5 * y - 3 by linarith)]

/-- `ratioPoly` is quasi-concave on `[0,1]`. -/
theorem ratioPoly_quasiconcave {u v w : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvw : v ≤ w) (hw : w ≤ 1) :
    min (ratioPoly u) (ratioPoly w) ≤ ratioPoly v := by
  by_cases hv : v ≤ 3 / 5
  · exact (min_le_left _ _).trans (ratioPoly_monotoneOn ⟨hu, huv.trans hv⟩ ⟨hu.trans huv, hv⟩ huv)
  push Not at hv
  by_cases hu' : 3 / 5 ≤ u
  · exact ratioPoly_concaveOn.min_le_of_mem_Icc ⟨hu', (huv.trans hvw).trans hw⟩
      ⟨hu'.trans (huv.trans hvw), hw⟩ ⟨huv, hvw⟩
  push Not at hu'
  have h1 := ratioPoly_concaveOn.min_le_of_mem_Icc (x := 3 / 5) (y := w) ⟨le_rfl, by norm_num⟩
    ⟨by linarith, hw⟩ ⟨hv.le, hvw⟩
  have h2 := ratioPoly_monotoneOn ⟨hu, hu'.le⟩ ⟨by norm_num, le_rfl⟩ hu'.le
  calc min (ratioPoly u) (ratioPoly w) ≤ min (ratioPoly (3 / 5)) (ratioPoly w) :=
        min_le_min_right _ h2
    _ ≤ _ := h1

theorem eta_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ eta t := by
  unfold eta
  apply div_nonneg _ (by nlinarith)
  exact mul_nonneg (by nlinarith) (by positivity)

/-- `𝓡(t) > η(t)` for `0 < t < 1`. -/
theorem eta_lt_ratio {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : eta t < ratioPoly (t ^ 2) := by
  have h2 : 0 < 1 - t ^ 2 / 2 := by nlinarith
  unfold eta ratioPoly
  rw [div_lt_iff₀ h2]
  have ht2 : 0 < t ^ 2 := by positivity
  have h1t : 0 < 1 - t ^ 2 := by nlinarith
  have key : (1 - t ^ 2) * (9 / 10 * t ^ 2 + 297 / 20 * (t ^ 2) ^ 4) * (1 - t ^ 2 / 2) -
      (1 - t ^ 2) * (9 / 20 * t ^ 2 + 297 / 100 * t ^ 8) =
      9 * t ^ 2 * (1 - t ^ 2) / 200 * (264 * t ^ 6 - 165 * t ^ 8 + 10 * (1 - t ^ 2)) := by ring
  have hp : 0 < 264 * t ^ 6 - 165 * t ^ 8 + 10 * (1 - t ^ 2) := by
    have : t ^ 8 ≤ t ^ 6 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
    nlinarith [pow_pos ht0 6]
  have := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 9) ht2) h1t) hp
  nlinarith

/-! ### The Bregman gap -/

/-- `φ_t(s) = D_ψ(s,t) - η(t) D_{I_B}(s,t)`. -/
def jensenGap (t s : ℝ) : ℝ :=
  psi s - psi t - psiSlope t * (s - t) -
    eta t * (binaryCost s - binaryCost t - binaryCostSlope t * (s - t))

/-- `log x ≤ (x - x⁻¹)/2` for `x ≥ 1`. -/
theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ (x - x⁻¹) / 2 := by
  have hx0 : 0 < x := by linarith
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hx)
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log hx0] at h
  exact h

/-- The endpoint `s = 0`. -/
theorem jensenGap_zero {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 ≤ jensenGap t 0 := by
  have h1t : 0 < 1 - t ^ 2 := by nlinarith
  have hp : 0 < 1 + t := by linarith
  have hm : 0 < 1 - t := by linarith
  -- `D_{I_B}(0,t) = -log(1-t²)/2 ≤ t²(2-t²)/(4(1-t²))`
  have hD : binaryCost 0 - binaryCost t - binaryCostSlope t * (0 - t) =
      Real.log ((1 - t ^ 2)⁻¹) / 2 := by
    unfold binaryCost binaryCostSlope
    rw [Real.log_inv, show 1 - t ^ 2 = (1 + t) * (1 - t) by ring, Real.log_mul hp.ne' hm.ne']
    simp
    ring
  have hlog := log_le_half_sub_inv (x := (1 - t ^ 2)⁻¹) (one_le_inv₀ h1t |>.mpr (by nlinarith))
  rw [inv_inv] at hlog
  have hbound : Real.log ((1 - t ^ 2)⁻¹) / 2 ≤ t ^ 2 * (2 - t ^ 2) / (4 * (1 - t ^ 2)) := by
    have : ((1 - t ^ 2)⁻¹ - (1 - t ^ 2)) / 2 / 2 = t ^ 2 * (2 - t ^ 2) / (4 * (1 - t ^ 2)) := by
      field_simp
      ring
    linarith
  have heta := eta_nonneg ht0 ht1.le
  have hexact : eta t * (t ^ 2 * (2 - t ^ 2) / (4 * (1 - t ^ 2))) =
      9 / 40 * t ^ 4 + 297 / 200 * t ^ 10 := by
    unfold eta
    have h2 : (1 - t ^ 2 / 2) ≠ 0 := by nlinarith
    have h3 : (2 - t ^ 2) ≠ 0 := by nlinarith
    rw [show 1 - t ^ 2 / 2 = (2 - t ^ 2) / 2 by ring]
    field_simp
    ring
  unfold jensenGap
  rw [hD]
  have hψ : psi 0 - psi t - psiSlope t * (0 - t) = 9 / 40 * t ^ 4 + 297 / 200 * t ^ 10 := by
    simp [psi, psiSlope]; ring
  rw [hψ]
  nlinarith [mul_le_mul_of_nonneg_left hbound heta]

/-- The endpoint `s = 1`. -/
theorem jensenGap_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 ≤ jensenGap t 1 := by
  have hp : 0 < 1 + t := by linarith
  have hm : 0 < 1 - t := by linarith
  have hD : binaryCost 1 - binaryCost t - binaryCostSlope t * (1 - t) =
      Real.log (2 / (1 + t)) := by
    unfold binaryCost binaryCostSlope
    rw [Real.log_div (by norm_num) hp.ne']
    norm_num
    ring
  have hlog : Real.log (2 / (1 + t)) ≤ (1 - t) / (1 + t) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 / (1 + t) by positivity)
    have he : 2 / (1 + t) - 1 = (1 - t) / (1 + t) := by field_simp; ring
    linarith
  have heta := eta_nonneg ht0 ht1.le
  -- `D_ψ(1,t) ≥ η(t)(1-t)/(1+t)`
  have hpoly : eta t * ((1 - t) / (1 + t)) ≤ psi 1 - psi t - psiSlope t * (1 - t) := by
    have h2 : 0 < 1 - t ^ 2 / 2 := by nlinarith
    have hrw : eta t * ((1 - t) / (1 + t)) =
        (1 - t) ^ 2 * (9 / 20 * t ^ 2 + 297 / 100 * t ^ 8) / (1 - t ^ 2 / 2) := by
      unfold eta
      field_simp
      ring
    rw [hrw, div_le_iff₀ h2]
    -- `400 (1 - t²/2) Q(t) - 400 (9t²/20 + 297t⁸/100) ≥ 207 t⁷ ≥ 0`
    have hQ : psi 1 - psi t - psiSlope t * (1 - t) =
        (1 - t) ^ 2 * (3 / 40 * (1 + 2 * t + 3 * t ^ 2) + 33 / 200 *
          (1 + 2 * t + 3 * t ^ 2 + 4 * t ^ 3 + 5 * t ^ 4 + 6 * t ^ 5 + 7 * t ^ 6 + 8 * t ^ 7 +
            9 * t ^ 8)) := by
      simp [psi, psiSlope]; ring
    rw [hQ]
    have hk (k : ℕ) (hk : k ≤ 7) : t ^ 7 ≤ t ^ k := pow_le_pow_of_le_one ht0 ht1.le hk
    have hk' (k : ℕ) (hk : 7 ≤ k) : t ^ k ≤ t ^ 7 := pow_le_pow_of_le_one ht0 ht1.le hk
    have hpoly : 0 ≤ (1 - t ^ 2 / 2) * (3 / 40 * (1 + 2 * t + 3 * t ^ 2) + 33 / 200 *
          (1 + 2 * t + 3 * t ^ 2 + 4 * t ^ 3 + 5 * t ^ 4 + 6 * t ^ 5 + 7 * t ^ 6 + 8 * t ^ 7 +
            9 * t ^ 8)) - (9 / 20 * t ^ 2 + 297 / 100 * t ^ 8) := by
      nlinarith [hk 0 (by norm_num), hk 1 (by norm_num), hk 2 (by norm_num), hk 3 (by norm_num),
        hk 4 (by norm_num), hk 5 (by norm_num), hk 6 (by norm_num), hk' 8 (by norm_num),
        hk' 9 (by norm_num), hk' 10 (by norm_num), pow_nonneg ht0 7]
    nlinarith [mul_nonneg (sq_nonneg (1 - t)) hpoly]
  unfold jensenGap
  rw [hD]
  nlinarith [mul_le_mul_of_nonneg_left hlog heta]

/-- The derivative of `s ↦ φ_t(s)`. -/
def jensenGapSlope (t s : ℝ) : ℝ :=
  psiSlope s - psiSlope t - eta t * (binaryCostSlope s - binaryCostSlope t)

/-- The second derivative of `s ↦ φ_t(s)`. -/
def jensenGapHessian (t s : ℝ) : ℝ := psiHessian s - eta t * binaryCostHessian s

theorem jensenGap_hasDerivAt (t : ℝ) {s : ℝ} (hs0 : -1 < s) (hs1 : s < 1) :
    HasDerivAt (jensenGap t) (jensenGapSlope t s) s := by
  have h := (((psi_hasDerivAt s).sub_const (psi t)).sub
    (((hasDerivAt_id s).sub_const t).const_mul (psiSlope t))).sub
    ((((binaryCost_derivative s hs0 hs1).sub_const (binaryCost t)).sub
      (((hasDerivAt_id s).sub_const t).const_mul (binaryCostSlope t))).const_mul (eta t))
  convert h using 1
  · ext x; simp [jensenGap]
  · simp [jensenGapSlope]; try ring

theorem jensenGapSlope_hasDerivAt (t : ℝ) {s : ℝ} (hs0 : -1 < s) (hs1 : s < 1) :
    HasDerivAt (jensenGapSlope t) (jensenGapHessian t s) s := by
  have h := ((psiSlope_hasDerivAt s).sub_const (psiSlope t)).sub
    (((binaryCost_second_derivative s hs0 hs1).sub_const (binaryCostSlope t)).const_mul (eta t))
  convert h using 1
  · ext x; simp [jensenGapSlope]
  · simp [jensenGapHessian]

theorem jensenGap_continuousOn (t : ℝ) : ContinuousOn (jensenGap t) (Icc 0 1) := by
  unfold jensenGap psi
  exact (by
    have := binaryCost_continuous
    fun_prop : Continuous fun s => 3 / 40 * s ^ 4 + 33 / 200 * s ^ 10 - psi t -
      psiSlope t * (s - t) - eta t * (binaryCost s - binaryCost t - binaryCostSlope t * (s - t)))
    |>.continuousOn

/-- `φ_t'' ≤ 0` exactly when `𝓡 ≤ η(t)`. -/
theorem jensenGapHessian_nonpos_iff {t s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    jensenGapHessian t s ≤ 0 ↔ ratioPoly (s ^ 2) ≤ eta t := by
  have h1s : 0 < 1 - s ^ 2 := by nlinarith
  have key : ratioPoly (s ^ 2) - eta t = (1 - s ^ 2) * jensenGapHessian t s := by
    unfold ratioPoly jensenGapHessian psiHessian binaryCostHessian
    field_simp
    try ring
  constructor
  · intro h
    have := mul_nonpos_of_nonneg_of_nonpos h1s.le h
    linarith
  · intro h
    by_contra hc
    push Not at hc
    have := mul_pos h1s hc
    linarith

/-- **Lemma 5.20**, pointwise form: `D_ψ(s,t) ≥ η(t) D_{I_B}(s,t)` for `0 ≤ t < 1`,
`0 ≤ s ≤ 1`. -/
theorem jensenGap_nonneg {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ jensenGap t s := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · have : eta 0 = 0 := by simp [eta]
    simp only [jensenGap, this, zero_mul, sub_zero]
    simp [psi, psiSlope]
    positivity
  have hRt := eta_lt_ratio htpos ht1
  have hquasi : ∀ {u v w : ℝ}, 0 ≤ u → u ≤ v → v ≤ w → w ≤ 1 →
      min (ratioPoly (u ^ 2)) (ratioPoly (w ^ 2)) ≤ ratioPoly (v ^ 2) := by
    intro u v w hu huv hvw hw
    exact ratioPoly_quasiconcave (sq_nonneg u) (pow_le_pow_left₀ hu huv 2)
      (pow_le_pow_left₀ (hu.trans huv) hvw 2) (by nlinarith)
  have h0 : jensenGap t t = 0 := by simp [jensenGap]
  have h1 : jensenGapSlope t t = 0 := by simp [jensenGapSlope]
  rcases le_total t s with hts | hst
  · apply nonneg_of_second_derivative_pattern (f' := jensenGapSlope t)
      (f'' := jensenGapHessian t) ((jensenGap_continuousOn t).mono (Icc_subset_Icc ht0 le_rfl))
      (fun x hx => jensenGap_hasDerivAt t (by linarith [hx.1]) hx.2)
      (fun x hx => jensenGapSlope_hasDerivAt t (by linarith [hx.1]) hx.2)
      h0 h1 (jensenGap_one ht0 ht1) _ s ⟨hts, hs1⟩
    intro x hx hx0 u hu
    rw [jensenGapHessian_nonpos_iff (by linarith [hx.1]) hx.2] at hx0
    rw [jensenGapHessian_nonpos_iff (by linarith [hu.1, hx.1]) hu.2]
    by_contra hc
    push Not at hc
    have := hquasi ht0 hx.1.le hu.1.le hu.2.le
    have : eta t < min (ratioPoly (t ^ 2)) (ratioPoly (u ^ 2)) := lt_min hRt hc
    linarith
  · apply nonneg_of_second_derivative_pattern_left (f' := jensenGapSlope t)
      (f'' := jensenGapHessian t) ((jensenGap_continuousOn t).mono (Icc_subset_Icc le_rfl ht1.le))
      (fun x hx => jensenGap_hasDerivAt t (by linarith [hx.1]) (by linarith [hx.2]))
      (fun x hx => jensenGapSlope_hasDerivAt t (by linarith [hx.1]) (by linarith [hx.2]))
      h0 h1 (jensenGap_zero ht0 ht1) _ s ⟨hs0, hst⟩
    intro x hx hx0 u hu
    rw [jensenGapHessian_nonpos_iff hx.1.le (by linarith [hx.2])] at hx0
    rw [jensenGapHessian_nonpos_iff hu.1.le (by linarith [hu.2, hx.2])]
    by_contra hc
    push Not at hc
    have := hquasi hu.1.le hu.2.le hx.2.le ht1.le
    have : eta t < min (ratioPoly (u ^ 2)) (ratioPoly (t ^ 2)) := lt_min hc hRt
    linarith

end BecknerOnofri.HighDim.Spin
