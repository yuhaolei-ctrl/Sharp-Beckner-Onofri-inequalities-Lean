module

public import Mathlib.Tactic
public import BecknerOnofri.CircleRateEntropy
public import BecknerOnofri.CircleBesselInverse
public import BecknerOnofri.V2.Circle.BaseExpansion

@[expose] public section

/-! # The global inverse-Bessel lower bound (Lemma 5.15, `d12-circle-lem:hminus`; Appendix A.2.1)

`R(h) = I_1(2h)/I_0(2h)` is `besselMoment 1`, `h(t) = parameter t` its inverse on `[0,1)`
(`parameter_mean`), `I = rate`.

* `hminus`, `hminusSlope`, `hminus_hasDerivAt`: `h_-(t) = t(1 - t^2/2 - t^4/12 - t^6/48)/(1-t^2)`.
* `hminus_residual`: the exact residual `d12-circle-eq:residual`
  `h_-'(2 h_-(1-t^2) - t) - h_- = -t^9(5t^6+25t^4+144t^2+16)/(1152(1-t^2)^2)`.
* `Iminus_hasDerivAt`: `I_-' = 2 h_-` (the integration step).
* `contact_deriv_neg`, `hminus_besselMoment_le`, `hminus_besselMoment_lt`: the comparison
  `h_-(R(b)) < b` (`b > 0`), proved by first contact in the Bessel variable `b` with an
  `epsilon`-boundary.  ROUTE DIFFERENCE from the manuscript (which compares `h` and `h_-` in the
  variable `t` after a jet at the origin): here neither the jet `h = t + t^3/2 + ... + O(t^11)`,
  nor the differentiability of the inverse, nor the first-contact lemma in `t` is used; the
  contact computation is the same one (Riccati + `d12-circle-eq:residual`).
* `hminus_lt_parameter`: `h(t) > h_-(t)` for `0 < t < 1`.
* `Iminus_le_rate`: `I(t) >= I_-(t)` for `0 <= t < 1`. -/
noncomputable section
namespace BecknerOnofri.V2.Circle
open BecknerOnofri.HighDim.CircleScalar
open Set

/-- `P(x) = 1 - x/2 - x²/12 - x³/48`, so that `h_-(t) = t P(t²)/(1-t²)` (`d12-circle-eq:hminus`). -/
def hmPoly (x : ℝ) : ℝ := 1 - x / 2 - x ^ 2 / 12 - x ^ 3 / 48
def hmPolyDeriv (x : ℝ) : ℝ := -1 / 2 - x / 6 - x ^ 2 / 16

/-- `h_-(t) = t (1 - t²/2 - t⁴/12 - t⁶/48)/(1 - t²)`. -/
noncomputable def hminus (t : ℝ) : ℝ := t * hmPoly (t ^ 2) / (1 - t ^ 2)
/-- the derivative of `h_-`. -/
noncomputable def hminusSlope (t : ℝ) : ℝ :=
  ((1 + t ^ 2) * hmPoly (t ^ 2) + 2 * t ^ 2 * (1 - t ^ 2) * hmPolyDeriv (t ^ 2)) / (1 - t ^ 2) ^ 2

theorem hminus_hasDerivAt {t : ℝ} (ht : t ^ 2 ≠ 1) : HasDerivAt hminus (hminusSlope t) t := by
  have hd : (1 - t ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hP : HasDerivAt (fun s : ℝ => hmPoly (s ^ 2)) (hmPolyDeriv (t ^ 2) * (2 * t)) t := by
    have h1 : HasDerivAt hmPoly (hmPolyDeriv (t ^ 2)) (t ^ 2) := by
      have := ((((hasDerivAt_id (t ^ 2)).div_const 2).const_sub 1).sub
        ((hasDerivAt_pow 2 (t ^ 2)).div_const 12)).sub ((hasDerivAt_pow 3 (t ^ 2)).div_const 48)
      convert this using 1
      · funext x; simp [hmPoly]
      · simp [hmPolyDeriv]; ring
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
    exact HasDerivAt.comp (h := fun s : ℝ => s ^ 2) t h1 h2
  have h := ((hasDerivAt_id t).mul hP).div ((hasDerivAt_pow 2 t).const_sub 1) hd
  have he : hminus = fun s => (id s * hmPoly (s ^ 2)) / (1 - s ^ 2) := by
    funext s; simp [hminus]
  rw [he]
  refine h.congr_deriv ?_
  simp only [hminusSlope, id, Pi.mul_apply]
  field_simp
  ring


/-- The exact residual `d12-circle-eq:residual`. -/
theorem hminus_residual {t : ℝ} (ht : t ^ 2 ≠ 1) :
    hminusSlope t * (2 * hminus t * (1 - t ^ 2) - t) - hminus t =
      -(t ^ 9 * (5 * t ^ 6 + 25 * t ^ 4 + 144 * t ^ 2 + 16)) / (1152 * (1 - t ^ 2) ^ 2) := by
  have hd : (1 - t ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  simp only [hminusSlope, hminus, hmPoly, hmPolyDeriv]
  field_simp
  ring

theorem hmPoly_pos {x : ℝ} (h1 : x ≤ 1) (h0 : 0 ≤ x) : 0 < hmPoly x := by
  unfold hmPoly; nlinarith [sq_nonneg x, pow_nonneg h0 3]

theorem hminus_slope_num_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 < (1 + x) * hmPoly x + 2 * x * (1 - x) * hmPolyDeriv x := by
  have e : (1 + x) * hmPoly x + 2 * x * (1 - x) * hmPolyDeriv x =
      1 - x / 2 + x ^ 2 / 12 + 5 * x ^ 3 / 48 + 5 * x ^ 4 / 48 := by
    unfold hmPoly hmPolyDeriv; ring
  rw [e]; have := pow_nonneg h0 3; have := pow_nonneg h0 4; nlinarith [sq_nonneg x]

section BesselFacts
open BecknerOnofri.HighDim.ContinuousGibbs BecknerOnofri.HighDim.GibbsTrialLower
  BecknerOnofri.HighDim.GinibreCovariance

/-- `d/dh log I₀(2h) = 2 I₁(2h)/I₀(2h)` (this is the repository's
`psi_log_bessel_derivative`, re-proved here to avoid importing the old barrier module). -/
theorem log_bessel_hasDerivAt (h : ℝ) :
    HasDerivAt (fun a : ℝ => Real.log (bessel 0 a)) (2 * besselMoment 1 h) h := by
  let w := (2:ℝ) • cosine (circleFrequency 1)
  have hd := (hasFDerivAt_logPartitionReal (h • w)).comp_hasDerivAt h
    ((hasDerivAt_id h).smul_const w)
  change HasDerivAt (fun a : ℝ => logPartitionReal (a • w))
    (weightedMean (h • w) (1 • w)) h at hd
  simp only [one_smul,w,← trial_one_line,trial_logPartition,Nat.cast_one,one_mul,
    map_smul,smul_eq_mul,trial_one_mean,Int.natAbs_one] at hd
  simpa only [bessel_zero_eq,besselMoment_eq] using hd

/-- `R' > 0` for `R(h) = I₁(2h)/I₀(2h)`: the derivative is twice the variance of `cos` under
the tilted law, positive because cosine is not constant. -/
theorem besselMoment_deriv_pos (h : ℝ) : 0 < deriv (besselMoment 1) h := by
  have hd := besselRatio_covariance_derivative h 1
  norm_num only [Int.natAbs_one] at hd
  have hf : besselMoment 1=(fun a => besselRatio a 1) := funext (besselMoment_eq 1)
  rw [hf]
  rw [hd.deriv]
  exact mul_pos (by norm_num) (first_cosine_variance_pos h)

theorem besselMoment_one_pos' {a : ℝ} (ha : 0 < a) : 0 < besselMoment 1 a := by
  have := besselMoment_first_strictMono ha
  rwa [besselMoment_one_zero] at this

theorem besselMoment_one_lt_one' {a : ℝ} (ha : 0 ≤ a) : besselMoment 1 a < 1 := by
  have h := besselMoment_first_le_supersolution a ha
  have hs : a < Real.sqrt (1 + a^2) := by
    rw [show a = Real.sqrt (a^2) from (Real.sqrt_sq ha).symm]
    rw [Real.sqrt_sq ha]
    exact Real.lt_sqrt_of_sq_lt (by linarith)
  have hpos : 0 < Real.sqrt (1 + a^2) := Real.sqrt_pos.mpr (by positivity)
  have : a / Real.sqrt (1 + a^2) < 1 := (div_lt_one hpos).mpr hs
  linarith

end BesselFacts

/-- Contact computation: whenever `a > 0` and `h_-(R a) ≥ a`, the derivative of
`a ↦ h_-(R a) - a` is strictly negative.  It uses the Riccati identity in the form
`1 + I₂/I₀ - 2R² = 2 - R/a - 2R²` (recurrence `a(1 - I₂/I₀) = R`) and the exact residual. -/
theorem contact_deriv_neg {a : ℝ} (ha : 0 < a) (hge : a ≤ hminus (besselMoment 1 a)) :
    hminusSlope (besselMoment 1 a) * (1 + besselMoment 2 a - 2 * (besselMoment 1 a) ^ 2) - 1 < 0 := by
  set T := besselMoment 1 a with hT
  have hT0 : 0 < T := besselMoment_one_pos' ha
  have hT1 : T < 1 := besselMoment_one_lt_one' ha.le
  have hx0 : 0 ≤ T ^ 2 := sq_nonneg T
  have hx1 : T ^ 2 ≤ 1 := by nlinarith
  have hden : 0 < 1 - T ^ 2 := by nlinarith
  have hHpos : 0 < hminus T := by linarith
  have hS : 0 ≤ hminusSlope T := by
    unfold hminusSlope
    exact div_nonneg (hminus_slope_num_pos hx0 hx1).le (by positivity)
  have hres := hminus_residual (t := T) (by nlinarith)
  have hneg : hminusSlope T * (2 * hminus T * (1 - T ^ 2) - T) - hminus T < 0 := by
    rw [hres]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have : 0 < T ^ 9 := by positivity
    have : 0 < 5 * T ^ 6 + 25 * T ^ 4 + 144 * T ^ 2 + 16 := by positivity
    nlinarith
  have hrec := besselMoment_recurrence a
  have hm2 : 1 + besselMoment 2 a - 2 * T ^ 2 = 2 - T / a - 2 * T ^ 2 := by
    field_simp
    nlinarith
  have hdiv : T / hminus T ≤ T / a := div_le_div_of_nonneg_left hT0.le ha hge
  have hlt : hminusSlope T * (2 - T / hminus T - 2 * T ^ 2) < 1 := by
    have he2 : hminusSlope T * (2 - T / hminus T - 2 * T ^ 2) - 1 =
        (hminusSlope T * (2 * hminus T * (1 - T ^ 2) - T) - hminus T) / hminus T := by
      field_simp
      ring
    have : (hminusSlope T * (2 * hminus T * (1 - T ^ 2) - T) - hminus T) / hminus T < 0 :=
      div_neg_of_neg_of_pos hneg hHpos
    linarith
  have hmono := mul_le_mul_of_nonneg_left
    (show 2 - T / a - 2 * T ^ 2 ≤ 2 - T / hminus T - 2 * T ^ 2 by linarith) hS
  rw [hm2]
  linarith

/-- Derivative of `f(a) = h_-(R(a)) - a`. -/
theorem barrier_fun_hasDerivAt {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt (fun x => hminus (besselMoment 1 x) - x)
      (hminusSlope (besselMoment 1 a) * (1 + besselMoment 2 a - 2 * (besselMoment 1 a) ^ 2) - 1) a := by
  have h0 := besselMoment_nonneg 1 ha
  have h1 := besselMoment_one_lt_one' ha
  have hsq : (besselMoment 1 a) ^ 2 ≠ 1 := by nlinarith
  have h := ((hminus_hasDerivAt hsq).comp a (besselMoment_first_derivative a)).sub (hasDerivAt_id a)
  exact h

/-- Nonstrict barrier comparison `h_-(R(b)) ≤ b` in the Bessel variable (first contact with an
`ε`-boundary; no jet at the origin and no differentiation of the inverse). -/
theorem hminus_besselMoment_le (b : ℝ) (hb : 0 ≤ b) : hminus (besselMoment 1 b) ≤ b := by
  let R := besselMoment 1
  let f : ℝ → ℝ := fun a => hminus (R a) - a
  have hd (a : ℝ) (ha : 0 ≤ a) := barrier_fun_hasDerivAt ha
  have hf : ContinuousOn f (Icc 0 b) := fun a ha => (hd a ha.1).continuousAt.continuousWithinAt
  have hzero : f 0 = 0 := by simp [f, R, besselMoment_one_zero, hminus]
  have hfnon : f b ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hbound := image_le_of_deriv_right_lt_deriv_boundary
      (a := 0) (b := b) hf
      (fun a ha => (hd a ha.1).hasDerivWithinAt)
      (B := fun _ : ℝ => ε) (B' := fun _ => 0)
      (by simpa [hzero] using hε.le)
      (fun a => hasDerivAt_const a ε) (fun a ha he => ?_)
      (show b ∈ Icc (0:ℝ) b from ⟨hb, le_rfl⟩)
    · simpa using hbound
    · have hapos : 0 < a := by
        by_contra hn
        have hz : a = 0 := le_antisymm (le_of_not_gt hn) ha.1
        rw [hz, hzero] at he
        linarith
      have hge : a ≤ hminus (R a) := by simp only [f] at he; linarith
      exact contact_deriv_neg hapos hge
  simp only [f] at hfnon
  linarith

/-- Strict barrier comparison `h_-(R(b)) < b` for `b > 0`. -/
theorem hminus_besselMoment_lt {b : ℝ} (hb : 0 < b) : hminus (besselMoment 1 b) < b := by
  by_contra hcon
  have heq : hminus (besselMoment 1 b) = b :=
    le_antisymm (hminus_besselMoment_le b hb.le) (not_lt.mp hcon)
  have hmax : IsLocalMax (fun x => hminus (besselMoment 1 x) - x) b := by
    filter_upwards [Ioi_mem_nhds hb] with x hx
    have := hminus_besselMoment_le x (le_of_lt hx)
    show hminus (besselMoment 1 x) - x ≤ hminus (besselMoment 1 b) - b
    linarith
  have hz := hmax.hasDerivAt_eq_zero (barrier_fun_hasDerivAt hb.le)
  have hneg := contact_deriv_neg hb (le_of_eq heq.symm)
  linarith


/-- `I_-' = 2 h_-`: the integration step in the proof of `d12-circle-lem:hminus`. -/
theorem Iminus_hasDerivAt {t : ℝ} (ht : t ^ 2 < 1) : HasDerivAt Iminus (2 * hminus t) t := by
  have hd : (1 - t ^ 2) ≠ 0 := by nlinarith
  have hlog := ((hasDerivAt_pow 2 t).const_sub 1).log hd
  have h := ((((hasDerivAt_pow 2 t).const_mul (29 / 48 : ℝ)).add
      (((hasDerivAt_pow 4 t).const_mul (5 / 96 : ℝ)))).add
      ((hasDerivAt_pow 6 t).const_mul (1 / 144 : ℝ))).sub (hlog.const_mul (19 / 48 : ℝ))
  have he : Iminus = fun s => 29 / 48 * s ^ 2 + 5 / 96 * s ^ 4 + 1 / 144 * s ^ 6 -
      19 / 48 * Real.log (1 - s ^ 2) := by
    funext s; simp only [Iminus]; ring_nf
  rw [he]
  refine h.congr_deriv ?_
  simp only [hminus, hmPoly]
  field_simp
  ring

/-- `I(t) ≥ I_-(t)` in the Bessel variable: `rateAt a ≥ I_-(R a)` for `a ≥ 0`. -/
theorem Iminus_le_rateAt {a : ℝ} (ha : 0 ≤ a) : Iminus (besselMoment 1 a) ≤ rateAt a := by
  let R := besselMoment 1
  let g : ℝ → ℝ := fun a => rateAt a - Iminus (R a)
  let g' : ℝ → ℝ := fun a => 2 * (a - hminus (R a)) * (1 + besselMoment 2 a - 2 * (R a) ^ 2)
  have hd (a : ℝ) (ha : 0 ≤ a) : HasDerivAt g (g' a) a := by
    have hR := besselMoment_first_derivative a
    have hsq : (R a) ^ 2 < 1 := by
      have h0 := besselMoment_nonneg 1 ha
      have h1 := besselMoment_one_lt_one' ha
      nlinarith
    have h := ((((hasDerivAt_id a).const_mul 2).mul hR).sub (log_bessel_hasDerivAt a)).sub
      ((Iminus_hasDerivAt hsq).comp a hR)
    have he : g = fun a => 2 * id a * besselMoment 1 a - Real.log (bessel 0 a) -
        (Iminus ∘ besselMoment 1) a := by
      funext a; simp [g, rateAt, R]
    rw [he]
    convert h using 1
    simp only [g', R, id]
    ring
  have hm : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun a ha => (hd a ha).continuousAt.continuousWithinAt)
      (fun a ha => (hd a (interior_subset ha)).hasDerivWithinAt)
    intro a ha
    have ha0 : 0 ≤ a := interior_subset ha
    have h1 := hminus_besselMoment_le a ha0
    have h2 := (besselMoment_first_derivative a).deriv
    have h3 := besselMoment_deriv_pos a
    rw [h2] at h3
    exact mul_nonneg (by linarith) h3.le
  have hz : bessel 0 0 = 1 := by
    rw [bessel_zero_eq, BecknerOnofri.HighDim.besselI0Two_eq_circle_integral]
    simp
  have hg0 : g 0 = 0 := by simp [g, rateAt, Iminus, R, besselMoment_one_zero, hz]
  have hb := hm (by simp : (0:ℝ) ∈ Ici 0) ha ha
  rw [hg0] at hb
  simp only [g, R] at hb
  linarith

/-- Lemma 5.15 (`d12-circle-lem:hminus`), first part: `h(t) > h_-(t)` for `0 < t < 1`
(`h = parameter`, the inverse of `R = I₁(2·)/I₀(2·)`). -/
theorem hminus_lt_parameter {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : hminus t < parameter t := by
  obtain ⟨hm, hp⟩ := parameter_mean ht.le ht1
  have hpos : 0 < parameter t := by
    rcases hp.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, besselMoment_one_zero] at hm; linarith
  have h := hminus_besselMoment_lt hpos
  rwa [hm] at h

/-- Lemma 5.15, second part: `I(t) ≥ I_-(t)` for `0 ≤ t < 1`, `I = rate`. -/
theorem Iminus_le_rate {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : Iminus t ≤ rate t := by
  obtain ⟨hm, hp⟩ := parameter_mean ht ht1
  have h := Iminus_le_rateAt hp
  rw [hm] at h
  have hr : rate t = rateAt (parameter t) := by simp [rate, rateAt, hm]
  rw [hr]; exact h

end BecknerOnofri.V2.Circle
