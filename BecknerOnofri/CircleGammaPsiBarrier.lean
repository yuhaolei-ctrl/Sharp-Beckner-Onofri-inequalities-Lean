module

public import BecknerOnofri.CircleGammaPsiPoly
public import BecknerOnofri.CircleRateGlobal

@[expose] public section

/-! Step 1 of the proof of Lemma 5.17 (`lem:section5-global-small-gamma`):
the quintic inverse-Riccati barrier `h̲(t) = t P(t²)/(1-t²)` lies below the
inverse Bessel mean `h(t)`, and integrating `I' = 2h ≥ 2h̲` gives `I ≥ J`.

The comparison is carried out in the Bessel variable `h` rather than in `t`:
we show `h̲(R(h)) ≤ h` for `R = I₁(2h)/I₀(2h)` by a first-contact argument
with an `ε`-boundary, which avoids differentiating the inverse function and
the power-series comparison at `t = 0` used in the manuscript. It uses
`h̲' ≥ 0`, which is checked by a Bernstein certificate. The positivity of the
sextic `ϱ` is also certified by Bernstein coefficients on four subintervals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.CircleScalar
open GammaPoly

/-- The quintic `P` of the barrier. -/
def barrierCoeffs : List ℚ := [1, -1/2, -1/12, -1/48, -1/10, 49/240]
/-- The sextic `ϱ` of the barrier residual. -/
def barrierResidualCoeffs : List ℚ :=
  [29200, -83840, 50705, 10590, -504, 23618, -21609]
/-- The numerator `(1+x)P + 2x(1-x)P'` of the barrier slope. -/
def barrierSlopeCoeffs : List ℚ :=
  add (mul [1, 1] barrierCoeffs) (mul [0, 2, -2] (derivL barrierCoeffs))

def barrierPoly (x : ℝ) : ℝ := 1 - x/2 - x^2/12 - x^3/48 - x^4/10 + 49*x^5/240
def barrierPolyDeriv (x : ℝ) : ℝ := -1/2 - x/6 - x^2/16 - 2*x^3/5 + 49*x^4/48
/-- The barrier `h̲(t) = t P(t²)/(1-t²)`. -/
def barrier (t : ℝ) : ℝ := t * barrierPoly (t^2) / (1 - t^2)
def barrierSlope (t : ℝ) : ℝ :=
  ((1 + t^2) * barrierPoly (t^2) + 2*t^2*(1 - t^2)*barrierPolyDeriv (t^2)) / (1 - t^2)^2
/-- The function `J` of `eq:simple-circle-J`. -/
def rateLower (t : ℝ) : ℝ :=
  -(1/2) * Real.log (1 - t^2) + t^2/2 - t^6/36 - 5*t^8/192 - 49*t^10/1200

theorem barrierPoly_eq (x : ℝ) : barrierPoly x = eval barrierCoeffs x := by
  simp [barrierPoly, barrierCoeffs]; ring

theorem barrierPolyDeriv_eq (x : ℝ) :
    barrierPolyDeriv x = eval (derivL barrierCoeffs) x := by
  simp only [barrierCoeffs, derivL, eval_add, eval_cons, eval_nil, barrierPolyDeriv]
  push_cast; ring

theorem barrierPoly_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < barrierPoly x := by
  rw [barrierPoly_eq]
  exact pos_of_posCheck (lo := 0) (hi := 1) (by decide +kernel) (by simpa using h0)
    (by simpa using h1)

theorem barrierSlope_num_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 < (1 + x) * barrierPoly x + 2*x*(1 - x)*barrierPolyDeriv x := by
  have he : (1 + x) * barrierPoly x + 2*x*(1 - x)*barrierPolyDeriv x =
      eval barrierSlopeCoeffs x := by
    simp only [barrierSlopeCoeffs, eval_add, eval_mul, barrierPoly_eq, barrierPolyDeriv_eq,
      eval_cons, eval_nil]
    push_cast; ring
  rw [he]
  exact pos_of_posCheck (lo := 0) (hi := 1) (by decide +kernel) (by simpa using h0)
    (by simpa using h1)

theorem barrierResidual_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 < 29200 - 83840*x + 50705*x^2 + 10590*x^3 - 504*x^4 + 23618*x^5 - 21609*x^6 := by
  have he : 29200 - 83840*x + 50705*x^2 + 10590*x^3 - 504*x^4 + 23618*x^5 - 21609*x^6 =
      eval barrierResidualCoeffs x := by
    simp [barrierResidualCoeffs]; ring
  rw [he]
  exact pos_of_posChain (a := 0) (bs := [1/2, 5/8, 3/4, 1]) (by decide +kernel)
    (by simpa using h0) (by simpa using h1)

theorem barrier_hasDerivAt {t : ℝ} (ht : t^2 ≠ 1) :
    HasDerivAt barrier (barrierSlope t) t := by
  have hd : (1 - t^2) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hP : HasDerivAt (fun s : ℝ => barrierPoly (s^2)) (barrierPolyDeriv (t^2) * (2*t)) t := by
    have h1 := (hasDerivAt_eval barrierCoeffs (t^2)).comp t (hasDerivAt_pow 2 t)
    have he : (fun s : ℝ => barrierPoly (s^2)) = (eval barrierCoeffs) ∘ (fun s => s^2) := by
      funext s; simp [barrierPoly_eq]
    rw [he, barrierPolyDeriv_eq]
    convert h1 using 1; simp
  have h := ((hasDerivAt_id t).mul hP).div ((hasDerivAt_pow 2 t).const_sub 1) hd
  have he : barrier = fun s => (id s * barrierPoly (s^2)) / (1 - s^2) := by
    funext s; simp [barrier]
  rw [he]
  convert h using 1
  simp only [barrierSlope, id, Pi.mul_apply]
  field_simp
  ring

theorem barrier_residual (t : ℝ) (ht : t^2 ≠ 1) :
    barrierSlope t * (2*(1 - t^2)*barrier t - t) - barrier t =
      -(t^9 * (29200 - 83840*t^2 + 50705*(t^2)^2 + 10590*(t^2)^3 - 504*(t^2)^4 +
        23618*(t^2)^5 - 21609*(t^2)^6)) / (28800*(1 - t^2)) := by
  have hd : (1 - t^2) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  simp only [barrierSlope, barrier, barrierPoly, barrierPolyDeriv]
  field_simp
  ring

theorem besselMoment_one_lt_one {a : ℝ} (ha : 0 ≤ a) : besselMoment 1 a < 1 := by
  have h := besselMoment_first_le_supersolution a ha
  have hs : a < Real.sqrt (1 + a^2) := by
    rw [show a = Real.sqrt (a^2) from (Real.sqrt_sq ha).symm]
    rw [Real.sqrt_sq ha]
    exact Real.lt_sqrt_of_sq_lt (by linarith)
  have hpos : 0 < Real.sqrt (1 + a^2) := Real.sqrt_pos.mpr (by positivity)
  have : a / Real.sqrt (1 + a^2) < 1 := (div_lt_one hpos).mpr hs
  linarith

theorem besselMoment_one_pos {a : ℝ} (ha : 0 < a) : 0 < besselMoment 1 a := by
  have := besselMoment_first_strictMono ha
  rwa [besselMoment_one_zero] at this

/-- The barrier comparison `h̲(R(b)) ≤ b`, in the Bessel variable. -/
theorem barrier_besselMoment_le (b : ℝ) (hb : 0 ≤ b) : barrier (besselMoment 1 b) ≤ b := by
  let R := besselMoment 1
  let f : ℝ → ℝ := fun a => barrier (R a) - a
  let f' : ℝ → ℝ := fun a =>
    barrierSlope (R a) * (1 + besselMoment 2 a - 2*(R a)^2) - 1
  have hR (a : ℝ) (ha : 0 ≤ a) : 0 ≤ R a ∧ R a < 1 :=
    ⟨besselMoment_nonneg 1 ha, besselMoment_one_lt_one ha⟩
  have hsq (a : ℝ) (ha : 0 ≤ a) : (R a)^2 ≠ 1 := by
    obtain ⟨h0, h1⟩ := hR a ha
    nlinarith
  have hd (a : ℝ) (ha : 0 ≤ a) : HasDerivAt f (f' a) a := by
    have h := ((barrier_hasDerivAt (hsq a ha)).comp a (besselMoment_first_derivative a)).sub
      (hasDerivAt_id a)
    convert h using 1
    rfl
  have hf : ContinuousOn f (Icc 0 b) := fun a ha =>
    (hd a ha.1).continuousAt.continuousWithinAt
  have hzero : f 0 = 0 := by simp [f, R, besselMoment_one_zero, barrier]
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
      set T := R a with hT
      have hT0 : 0 < T := besselMoment_one_pos hapos
      have hT1 : T < 1 := besselMoment_one_lt_one hapos.le
      have hx0 : 0 ≤ T^2 := sq_nonneg T
      have hx1 : T^2 ≤ 1 := by nlinarith
      have hden : 0 < 1 - T^2 := by nlinarith
      have hH : barrier T = a + ε := by simp only [f] at he; linarith
      have hHpos : 0 < barrier T := by linarith
      have hS : 0 ≤ barrierSlope T := by
        unfold barrierSlope
        exact div_nonneg (barrierSlope_num_pos hx0 hx1).le (by positivity)
      have hres := barrier_residual T (by nlinarith)
      have hq := barrierResidual_pos hx0 hx1
      have hneg : barrierSlope T * (2*(1 - T^2)*barrier T - T) - barrier T < 0 := by
        rw [hres]
        apply div_neg_of_neg_of_pos _ (by positivity)
        have : 0 < T^9 := by positivity
        nlinarith
      have hrec := besselMoment_recurrence a
      have hm2 : 1 + besselMoment 2 a - 2*T^2 = 2 - T/a - 2*T^2 := by
        field_simp
        simp only [hT, R] at *
        nlinarith
      have hdiv : T / barrier T ≤ T / a :=
        div_le_div_of_nonneg_left hT0.le hapos (by linarith)
      have hlt : barrierSlope T * (2 - T/barrier T - 2*T^2) < 1 := by
        have he2 : barrierSlope T * (2 - T/barrier T - 2*T^2) - 1 =
            (barrierSlope T * (2*(1 - T^2)*barrier T - T) - barrier T) / barrier T := by
          field_simp
          ring
        have : (barrierSlope T * (2*(1 - T^2)*barrier T - T) - barrier T) / barrier T < 0 :=
          div_neg_of_neg_of_pos hneg hHpos
        linarith
      have hmono := mul_le_mul_of_nonneg_left
        (show 2 - T/a - 2*T^2 ≤ 2 - T/barrier T - 2*T^2 by linarith) hS
      show barrierSlope T * (1 + besselMoment 2 a - 2*T^2) - 1 < 0
      rw [hm2]
      linarith
  simp only [f] at hfnon
  linarith

/-- The barrier lies below the inverse Bessel mean. -/
theorem barrier_le_parameter {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : barrier t ≤ parameter t := by
  obtain ⟨hm, hp⟩ := parameter_mean ht ht1
  have h := barrier_besselMoment_le (parameter t) hp
  rwa [hm] at h

theorem rateLower_hasDerivAt {t : ℝ} (ht : t^2 < 1) :
    HasDerivAt rateLower (2 * barrier t) t := by
  have hd : (1 - t^2) ≠ 0 := by nlinarith
  have hlog := ((hasDerivAt_pow 2 t).const_sub 1).log hd
  have h := ((((hlog.const_mul (-(1/2:ℝ))).add ((hasDerivAt_pow 2 t).div_const 2)).sub
    ((hasDerivAt_pow 6 t).div_const 36)).sub (((hasDerivAt_pow 8 t).const_mul 5).div_const 192)).sub
    (((hasDerivAt_pow 10 t).const_mul 49).div_const 1200)
  have he : rateLower = fun s => -(1/2) * Real.log (1 - s^2) + s^2/2 - s^6/36 -
      5*s^8/192 - 49*s^10/1200 := rfl
  rw [he]
  convert h using 1
  simp only [barrier, barrierPoly]
  field_simp
  ring

/-- Step 1: `I(t) ≥ J(t)` (`eq:simple-circle-J`). -/
theorem rateLower_le_rate {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : rateLower t ≤ rate t := by
  let R := besselMoment 1
  let g : ℝ → ℝ := fun a => rateAt a - rateLower (R a)
  let g' : ℝ → ℝ := fun a => 2*(a - barrier (R a)) * (1 + besselMoment 2 a - 2*(R a)^2)
  have hd (a : ℝ) (ha : 0 ≤ a) : HasDerivAt g (g' a) a := by
    have hR := besselMoment_first_derivative a
    have hsq : (R a)^2 < 1 := by
      have h0 := besselMoment_nonneg 1 ha
      have h1 := besselMoment_one_lt_one ha
      nlinarith
    have h := ((((hasDerivAt_id a).const_mul 2).mul hR).sub (log_bessel_derivative a)).sub
      ((rateLower_hasDerivAt hsq).comp a hR)
    have he : g = fun a => 2 * id a * besselMoment 1 a - Real.log (bessel 0 a) -
        (rateLower ∘ besselMoment 1) a := by
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
    have h1 := barrier_besselMoment_le a ha0
    have h2 := (besselMoment_first_derivative a).deriv
    have h3 := besselMoment_first_deriv_pos a
    rw [h2] at h3
    exact mul_nonneg (by linarith) h3.le
  have hz : bessel 0 0 = 1 := by
    rw [bessel_zero_eq, besselI0Two_eq_circle_integral]
    simp
  have hg0 : g 0 = 0 := by simp [g, rateAt, rateLower, R, besselMoment_one_zero, hz]
  obtain ⟨hmean, hp⟩ := parameter_mean ht ht1
  have hb := hm (by simp : (0:ℝ) ∈ Ici 0) hp hp
  rw [hg0] at hb
  simp only [g, R, hmean] at hb
  have hr : rate t = rateAt (parameter t) := by simp [rate, rateAt, hmean]
  rw [hr]
  linarith

end BecknerOnofri.HighDim.CircleScalar
