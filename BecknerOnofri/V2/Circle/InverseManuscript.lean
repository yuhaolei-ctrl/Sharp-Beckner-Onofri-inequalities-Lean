module

public import Mathlib.Tactic
public import BecknerOnofri.V2.Circle.JetAtOrigin

@[expose] public section

/-! # Lemma 5.15 along the manuscript route (`d12-circle-lem:hminus`, Appendix A.2.1)

The manuscript proves `h_-(t) < h(t)` on `(0,1)` by: jet at the origin (`JetAtOrigin`), the
differentiability of the inverse `h = parameter` with `h'(t) = h/(2h(1-t^2)-t)`
(`d12-circle-eq:riccati`, positive denominator), the exact residual (`hminus_residual`), and a
first-contact argument in `t`.  This module formalizes exactly that route; its conclusions are
named without suffix:

* `parameter_continuousOn`: `h` is continuous on `[0,1)`;
* `parameter_hasDerivAt`: `h'(t) = h/(2h(1-t^2)-t)` and the denominator is positive, `0 < t < 1`;
* `first_contact`: the abstract first-contact lemma;
* `hminus_lt_parameter_t`: `h_-(t) < h(t)` for `0 < t < 1`;
* `rate_hasDerivAt`: `I'(t) = 2 h(t)`;
* `Iminus_le_rate_t`: `I_-(t) <= I(t)` for `0 <= t < 1` by integrating `I' = 2h >= 2 h_- = I_-'`.
-/
noncomputable section
open Set Filter Topology
open BecknerOnofri.HighDim.CircleScalar
namespace BecknerOnofri.V2.Circle

/-- **First-contact lemma.**  Let `g` be continuous on the compact interval `[a, T]`, positive at `a`
and suppose that at every zero `t₀ ∈ [a, T]` of `g` the function is differentiable with positive
derivative (the hypothesis one obtains from a strict differential inequality at the contact point).
Then `g > 0` on all of `[a, T]`. -/
theorem first_contact {g : ℝ → ℝ} {a T : ℝ} (hcont : ContinuousOn g (Icc a T)) (hpos : 0 < g a)
    (hzero : ∀ t ∈ Icc a T, g t = 0 → ∃ g', HasDerivAt g g' t ∧ 0 < g') :
    ∀ t ∈ Icc a T, 0 < g t := by
  by_contra hcon
  simp only [not_forall, not_lt] at hcon
  obtain ⟨t1, ht1, hg1⟩ := hcon
  set S : Set ℝ := Icc a T ∩ g ⁻¹' Iic 0 with hS
  have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t1, ht1, hg1⟩
  have hSb : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  set t0 := sInf S with ht0
  have ht0S : t0 ∈ S := hSc.csInf_mem hSne hSb
  have hat0 : a ≤ t0 := ht0S.1.1
  have ht0T : t0 ≤ T := ht0S.1.2
  have hgt : ∀ t ∈ Icc a T, t < t0 → 0 < g t := by
    intro t ht hlt
    by_contra hle
    rw [not_lt] at hle
    have : t0 ≤ t := csInf_le hSb ⟨ht, hle⟩
    linarith
  have hg0 : g t0 ≤ 0 := ht0S.2
  have hlt : a < t0 := by
    rcases hat0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hg0; linarith
  have hzero0 : g t0 = 0 := by
    by_contra hne
    have hneg : g t0 < 0 := lt_of_le_of_ne hg0 hne
    -- continuity within [a,t0] contradicts positivity on [a,t0)
    have hc : ContinuousWithinAt g (Icc a T) t0 := hcont t0 ⟨hat0, ht0T⟩
    have hev : ∀ᶠ t in 𝓝[Icc a T] t0, g t < 0 := hc.eventually (gt_mem_nhds hneg)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hball⟩ := hev
    set s := max a (t0 - δ / 2) with hs
    have hs1 : a ≤ s := le_max_left _ _
    have hs2 : s < t0 := by
      apply max_lt hlt; linarith
    have hsI : s ∈ Icc a T := ⟨hs1, by linarith⟩
    have : g s < 0 := hball (by
      rw [Real.dist_eq, abs_lt]
      constructor <;> [skip; skip] <;> (have : t0 - δ / 2 ≤ s := le_max_right _ _) <;> linarith) hsI
    have := hgt s hsI hs2
    linarith
  obtain ⟨g', hd, hg'⟩ := hzero t0 ⟨hat0, ht0T⟩ hzero0
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hd).eventually (lt_mem_nhds hg')
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hsl
  obtain ⟨δ, hδ, hball⟩ := hsl
  set s := max a (t0 - δ / 2) with hs
  have hs1 : a ≤ s := le_max_left _ _
  have hs2 : s < t0 := max_lt hlt (by linarith)
  have hsI : s ∈ Icc a T := ⟨hs1, by linarith⟩
  have h3 : 0 < slope g t0 s := hball (by
      rw [Real.dist_eq, abs_lt]
      have : t0 - δ / 2 ≤ s := le_max_right _ _
      constructor <;> linarith) (by simp only [mem_compl_iff, mem_singleton_iff]; exact hs2.ne)
  rw [slope_def_field, hzero0] at h3
  have := hgt s hsI hs2
  have h4 : s - t0 < 0 := by linarith
  have h5 : (g s - 0) / (s - t0) < 0 := div_neg_of_pos_of_neg (by linarith) h4
  linarith


/-- `h = parameter` is continuous on `[0,1)` (strict monotonicity of `R`, `R (h t) = t`). -/
theorem parameter_continuousOn : ContinuousOn parameter (Ico 0 1) := by
  intro t0 ht0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨hm0, hp0⟩ := parameter_mean_t ht0.1 ht0.2
  set h0 := parameter t0 with hh0
  have hlo : besselMoment 1 (h0 - ε) < t0 := by
    rw [← hm0]; exact besselMoment_first_strictMono (by linarith)
  have hhi : t0 < besselMoment 1 (h0 + ε) := by
    rw [← hm0]; exact besselMoment_first_strictMono (by linarith)
  refine ⟨min (t0 - besselMoment 1 (h0 - ε)) (besselMoment 1 (h0 + ε) - t0),
    lt_min (by linarith) (by linarith), ?_⟩
  intro x hx hdist
  rw [Real.dist_eq] at hdist
  obtain ⟨hd1, hd2⟩ := abs_lt.mp hdist
  have hm1 := min_le_left (t0 - besselMoment 1 (h0 - ε)) (besselMoment 1 (h0 + ε) - t0)
  have hm2 := min_le_right (t0 - besselMoment 1 (h0 - ε)) (besselMoment 1 (h0 + ε) - t0)
  obtain ⟨hmx, _⟩ := parameter_mean_t hx.1 hx.2
  have h1 : besselMoment 1 (h0 - ε) < besselMoment 1 (parameter x) := by rw [hmx]; linarith
  have h2 : besselMoment 1 (parameter x) < besselMoment 1 (h0 + ε) := by rw [hmx]; linarith
  have h3 := besselMoment_first_strictMono.lt_iff_lt.mp h1
  have h4 := besselMoment_first_strictMono.lt_iff_lt.mp h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- `d12-circle-eq:riccati`: `h'(t) = h/(2h(1-t²)-t)` with positive denominator. -/
theorem parameter_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < 2 * parameter t * (1 - t ^ 2) - t ∧
      HasDerivAt parameter (parameter t / (2 * parameter t * (1 - t ^ 2) - t)) t := by
  obtain ⟨hm, hp⟩ := parameter_mean_t ht0.le ht1
  set h := parameter t with hh
  have hhpos : 0 < h := by
    rcases hp.lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [← h', besselMoment_one_zero] at hm; linarith
  have hder := besselMoment_first_derivative h
  have hrec := besselMoment_recurrence h
  rw [hm] at hder hrec
  have hR : 1 + besselMoment 2 h - 2 * t ^ 2 = (2 * h * (1 - t ^ 2) - t) / h := by
    field_simp
    nlinarith
  have hRpos : 0 < 1 + besselMoment 2 h - 2 * t ^ 2 := by
    have := besselMoment_deriv_pos h
    rw [(besselMoment_first_derivative h).deriv, hm] at this
    exact this
  have hD : 0 < 2 * h * (1 - t ^ 2) - t := by
    rw [hR] at hRpos
    exact (div_pos_iff_of_pos_right hhpos).mp hRpos
  refine ⟨hD, ?_⟩
  have hcont : ContinuousAt parameter t :=
    (parameter_continuousOn t ⟨ht0.le, ht1⟩).continuousAt (Ico_mem_nhds ht0 ht1)
  have hev : ∀ᶠ y in 𝓝 t, besselMoment 1 (parameter y) = y := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with y hy
    exact (parameter_mean_t hy.1.le hy.2).1
  have hf : HasDerivAt (besselMoment 1) (1 + besselMoment 2 h - 2 * t ^ 2) (parameter t) := by
    rw [← hh]; exact hder
  have := HasDerivAt.of_local_left_inverse hcont hf hRpos.ne' hev
  convert this using 1
  rw [hR]
  field_simp


/-- **`d12-circle-lem:hminus`, first part**, along the manuscript's route (jet at the origin, then
first contact of `h - h_-` in the variable `t` using `h' = h/(2h(1-t²)-t)` and the exact residual):
`h_-(t) < h(t)` for `0 < t < 1`. -/
theorem hminus_lt_parameter_t {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : hminus t < parameter t := by
  rcases le_or_gt t (1 / 100) with hsmall | hbig
  · exact hminus_lt_parameter_near_zero ht hsmall
  · let g : ℝ → ℝ := fun s => parameter s - hminus s
    have hsub : Icc (1 / 100 : ℝ) t ⊆ Ico 0 1 := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hcont : ContinuousOn g (Icc (1 / 100 : ℝ) t) := by
      apply ContinuousOn.sub (parameter_continuousOn.mono hsub)
      intro s hs
      have hs1 : s ^ 2 ≠ 1 := by nlinarith [hs.1, hs.2]
      exact (hminus_hasDerivAt hs1).continuousAt.continuousWithinAt
    have hpos : 0 < g (1 / 100) := by
      have := hminus_lt_parameter_near_zero (t := 1 / 100) (by norm_num) le_rfl
      simp only [g]; linarith
    have hzero : ∀ s ∈ Icc (1 / 100 : ℝ) t, g s = 0 → ∃ g', HasDerivAt g g' s ∧ 0 < g' := by
      intro s hs hgs
      have hs0 : 0 < s := by linarith [hs.1]
      have hs1 : s < 1 := by linarith [hs.2]
      obtain ⟨hD, hpd⟩ := parameter_hasDerivAt hs0 hs1
      have hsq : s ^ 2 ≠ 1 := by nlinarith
      refine ⟨parameter s / (2 * parameter s * (1 - s ^ 2) - s) - hminusSlope s,
        hpd.sub (hminus_hasDerivAt hsq), ?_⟩
      have heq : parameter s = hminus s := by simp only [g] at hgs; linarith
      have hres := hminus_residual hsq
      have hneg : hminusSlope s * (2 * hminus s * (1 - s ^ 2) - s) - hminus s < 0 := by
        rw [hres]
        have h1s : 0 < 1 - s ^ 2 := by nlinarith
        apply div_neg_of_neg_of_pos _ (by positivity)
        have : 0 < s ^ 9 := by positivity
        have : 0 < 5 * s ^ 6 + 25 * s ^ 4 + 144 * s ^ 2 + 16 := by positivity
        nlinarith
      rw [heq] at hD ⊢
      rw [sub_pos, lt_div_iff₀ hD]
      linarith
    have := first_contact hcont hpos hzero t ⟨hbig.le, le_rfl⟩
    simp only [g] at this
    linarith

/-- `I'(t) = 2 h(t)` on `(0,1)` (`I = rate`). -/
theorem rate_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : HasDerivAt rate (2 * parameter t) t := by
  obtain ⟨hm, hp⟩ := parameter_mean_t ht0.le ht1
  obtain ⟨_, hpd⟩ := parameter_hasDerivAt ht0 ht1
  set h' := parameter t / (2 * parameter t * (1 - t ^ 2) - t)
  have hlog := (log_bessel_hasDerivAt (parameter t)).comp t hpd
  have h : HasDerivAt (fun s => 2 * parameter s * s - Real.log (bessel 0 (parameter s)))
      (2 * h' * t + 2 * parameter t * 1 - 2 * besselMoment 1 (parameter t) * h') t :=
    ((hpd.const_mul 2).mul (hasDerivAt_id t)).sub hlog
  refine HasDerivAt.congr_deriv (f := rate) h ?_
  rw [hm]
  ring

theorem rate_continuousOn : ContinuousOn rate (Ico 0 1) := by
  have hlogc : Continuous (fun a : ℝ => Real.log (bessel 0 a)) :=
    continuous_iff_continuousAt.mpr (fun a => (log_bessel_hasDerivAt a).continuousAt)
  have := ((parameter_continuousOn.const_smul (2 : ℝ)).mul continuousOn_id).sub
    (hlogc.comp_continuousOn parameter_continuousOn)
  refine this.congr ?_
  intro s _
  simp only [rate, Pi.sub_apply, Pi.mul_apply, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- **`d12-circle-lem:hminus`, second part**, along the manuscript's route: `I_-(t) <= I(t)` for
`0 <= t < 1`, by integrating `I' = 2h >= 2 h_- = I_-'` from `I(0) = I_-(0) = 0`. -/
theorem Iminus_le_rate_t {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : Iminus t ≤ rate t := by
  let G : ℝ → ℝ := fun s => rate s - Iminus s
  have hdiff : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt G (2 * (parameter s - hminus s)) s := by
    intro s hs
    have hsq : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
    have := (rate_hasDerivAt hs.1 hs.2).sub (Iminus_hasDerivAt hsq)
    convert this using 1; ring
  have hGc : ContinuousOn G (Ico 0 1) := by
    apply rate_continuousOn.sub
    intro s hs
    have hsq : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
    exact (Iminus_hasDerivAt hsq).continuousAt.continuousWithinAt
  have hmono : MonotoneOn G (Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1) hGc
    · rw [interior_Ico]; exact fun s hs => (hdiff s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro s hs
      rw [(hdiff s hs).deriv]
      have := hminus_lt_parameter_t hs.1 hs.2
      linarith
  have hz : bessel 0 0 = 1 := by
    rw [bessel_zero_eq, BecknerOnofri.HighDim.besselI0Two_eq_circle_integral]
    simp
  have hp0 : parameter 0 = 0 := by
    obtain ⟨hm, _⟩ := parameter_mean_t (le_refl 0) one_pos
    exact besselMoment_first_strictMono.injective (hm.trans besselMoment_one_zero.symm)
  have hG0 : G 0 = 0 := by simp [G, rate, Iminus, hp0, hz]
  have := hmono ⟨le_refl 0, one_pos⟩ ⟨ht, ht1⟩ ht
  rw [hG0] at this
  simp only [G] at this
  linarith

end BecknerOnofri.V2.Circle
