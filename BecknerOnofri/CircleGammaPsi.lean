module

public import BecknerOnofri.CircleGammaPsiCertificate
public import BecknerOnofri.CircleGammaMinimum

@[expose] public section

/-! Step 4 of the proof of Lemma 5.17 (`lem:section5-global-small-gamma`) and
the lemma itself: `γ(t) ≥ ψ(t) = (3/40)t⁴ + (33/200)t¹⁰` for `0 ≤ t < 1`.

The constrained minimum in `γ` is bounded below by the unconstrained one,
after lowering `c w₁, c w₂` to `B, C` (Step 2) and, for `t ≥ 3/4`, the moment
combination `L = 6m₂ - m₃` to its value `L_*` at the barrier (Step 1). The
three resulting rational functions are handled by the certificates of
`CircleGammaPsiCertificate`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.CircleScalar
open GammaPoly Spin

theorem bessel_recurrence_two_term (h : ℝ) (j : ℕ) :
    h * besselOrderTerm h 1 (j+1) = h * besselOrderTerm h 3 j + 2 * besselOrderTerm h 2 (j+1) := by
  simp only [besselOrderTerm]
  rw [show j + 1 + 1 = j + 2 by omega, show j + 1 + 2 = j + 3 by omega,
    show j + 3 = (j + 2) + 1 by omega, show j + 2 = (j + 1) + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_add, pow_one]
  field_simp
  ring

/-- The Bessel recurrence `h I₁ = h I₃ + 2 I₂` (argument `2h`). -/
theorem bessel_recurrence_two (h : ℝ) : h * bessel 1 h = h * bessel 3 h + 2 * bessel 2 h := by
  have h1 := (besselOrderTerm_summable h 1).sum_add_tsum_nat_add 1
  have h2 := (besselOrderTerm_summable h 2).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at h1 h2
  have ho : besselOrderTerm h 1 0 = h := by norm_num [besselOrderTerm]
  have ht : besselOrderTerm h 2 0 = h^2/2 := by norm_num [besselOrderTerm, Nat.factorial]
  rw [ho] at h1
  rw [ht] at h2
  have he : h * (∑' j : ℕ, besselOrderTerm h 1 (j+1)) =
      h * (∑' j : ℕ, besselOrderTerm h 3 j) + 2 * (∑' j : ℕ, besselOrderTerm h 2 (j+1)) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add
      ((besselOrderTerm_summable h 3).mul_left h)
      (((summable_nat_add_iff 1).mpr (besselOrderTerm_summable h 2)).mul_left 2)]
    exact tsum_congr (bessel_recurrence_two_term h)
  simp only [bessel_series_eq]
  rw [← h1, ← h2, mul_add, he]
  ring

/-- The moment combination `L = 6m₂ - m₃` in terms of `h` and `t = m₁`. -/
theorem moment_combination_eq {h : ℝ} (hh : 0 < h) :
    6 * besselMoment 2 h - besselMoment 3 h =
      6 - besselMoment 1 h + (2 - 6 * besselMoment 1 h) / h - 2 * besselMoment 1 h / h^2 := by
  have hp : bessel 0 h ≠ 0 := by rw [bessel_zero_eq]; exact (besselI0Two_pos h).ne'
  have h1 := besselMoment_recurrence h
  have h2 : h * besselMoment 1 h = h * besselMoment 3 h + 2 * besselMoment 2 h := by
    have := bessel_recurrence_two h
    unfold besselMoment
    field_simp
    linarith
  have hm2 : besselMoment 2 h = 1 - besselMoment 1 h / h := by
    field_simp; linarith
  have hm3 : besselMoment 3 h = besselMoment 1 h - 2 * besselMoment 2 h / h := by
    field_simp; linarith
  rw [hm3, hm2]
  field_simp
  ring

/-- `L` as a function of `h` at fixed `t`. -/
def momentCombination (t h : ℝ) : ℝ := 6 - t + (2 - 6*t)/h - 2*t/h^2

theorem momentCombination_mono {t H h : ℝ} (ht : 1/3 ≤ t) (hH : 0 < H) (hHh : H ≤ h) :
    momentCombination t H ≤ momentCombination t h := by
  have hh : 0 < h := hH.trans_le hHh
  set u := 1/h with hu
  set v := 1/H with hv
  have huv : u ≤ v := one_div_le_one_div_of_le hH hHh
  have hu0 : 0 < u := by positivity
  have hv0 : 0 < v := by positivity
  have e1 : momentCombination t h = 6 - t + (2 - 6*t)*u - 2*t*u^2 := by
    simp only [momentCombination, hu]; field_simp
  have e2 : momentCombination t H = 6 - t + (2 - 6*t)*v - 2*t*v^2 := by
    simp only [momentCombination, hv]; field_simp
  rw [e1, e2]
  nlinarith [mul_nonneg (sub_nonneg.mpr huv)
    (show 0 ≤ 6*t - 2 + 2*t*(u+v) by nlinarith)]

/-- The unconstrained minimum of `A a² + B(a-x)² + C(L-Da)₊²`
(`eq:simple-positive-square`), as a lower bound. -/
theorem quadratic_lower (A B C D L x a : ℝ) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 < D) :
    A*B/(A+B)*x^2 + C*(A+B)/(A+B+C*D^2) * (max 0 (L - D*B*x/(A+B)))^2 ≤
      A*a^2 + B*(a-x)^2 + C*(max 0 (L - D*a))^2 := by
  set K := A + B with hK
  have hK0 : 0 < K := by linarith
  have hKC : 0 < K + C*D^2 := by positivity
  set u := B*x/K with hu
  have e1 : A*a^2 + B*(a-x)^2 = K*(a-u)^2 + A*B/K*x^2 := by
    simp only [hu, hK]; field_simp; ring
  have e2 : D*B*x/K = D*u := by simp only [hu]; ring
  rw [e1, e2]
  suffices hs : C*K/(K+C*D^2) * (max 0 (L - D*u))^2 ≤ K*(a-u)^2 + C*(max 0 (L - D*a))^2 by
    linarith
  rcases le_total (L - D*u) 0 with hv | hv
  · rw [max_eq_left hv]
    have : 0 ≤ C*(max 0 (L - D*a))^2 := by positivity
    nlinarith [sq_nonneg (a-u)]
  · rw [max_eq_right hv]
    set v := L - D*u
    rw [div_mul_eq_mul_div, div_le_iff₀ hKC]
    rcases le_total (L - D*a) 0 with hw | hw
    · rw [max_eq_left hw]
      have hs : v ≤ D*(a-u) := by simp only [v]; nlinarith
      have hs2 : v^2 ≤ D^2*(a-u)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ C*K),
        sq_nonneg (a-u), mul_nonneg hK0.le (sq_nonneg (a-u))]
    · rw [max_eq_right hw]
      have hw' : L - D*a = v - D*(a-u) := by simp only [v]; ring
      rw [hw']
      nlinarith [sq_nonneg ((K + C*D^2)*(a-u) - C*D*v)]

/-- Lowering the weights and `L` and dropping the constraint `a ≥ m₂`. -/
theorem gamma_lower_of_bounds {t : ℝ} (ht1 : t < 1) (B C L : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ (67/100) * weight 1 t) (hC0 : 0 ≤ C)
    (hC : C ≤ (67/100) * weight 2 t)
    (hL : L ≤ 6 * besselMoment 2 (parameter t) - besselMoment 3 (parameter t)) :
    (33/100) * rate t + (67/100) * t^2 - 2 * binaryCost t +
      ((157/500)*B/(157/500+B)*(t^2)^2 +
        C*(157/500+B)/(157/500+B+C*(6-t)^2) * (max 0 (L - (6-t)*B*t^2/(157/500+B)))^2) ≤
      gamma t := by
  obtain ⟨a, -, he⟩ := candidateMinimum_attained (157/500) ((67/100)*weight 1 t)
    ((67/100)*weight 2 t) (6-t) (6*besselMoment 2 (parameter t)-besselMoment 3 (parameter t))
    (t^2) (besselMoment 2 (parameter t))
  have hq := quadratic_lower (157/500) B C (6-t) L (t^2) a (by norm_num) hB0 hC0 (by linarith)
  have hm : max 0 (L - (6-t)*a) ≤
      max 0 (6*besselMoment 2 (parameter t)-besselMoment 3 (parameter t) - (6-t)*a) :=
    max_le_max le_rfl (by linarith)
  have hm2 := pow_le_pow_left₀ (le_max_left _ _) hm 2
  have h1 : B*(a-t^2)^2 ≤ (67/100)*weight 1 t*(a-t^2)^2 :=
    mul_le_mul_of_nonneg_right hB (sq_nonneg _)
  have h2 : C*(max 0 (L - (6-t)*a))^2 ≤ (67/100)*weight 2 t*
      (max 0 (6*besselMoment 2 (parameter t)-besselMoment 3 (parameter t) - (6-t)*a))^2 :=
    mul_le_mul hC hm2 (by positivity) (by linarith)
  unfold gamma
  rw [← he]
  unfold cost
  linarith

theorem barrier_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : 0 < barrier t := by
  have hx1 : t^2 ≤ 1 := by nlinarith
  have hp := barrierPoly_pos (sq_nonneg t) hx1
  have hd : 0 < 1 - t^2 := by nlinarith
  unfold barrier
  positivity

/-- Lemma 5.17 for `0 ≤ t ≤ 3/4`: the last square is discarded. -/
theorem psi_le_gamma_small {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 3/4) :
    (3/40 : ℝ) * t^4 + (33/200) * t^10 ≤ gamma t := by
  have ht1' : t < 1 := by linarith
  have hx0 : 0 ≤ t^2 := sq_nonneg t
  have hx1 : t^2 ≤ 1 := by nlinarith
  have hx9 : t^2 ≤ 9/16 := by nlinarith
  have hg := gamma_lower_of_bounds ht1' (weightBoundOne (t^2)) 0
    (6 * besselMoment 2 (parameter t) - besselMoment 3 (parameter t))
    (weightBoundOne_nonneg hx0 hx1) (weightBoundOne_le ht ht1') le_rfl
    (by have := weight_initial_lower 2 ht ht1'; positivity) le_rfl
  have hI := rateLower_le_rate ht ht1'
  have hE := entropyBound_le ht ht1'
  have hn := smallNum_pos hx0 hx9
  have hdE := entropyDen_pos hx0 hx1
  have hdAB := minDen_pos hx0 hx1
  have hnB := weightNumOne_pos hx0 hx1
  have hdB := weightDenOne_pos hx0 hx1
  have key : t^4 * entropyBound (t^2) + (157/500)*weightBoundOne (t^2)/
      (157/500 + weightBoundOne (t^2))*(t^2)^2 =
      t^4 * (eval smallNum (t^2) / (1441440000 * eval entropyDen (t^2) * eval minDen (t^2))) := by
    simp only [entropyBound, weightBoundOne, smallNum, minDen, eval_add, eval_smul, eval_mul]
    field_simp
    push_cast
    ring
  have hpos : 0 ≤ t^4 * (eval smallNum (t^2) /
      (1441440000 * eval entropyDen (t^2) * eval minDen (t^2))) := by positivity
  simp only [zero_mul, zero_div, add_zero] at hg
  linarith

/-- Lemma 5.17 for `3/4 ≤ t < 1`, using `L ≥ L_*`. -/
theorem psi_le_gamma_large {t : ℝ} (ht : 3/4 ≤ t) (ht1 : t < 1) :
    (3/40 : ℝ) * t^4 + (33/200) * t^10 ≤ gamma t := by
  have ht0 : 0 ≤ t := by linarith
  have htp : 0 < t := by linarith
  have hx0 : 0 ≤ t^2 := sq_nonneg t
  have hx1 : t^2 ≤ 1 := by nlinarith
  have hden : 0 < 1 - t^2 := by nlinarith
  obtain ⟨hmean, hp0⟩ := parameter_mean ht0 ht1
  have hHb := barrier_le_parameter ht0 ht1
  have hHpos := barrier_pos htp ht1
  have hL : momentCombination t (barrier t) ≤
      6 * besselMoment 2 (parameter t) - besselMoment 3 (parameter t) := by
    rw [moment_combination_eq (hHpos.trans_le hHb), hmean]
    exact momentCombination_mono (by linarith) hHpos hHb
  have hg := gamma_lower_of_bounds ht1 (weightBoundOne (t^2)) (weightBoundTwo (t^2))
    (momentCombination t (barrier t))
    (weightBoundOne_nonneg hx0 hx1) (weightBoundOne_le ht0 ht1)
    (weightBoundTwo_nonneg hx0 hx1) (weightBoundTwo_le ht0 ht1) hL
  have hI := rateLower_le_rate ht0 ht1
  have hE := entropyBound_le ht0 ht1
  have hn := largeNum_pos ht ht1.le
  have hz := zNumReduced_pos ht ht1.le
  have hk := kDen_pos ht ht1.le
  have hdE := entropyDen_pos hx0 hx1
  have hdAB := minDen_pos hx0 hx1
  have hnB := weightNumOne_pos hx0 hx1
  have hdB := weightDenOne_pos hx0 hx1
  have hnC := weightNumTwo_pos hx0 hx1
  have hdC := weightDenTwo_pos hx0 hx1
  have hP := barrierPoly_pos hx0 hx1
  have hzNum := zNum_eq t
  simp only [zNum, lowerNum, barrierT, sideD, minDen, eval_sub, eval_add, eval_smul, eval_mul,
    eval_subsq, eval_cons, eval_nil, ← barrierPoly_eq] at hzNum
  push_cast at hzNum
  set p := barrierPoly (t^2) with hpdef
  set nB := eval weightNumOne (t^2)
  set dB := eval weightDenOne (t^2)
  set nC := eval weightNumTwo (t^2)
  set dC := eval weightDenTwo (t^2)
  set nE := eval entropyNum (t^2)
  set dE := eval entropyDen (t^2)
  set nz := eval zNumReduced t
  have hdABe : eval minDen (t^2) = 3*(157/500)*dB + (67/100)*nB := by
    simp only [minDen, eval_add, eval_smul, dB, nB]; push_cast; ring
  rw [hdABe] at hdAB
  have hnz : nz = (((6 - t)*t*p^2 + (2 - 6*t)*(1 - t^2)*p - 2*(1 - t^2)^2) *
      (3*(157/500)*dB + (67/100)*nB) - (67/100)*(6 - t)*nB*t^3*p^2) / t^3 := by
    rw [eq_div_iff (by positivity)]
    linear_combination -hzNum
  have hdB0 : dB ≠ 0 := hdB.ne'
  have hdC0 : dC ≠ 0 := hdC.ne'
  have hdE0 : dE ≠ 0 := hdE.ne'
  have hdAB0 : 3*(157/500)*dB + (67/100)*nB ≠ 0 := hdAB.ne'
  have hp0' : p ≠ 0 := hP.ne'
  have ht0' : t ≠ 0 := htp.ne'
  have hden0 : 1 - t^2 ≠ 0 := hden.ne'
  have hBf : weightBoundOne (t^2) = (67/100)*nB/(3*dB) := rfl
  have hCf : weightBoundTwo (t^2) = 5*(67/100)*nC/(12*dC) := rfl
  have hEf : entropyBound (t^2) = -nE/(1441440000*dE) := rfl
  have hA1 : 157/500 + weightBoundOne (t^2) = (3*(157/500)*dB + (67/100)*nB)/(3*dB) := by
    rw [hBf]; field_simp
  have hk0 : 12*(3*(157/500)*dB + (67/100)*nB)*dC + 15*(67/100)*nC*(6-t)^2*dB ≠ 0 := by
    positivity
  have hA2 : 157/500 + weightBoundOne (t^2) + weightBoundTwo (t^2)*(6-t)^2 =
      (12*(3*(157/500)*dB + (67/100)*nB)*dC + 15*(67/100)*nC*(6-t)^2*dB)/(36*dB*dC) := by
    rw [hA1, hCf]; field_simp; ring
  have hHe : barrier t = t*p/(1 - t^2) := rfl
  -- the argument of the positive part
  have hQ : momentCombination t (barrier t) - (6-t)*weightBoundOne (t^2)*t^2/
      (157/500 + weightBoundOne (t^2)) = t^2 * nz / (p^2 * (3*(157/500)*dB + (67/100)*nB)) := by
    rw [hA1, hBf, hnz, hHe]
    simp only [momentCombination]
    field_simp
  have hQpos : 0 ≤ t^2 * nz / (p^2 * (3*(157/500)*dB + (67/100)*nB)) := by positivity
  rw [hQ, max_eq_right hQpos] at hg
  have hlarge := largeNum_pos ht ht1.le
  have hlargeE : eval largeNum t = eval smallNum (t^2) * eval kDen t * p^4 +
      5*(67/100)*1441440000 * dE * nC * nz^2 := by
    simp only [largeNum, barrierT, eval_add, eval_mul, eval_smul, eval_subsq, eval_npow,
      ← barrierPoly_eq]
    push_cast; ring
  have hkE : eval kDen t = 12*(3*(157/500)*dB + (67/100)*nB)*dC +
      15*(67/100)*nC*(6-t)^2*dB := by
    simp only [kDen, sideD, minDen, eval_add, eval_mul, eval_smul, eval_subsq, eval_cons,
      eval_nil]
    push_cast; ring
  have hsE : eval smallNum (t^2) = -nE*(3*(157/500)*dB + (67/100)*nB) +
      1441440000*(157/500)*(67/100)*dE*nB := by
    simp only [smallNum, minDen, eval_add, eval_mul, eval_smul]
    push_cast; ring
  rw [hkE] at hk hlargeE
  rw [hsE] at hlargeE
  have key : t^4 * entropyBound (t^2) + ((157/500)*weightBoundOne (t^2)/
      (157/500 + weightBoundOne (t^2))*(t^2)^2 +
      weightBoundTwo (t^2)*(157/500 + weightBoundOne (t^2))/
        (157/500 + weightBoundOne (t^2) + weightBoundTwo (t^2)*(6-t)^2) *
        (t^2 * nz / (p^2 * (3*(157/500)*dB + (67/100)*nB)))^2) =
      t^4 * (eval largeNum t / (1441440000 * dE * (3*(157/500)*dB + (67/100)*nB) *
        (12*(3*(157/500)*dB + (67/100)*nB)*dC + 15*(67/100)*nC*(6-t)^2*dB) * p^4)) := by
    rw [hlargeE, hA2, hA1, hEf, hBf, hCf]
    field_simp
    ring
  have hpos : 0 ≤ t^4 * (eval largeNum t / (1441440000 * dE * (3*(157/500)*dB + (67/100)*nB) *
      (12*(3*(157/500)*dB + (67/100)*nB)*dC + 15*(67/100)*nC*(6-t)^2*dB) * p^4)) := by
    positivity
  linarith

/-- **Lemma 5.17** (`lem:section5-global-small-gamma`): for `0 ≤ t < 1`,
`γ(t) ≥ ψ(t) = (3/40)t⁴ + (33/200)t¹⁰`. -/
theorem psi_le_gamma (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (3/40 : ℝ) * t^4 + (33/200) * t^10 ≤ gamma t := by
  rcases le_total t (3/4) with h | h
  · exact psi_le_gamma_small ht0 h
  · exact psi_le_gamma_large h ht1

end BecknerOnofri.HighDim.CircleScalar
