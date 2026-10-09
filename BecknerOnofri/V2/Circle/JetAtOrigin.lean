module

public import Mathlib.Tactic
public import BecknerOnofri.V2.Circle.BesselTruncation
public import BecknerOnofri.V2.Circle.InverseBessel
public import BecknerOnofri.V2.Circle.InverseExists

@[expose] public section

/-! # The jet of the inverse Bessel function at the origin (Lemma 5.15, Appendix A.2.1)

The manuscript states `h(t) = t + t^3/2 + 5t^5/12 + 19t^7/48 + 143t^9/360 + O(t^11)` for the inverse
`h = parameter` of `R = I_1(2.)/I_0(2.)`, "checked by substituting the series into `R(h) = t`", and
deduces `h - h_- = t^9/720 + O(t^11) > 0` near `0`.

* `H9_identity`: `t D_4(H_9(t)) - N_4(H_9(t)) = t^11 q(t^2)` (the coefficients `1, 1/2, 5/12, 19/48,
  143/360` are exactly those for which the first ten orders cancel);
* `qjet_abs_le`: `|q| <= 4` on `[0,1]`;
* `H9_residual`: `|R(H_9(t)) - t| <= 5 t^11` for `0 < t <= 1/50` (uses the truncation remainders of
  `BesselTruncation`);
* `parameter_jet`: `|h(t) - H_9(t)| <= 10 t^11` (uses `R' >= 1/2` on `[0,1/2]`);
* `hminus_lt_parameter_near_zero`: `h_-(t) < h(t)` for `0 < t <= 1/100`. -/
noncomputable section
open Set
open BecknerOnofri.HighDim.CircleScalar
namespace BecknerOnofri.V2.Circle

/-- The degree-nine truncation of the inverse series `h(t) = t + t³/2 + 5t⁵/12 + 19t⁷/48 + 143t⁹/360 + O(t¹¹)`. -/
def H9 (t : ℝ) : ℝ := t + t ^ 3 / 2 + 5 * t ^ 5 / 12 + 19 * t ^ 7 / 48 + 143 * t ^ 9 / 360

/-- `q(x)`, with `t D₄(H₉(t)) - N₄(H₉(t)) = t¹¹ q(t²)`: the first ten orders cancel, which verifies the
coefficients `1, 1/2, 5/12, 19/48, 143/360` by substitution into `I₁(2h)/I₀(2h) = t`. -/
def qjet (x : ℝ) : ℝ := (1415/3456:ℝ) * x ^ 0 + (3853/17280:ℝ) * x ^ 1 + (83501/414720:ℝ) * x ^ 2 + (222743/1036800:ℝ) * x ^ 3 + (25413/102400:ℝ) * x ^ 4 + (296719/995328:ℝ) * x ^ 5 + (83892289/298598400:ℝ) * x ^ 6 + (519019087/1990656000:ℝ) * x ^ 7 + (2094766297/8957952000:ℝ) * x ^ 8 + (1411017361/7166361600:ℝ) * x ^ 9 + (41888554937/286654464000:ℝ) * x ^ 10 + (958233794203/8599633920000:ℝ) * x ^ 11 + (2075822917807/25798901760000:ℝ) * x ^ 12 + (3566204789999/68797071360000:ℝ) * x ^ 13 + (32295427589071/1238347284480000:ℝ) * x ^ 14 + (19556936388673/4127824281600000:ℝ) * x ^ 15 + (-95853988696619/9906778275840000:ℝ) * x ^ 16 + (-5386567484534143/297203348275200000:ℝ) * x ^ 17 + (-38715809502085073/1783220089651200000:ℝ) * x ^ 18 + (-770763134043347389/35664401793024000000:ℝ) * x ^ 19 + (-2043248159832361549/106993205379072000000:ℝ) * x ^ 20 + (-1670509008108952223/106993205379072000000:ℝ) * x ^ 21 + (-189760081118039057/15850845241344000000:ℝ) * x ^ 22 + (-73956959766910951667/8559456430325760000000:ℝ) * x ^ 23 + (-3612372273734461827611/616280862983454720000000:ℝ) * x ^ 24 + (-4590600998940919809221/1232561725966909440000000:ℝ) * x ^ 25 + (-1309222875842605000153/591629628464116531200000:ℝ) * x ^ 26 + (-45177872568144162543983/36976851779007283200000000:ℝ) * x ^ 27 + (-957072969747747951527/1540702157458636800000000:ℝ) * x ^ 28 + (-1997013617561356071821/6933159708563865600000000:ℝ) * x ^ 29 + (-837848856526129823089/6933159708563865600000000:ℝ) * x ^ 30 + (-2341479194807933000821/51998697814228992000000000:ℝ) * x ^ 31 + (-20956048175557084733/1444408272617472000000000:ℝ) * x ^ 32 + (-1674000989581532183/433322481785241600000000:ℝ) * x ^ 33 + (-3322323366466780819/4333224817852416000000000:ℝ) * x ^ 34 + (-25004854810776297743/292492675205038080000000000:ℝ) * x ^ 35

theorem H9_identity (t : ℝ) : t * Dtr (H9 t) - Ntr (H9 t) = t ^ 11 * qjet (t ^ 2) := by
  simp only [Dtr, Ntr, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  unfold H9 qjet
  ring

theorem term_pos (c : ℝ) (i : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hc : 0 ≤ c) :
    0 ≤ c * x ^ i ∧ c * x ^ i ≤ c := by
  refine ⟨by positivity, ?_⟩
  have : x ^ i ≤ 1 := pow_le_one₀ hx0 hx1
  nlinarith

theorem term_neg (c : ℝ) (i : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hc : c ≤ 0) :
    c ≤ c * x ^ i ∧ c * x ^ i ≤ 0 := by
  have h0 : 0 ≤ x ^ i := by positivity
  have : x ^ i ≤ 1 := pow_le_one₀ hx0 hx1
  constructor <;> nlinarith

theorem qjet_abs_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : |qjet x| ≤ 4 := by
  unfold qjet
  have a0 := term_pos ((1415/3456:ℝ)) 0 hx0 hx1 (by norm_num)
  have a1 := term_pos ((3853/17280:ℝ)) 1 hx0 hx1 (by norm_num)
  have a2 := term_pos ((83501/414720:ℝ)) 2 hx0 hx1 (by norm_num)
  have a3 := term_pos ((222743/1036800:ℝ)) 3 hx0 hx1 (by norm_num)
  have a4 := term_pos ((25413/102400:ℝ)) 4 hx0 hx1 (by norm_num)
  have a5 := term_pos ((296719/995328:ℝ)) 5 hx0 hx1 (by norm_num)
  have a6 := term_pos ((83892289/298598400:ℝ)) 6 hx0 hx1 (by norm_num)
  have a7 := term_pos ((519019087/1990656000:ℝ)) 7 hx0 hx1 (by norm_num)
  have a8 := term_pos ((2094766297/8957952000:ℝ)) 8 hx0 hx1 (by norm_num)
  have a9 := term_pos ((1411017361/7166361600:ℝ)) 9 hx0 hx1 (by norm_num)
  have a10 := term_pos ((41888554937/286654464000:ℝ)) 10 hx0 hx1 (by norm_num)
  have a11 := term_pos ((958233794203/8599633920000:ℝ)) 11 hx0 hx1 (by norm_num)
  have a12 := term_pos ((2075822917807/25798901760000:ℝ)) 12 hx0 hx1 (by norm_num)
  have a13 := term_pos ((3566204789999/68797071360000:ℝ)) 13 hx0 hx1 (by norm_num)
  have a14 := term_pos ((32295427589071/1238347284480000:ℝ)) 14 hx0 hx1 (by norm_num)
  have a15 := term_pos ((19556936388673/4127824281600000:ℝ)) 15 hx0 hx1 (by norm_num)
  have a16 := term_neg ((-95853988696619/9906778275840000:ℝ)) 16 hx0 hx1 (by norm_num)
  have a17 := term_neg ((-5386567484534143/297203348275200000:ℝ)) 17 hx0 hx1 (by norm_num)
  have a18 := term_neg ((-38715809502085073/1783220089651200000:ℝ)) 18 hx0 hx1 (by norm_num)
  have a19 := term_neg ((-770763134043347389/35664401793024000000:ℝ)) 19 hx0 hx1 (by norm_num)
  have a20 := term_neg ((-2043248159832361549/106993205379072000000:ℝ)) 20 hx0 hx1 (by norm_num)
  have a21 := term_neg ((-1670509008108952223/106993205379072000000:ℝ)) 21 hx0 hx1 (by norm_num)
  have a22 := term_neg ((-189760081118039057/15850845241344000000:ℝ)) 22 hx0 hx1 (by norm_num)
  have a23 := term_neg ((-73956959766910951667/8559456430325760000000:ℝ)) 23 hx0 hx1 (by norm_num)
  have a24 := term_neg ((-3612372273734461827611/616280862983454720000000:ℝ)) 24 hx0 hx1 (by norm_num)
  have a25 := term_neg ((-4590600998940919809221/1232561725966909440000000:ℝ)) 25 hx0 hx1 (by norm_num)
  have a26 := term_neg ((-1309222875842605000153/591629628464116531200000:ℝ)) 26 hx0 hx1 (by norm_num)
  have a27 := term_neg ((-45177872568144162543983/36976851779007283200000000:ℝ)) 27 hx0 hx1 (by norm_num)
  have a28 := term_neg ((-957072969747747951527/1540702157458636800000000:ℝ)) 28 hx0 hx1 (by norm_num)
  have a29 := term_neg ((-1997013617561356071821/6933159708563865600000000:ℝ)) 29 hx0 hx1 (by norm_num)
  have a30 := term_neg ((-837848856526129823089/6933159708563865600000000:ℝ)) 30 hx0 hx1 (by norm_num)
  have a31 := term_neg ((-2341479194807933000821/51998697814228992000000000:ℝ)) 31 hx0 hx1 (by norm_num)
  have a32 := term_neg ((-20956048175557084733/1444408272617472000000000:ℝ)) 32 hx0 hx1 (by norm_num)
  have a33 := term_neg ((-1674000989581532183/433322481785241600000000:ℝ)) 33 hx0 hx1 (by norm_num)
  have a34 := term_neg ((-3322323366466780819/4333224817852416000000000:ℝ)) 34 hx0 hx1 (by norm_num)
  have a35 := term_neg ((-25004854810776297743/292492675205038080000000000:ℝ)) 35 hx0 hx1 (by norm_num)
  rw [abs_le]
  constructor <;> linarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, a6.1, a6.2, a7.1, a7.2, a8.1, a8.2, a9.1, a9.2, a10.1, a10.2, a11.1, a11.2, a12.1, a12.2, a13.1, a13.2, a14.1, a14.2, a15.1, a15.2, a16.1, a16.2, a17.1, a17.2, a18.1, a18.2, a19.1, a19.2, a20.1, a20.2, a21.1, a21.2, a22.1, a22.2, a23.1, a23.2, a24.1, a24.2, a25.1, a25.2, a26.1, a26.2, a27.1, a27.2, a28.1, a28.2, a29.1, a29.2, a30.1, a30.2, a31.1, a31.2, a32.1, a32.2, a33.1, a33.2, a34.1, a34.2, a35.1, a35.2]


theorem H9_bounds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 50) : t ≤ H9 t ∧ H9 t ≤ 2 * t := by
  unfold H9
  have h2 : t ^ 2 ≤ 1 / 2500 := by nlinarith
  have h3 : t ^ 3 = t * t ^ 2 := by ring
  have h5 : t ^ 5 = t * (t ^ 2) ^ 2 := by ring
  have h7 : t ^ 7 = t * (t ^ 2) ^ 3 := by ring
  have h9 : t ^ 9 = t * (t ^ 2) ^ 4 := by ring
  have x0 : 0 ≤ t ^ 2 := sq_nonneg t
  have x1 : (t ^ 2) ^ 2 ≤ 1 / 2500 := by nlinarith
  have x2 : (t ^ 2) ^ 3 ≤ 1 / 2500 := by nlinarith [pow_nonneg x0 3, pow_nonneg x0 2]
  have x3 : (t ^ 2) ^ 4 ≤ 1 / 2500 := by nlinarith [pow_nonneg x0 3, pow_nonneg x0 4]
  constructor
  · have : 0 ≤ t ^ 3 / 2 + 5 * t ^ 5 / 12 + 19 * t ^ 7 / 48 + 143 * t ^ 9 / 360 := by positivity
    linarith
  · rw [h3, h5, h7, h9]; nlinarith [mul_nonneg ht.le x0]

/-- The finite jet with an actual remainder estimate: `|R(H₉(t)) - t| ≤ 5 t¹¹` for `0 < t ≤ 1/50`. -/
theorem H9_residual {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 50) : |besselMoment 1 (H9 t) - t| ≤ 5 * t ^ 11 := by
  obtain ⟨hlow, hup⟩ := H9_bounds ht ht1
  set h := H9 t with hh
  have hpos : 0 < h := by linarith
  have hlt1 : h < 1 := by linarith
  have hx0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hx1 : t ^ 2 ≤ 1 := by nlinarith
  have hq := qjet_abs_le hx0 hx1
  have hid := H9_identity t
  have hD := Dtr_le_bessel hpos.le hlt1
  have hD' := bessel_zero_le hpos.le hlt1
  have hN := bessel_one_le hpos.le hlt1
  have hN0 : Ntr h ≤ bessel 1 h := by
    have := (bterm_summable 1 hpos.le hlt1).sum_add_tsum_nat_add 5
    rw [bessel_eq_tsum, ← this]
    have h2 : 0 ≤ ∑' i, bterm 1 h (i + 5) := tsum_nonneg (fun i => bterm_nonneg 1 hpos.le _)
    have : Ntr h = ∑ i ∈ Finset.range 5, bterm 1 h i := by simp only [Ntr, bterm]
    linarith
  have hb0 := bessel_zero_pos hpos.le hlt1
  have hhq : h ^ 2 ≤ 1 / 2 := by nlinarith
  have hden : 1 / 2 ≤ 1 - h ^ 2 := by linarith
  have hh2 : h ^ 11 ≤ (2 * t) ^ 11 := pow_le_pow_left₀ hpos.le hup 11
  have hh10 : h ^ 10 ≤ (2 * t) ^ 10 := pow_le_pow_left₀ hpos.le hup 10
  have T1 : h ^ 11 / (86400 * (1 - h ^ 2)) ≤ t ^ 11 / 10 := by
    rw [div_le_iff₀ (by nlinarith)]
    have : (2 * t) ^ 11 = 2048 * t ^ 11 := by ring
    have t11 : 0 ≤ t ^ 11 := by positivity
    nlinarith
  have T0 : h ^ 10 / (14400 * (1 - h ^ 2)) ≤ t ^ 10 / 5 := by
    rw [div_le_iff₀ (by nlinarith)]
    have : (2 * t) ^ 10 = 1024 * t ^ 10 := by ring
    have t10 : 0 ≤ t ^ 10 := by positivity
    nlinarith
  have hqq : |t ^ 11 * qjet (t ^ 2)| ≤ 4 * t ^ 11 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    nlinarith [pow_nonneg ht.le 11]
  have hqq' := abs_le.mp hqq
  -- t * bessel0 - bessel1
  have hlow2 : -(5 * t ^ 11) ≤ t * bessel 0 h - bessel 1 h := by
    have : t * Dtr h ≤ t * bessel 0 h := mul_le_mul_of_nonneg_left hD ht.le
    nlinarith [pow_nonneg ht.le 11]
  have hup2 : t * bessel 0 h - bessel 1 h ≤ 5 * t ^ 11 := by
    have h1 : t * bessel 0 h ≤ t * (Dtr h + h ^ 10 / (14400 * (1 - h ^ 2))) :=
      mul_le_mul_of_nonneg_left hD' ht.le
    have h2 : t * (h ^ 10 / (14400 * (1 - h ^ 2))) ≤ t * (t ^ 10 / 5) := mul_le_mul_of_nonneg_left T0 ht.le
    nlinarith [pow_nonneg ht.le 11]
  unfold besselMoment
  rw [div_sub' (by linarith)]
  rw [abs_div, abs_of_pos (by linarith : 0 < bessel 0 h), div_le_iff₀ (by linarith)]
  rw [abs_le]
  constructor <;> nlinarith [pow_nonneg ht.le 11]


theorem besselMoment_one_le_self {a : ℝ} (ha : 0 ≤ a) : besselMoment 1 a ≤ a := by
  have h := besselMoment_first_le_supersolution a ha
  have hs : 1 ≤ Real.sqrt (1 + a ^ 2) := by
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + a ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have : a / Real.sqrt (1 + a ^ 2) ≤ a := div_le_self ha hs
  linarith

theorem besselMoment_deriv_ge_half {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    1 / 2 ≤ 1 + besselMoment 2 a - 2 * (besselMoment 1 a) ^ 2 := by
  have h1 := besselMoment_one_le_self ha
  have h0 := besselMoment_nonneg 1 ha
  have h2 := besselMoment_nonneg 2 ha
  nlinarith

/-- `R(b) - R(a) ≥ (b - a)/2` for `0 ≤ a ≤ b ≤ 1/2`. -/
theorem besselMoment_sub_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    (b - a) / 2 ≤ besselMoment 1 b - besselMoment 1 a := by
  have hmono : MonotoneOn (fun x => besselMoment 1 x - x / 2) (Icc 0 (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
    · intro x _
      exact ((besselMoment_first_derivative x).continuousAt.sub (continuousAt_id.div_const 2)).continuousWithinAt
    · intro x _
      exact ((besselMoment_first_derivative x).differentiableAt.sub
        ((differentiableAt_id).div_const 2)).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hd : HasDerivAt (fun x => besselMoment 1 x - x / 2)
          (1 + besselMoment 2 x - 2 * besselMoment 1 x ^ 2 - 1 / 2) x :=
        ((besselMoment_first_derivative x).sub ((hasDerivAt_id x).div_const 2)).congr_deriv (by simp)
      rw [hd.deriv]
      have := besselMoment_deriv_ge_half hx.1.le (by linarith [hx.2])
      linarith
  have := hmono ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab
  simp only at this
  linarith

/-- The finite jet of the inverse: `|h(t) - H₉(t)| ≤ 10 t¹¹` for `0 < t ≤ 1/50`, with
`h = parameter`, the inverse of `R = I₁(2·)/I₀(2·)`. -/
theorem parameter_jet {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 50) : |parameter t - H9 t| ≤ 10 * t ^ 11 := by
  obtain ⟨hlow, hup⟩ := H9_bounds ht ht1
  obtain ⟨hm, hp⟩ := parameter_mean_t ht.le (by linarith)
  set p := parameter t with hpdef
  have hp12 : p ≤ 1 / 2 := by
    by_contra hcon
    replace hcon : 1 / 2 < p := not_le.mp hcon
    have h1 : besselMoment 1 (1 / 2) < besselMoment 1 p := besselMoment_first_strictMono hcon
    have h2 := besselMoment_sub_ge (le_refl 0) (by norm_num : (0:ℝ) ≤ 1 / 2) (le_refl _)
    rw [besselMoment_one_zero] at h2
    linarith
  have hres0 := H9_residual ht ht1
  have hres : |besselMoment 1 (H9 t) - besselMoment 1 p| ≤ 5 * t ^ 11 := by rw [hm]; exact hres0
  have hH : H9 t ≤ 1 / 2 := by linarith
  rcases le_total p (H9 t) with hle | hle
  · have := besselMoment_sub_ge hp hle hH
    rw [abs_le] at hres ⊢
    constructor <;> linarith [hres.1, hres.2, pow_nonneg ht.le 11]
  · have := besselMoment_sub_ge (by linarith) hle hp12
    rw [abs_le] at hres ⊢
    constructor <;> linarith [hres.1, hres.2]

/-- `h_-(t) = H₉(t) - (t⁹/720 - 143 t¹¹/360)/(1 - t²)`: the difference of `H₉` and `h_-` is exactly
`t⁹/720 + O(t¹¹)`. -/
theorem H9_sub_hminus {t : ℝ} (ht : t ^ 2 ≠ 1) :
    H9 t - hminus t = (t ^ 9 / 720 - 143 * t ^ 11 / 360) / (1 - t ^ 2) := by
  have hd : (1 - t ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  unfold H9 hminus hmPoly
  field_simp
  ring

/-- The positive initial interval for the first contact argument: `h(t) > h_-(t)` for `0 < t ≤ 1/100`. -/
theorem hminus_lt_parameter_near_zero {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100) :
    hminus t < parameter t := by
  have ht50 : t ≤ 1 / 50 := by linarith
  have hj := parameter_jet ht ht50
  have hx : t ^ 2 ≤ 1 / 10000 := by nlinarith
  have ht2 : t ^ 2 ≠ 1 := by intro h; nlinarith
  have hd := H9_sub_hminus ht2
  have hw : 0 < 1 - t ^ 2 := by nlinarith
  have hnum : 0 < t ^ 9 / 720 - 143 * t ^ 11 / 360 := by
    have : t ^ 11 = t ^ 9 * t ^ 2 := by ring
    have t9 : 0 < t ^ 9 := by positivity
    rw [this]; nlinarith
  have hge : t ^ 9 / 720 - 143 * t ^ 11 / 360 ≤ (t ^ 9 / 720 - 143 * t ^ 11 / 360) / (1 - t ^ 2) := by
    rw [le_div_iff₀ hw]; nlinarith [sq_nonneg t]
  rw [abs_le] at hj
  have : 10 * t ^ 11 < t ^ 9 / 720 - 143 * t ^ 11 / 360 := by
    have e : t ^ 11 = t ^ 9 * t ^ 2 := by ring
    have t9 : 0 < t ^ 9 := by positivity
    rw [e]; nlinarith
  linarith [hj.1, hj.2]

end BecknerOnofri.V2.Circle
