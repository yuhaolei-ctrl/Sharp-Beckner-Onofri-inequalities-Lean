module

public import Legacy.BecknerOnofri.ThetaIntegralBound
public import BecknerOnofri.LowScalarDefinitions

@[expose] public section

/-! # Row S022 (`lem:theta-integral-certificate`): the replacement proof, claim by claim

Replacement text: `ManuscriptPatch/manuscript_v2_proposed.tex` lines 2081-2145 (marker `% REAUDIT S022`);
original text `beckner_v2_proof_route_decisions_20261010T105832Z.md`, section 3.5.

The Lean route (`Legacy.BecknerOnofri.ThetaIntegralBound`, `ThetaPolynomialCertificate`,
`ThetaExponentialIntegral`, `LaplaceReciprocal`) is the route of the replacement text.  This file
adds no new numerical certificate: it re-states each numerical claim of the text with the text's own
constants and ranges, and proves the few claims that the legacy files did not state literally

* the middle inequality `ϑ ≤ 1 + 2x + 2x⁴/(1-x)` of `eq:reaudit-S022-majorant`, and `x < 1/3`;
* the exact formula `eq:theta-shell-integral-bound` (equality, with **no** factor `e^A` in front of
  the Laplace integral) and the false-ness of the version with that extra factor;
* the Taylor sum of degree 16 (the text says degree 16; the legacy file used degree 23);
* the 40 witnesses exactly as printed (twelve listed numbers, then `1` except `0` at `q = 35, 38, 39`)
  and their sum `1638798566936 · 10⁻¹²`;
* `J_{10} ≤ 41/25`, `J_2 ≤ J_{10}/5 ≤ 41/125`.

Witnesses are the ones of `audit/theta_witnesses.json` (they coincide with the legacy array
`ThetaPolynomialCertificate.rounded`, proved below).  All kernel evaluation is `decide +kernel`. -/

noncomputable section
open MeasureTheory Finset
open Legacy.BecknerOnofri

namespace BecknerOnofri.V2.Reaudit.ShellMargins

/-! ### The polynomial majorant (`eq:reaudit-S022-majorant`) -/

/-- `(j+2)² ≥ 4 + j` for `j ≥ 0` (the elementary inequality before `eq:reaudit-S022-majorant`; [TeX `manuscript_v2_proposed.tex` line 2087]). -/
theorem sq_add_two_ge (j : ℕ) : 4 + j ≤ (j + 2) ^ 2 := by nlinarith

/-- For `t ≥ π`, `x = e^{-t} < 1/3` (text: "put `x = e^{-t} < 1/3`", [TeX `manuscript_v2_proposed.tex` line 2087]). -/
theorem exp_neg_lt_one_third {t : ℝ} (ht : Real.pi ≤ t) : Real.exp (-t) < 1 / 3 := by
  have h3 : (3 : ℝ) < Real.exp t := by
    have := Real.add_one_le_exp t
    linarith [Real.pi_gt_three]
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) h3

/-- First inequality of `eq:reaudit-S022-majorant`:
`ϑ(t) ≤ 1 + 2x + 2x⁴/(1-x)` for `t ≥ π`, `x = e^{-t}`; `ϑ(t) = ∑_{j ∈ ℤ} e^{-t j²}`. -/
theorem theta_le_middle {t : ℝ} (ht : Real.pi ≤ t) :
    ThetaDomination.realTheta t ≤
      1 + 2 * Real.exp (-t) + 2 * Real.exp (-t) ^ 4 / (1 - Real.exp (-t)) := by
  have htpos : 0 < t := lt_of_lt_of_le Real.pi_pos ht
  have hq := ThetaDomination.exp_neg_le_one_third ht
  have hden : 0 < 1 - Real.exp (-t) := by linarith
  have htail := ThetaDomination.realTheta_positive_tail_le ht
  have hnat : Summable (fun n : ℕ ↦ Real.exp (-t * (n : ℝ) ^ 2)) := by
    simpa only [Int.cast_natCast] using
      (summable_int_iff_summable_nat_and_neg.mp (ThetaDomination.summable_realTheta htpos)).1
  have hone : Summable (fun n : ℕ ↦ Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr hnat
  have he := hone.tsum_eq_zero_add
  simp only [Nat.zero_add, Nat.cast_one, one_pow, mul_one,
    show ∀ n : ℕ, n + 1 + 1 = n + 2 from fun n ↦ by omega] at he
  rw [ThetaDomination.realTheta_eq_one_add_two_mul_tsum htpos, he]
  have hdiv : 2 * Real.exp (-t) ^ 4 / (1 - Real.exp (-t)) =
      2 * (Real.exp (-t) ^ 4 * (1 - Real.exp (-t))⁻¹) := by
    rw [div_eq_mul_inv]; ring
  rw [hdiv]
  nlinarith only [htail]

/-- Second inequality of `eq:reaudit-S022-majorant`: `2x⁴/(1-x) ≤ 3x⁴` for `x ≤ 1/3`. -/
theorem middle_le_cubic {x : ℝ} (hx : x ≤ 1 / 3) :
    2 * x ^ 4 / (1 - x) ≤ 3 * x ^ 4 := by
  have hden : 0 < 1 - x := by linarith
  rw [div_le_iff₀ hden]
  have : 0 ≤ x ^ 4 := by positivity
  nlinarith [mul_nonneg this (by linarith : (0:ℝ) ≤ 1 / 3 - x)]

/-- **`eq:reaudit-S022-majorant`** in full [TeX `manuscript_v2_proposed.tex` lines 2086-2092]: for `t ≥ π` and `x = e^{-t}`,
`x < 1/3` and `ϑ(t) ≤ 1 + 2x + 2x⁴/(1-x) ≤ 1 + 2x + 3x⁴`. -/
theorem majorant {t : ℝ} (ht : Real.pi ≤ t) :
    Real.exp (-t) < 1 / 3 ∧
      ThetaDomination.realTheta t ≤
        1 + 2 * Real.exp (-t) + 2 * Real.exp (-t) ^ 4 / (1 - Real.exp (-t)) ∧
      1 + 2 * Real.exp (-t) + 2 * Real.exp (-t) ^ 4 / (1 - Real.exp (-t)) ≤
        1 + 2 * Real.exp (-t) + 3 * Real.exp (-t) ^ 4 := by
  refine ⟨exp_neg_lt_one_third ht, theta_le_middle ht, ?_⟩
  have := middle_le_cubic (ThetaDomination.exp_neg_le_one_third ht)
  linarith

/-! ### The coefficients `c_q` -/

/-- Re-indexing of the forty terms. -/
theorem sum_Icc_one_forty {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ q ∈ Icc 1 40, f q = ∑ q ∈ range 40, f (q + 1) := by
  rw [show Icc 1 40 = (range 40).image (· + 1) from by decide +kernel,
    sum_image (by intro a _ b _ h; simpa using h)]


/-- `c_q`: the coefficient of `x^q` in `(1 + 2x + 3x⁴)^10 - 1` (a natural number by construction; [TeX `manuscript_v2_proposed.tex` line 2092]). -/
abbrev c (q : ℕ) : ℕ := ThetaPolynomialCertificate.coeff q

/-- `(1 + 2x + 3x⁴)^10 - 1 = ∑_{q=1}^{40} c_q x^q`, an identity of polynomials in `x`. -/
theorem polynomial_expansion (x : ℝ) :
    (1 + 2 * x + 3 * x ^ 4) ^ 10 - 1 = ∑ q ∈ Icc 1 40, (c q : ℝ) * x ^ q := by
  rw [ThetaPolynomialCertificate.polynomial_identity x, sum_Icc_one_forty]

/-- `c_35 = c_38 = c_39 = 0`, and `c_q > 0` for every other `q ∈ [1, 40]` ([TeX `manuscript_v2_proposed.tex` lines 2092 and 2138]). -/
theorem c_vanishing :
    c 35 = 0 ∧ c 38 = 0 ∧ c 39 = 0 ∧
      ∀ q : Fin 41, 1 ≤ q.val → q.val ≠ 35 → q.val ≠ 38 → q.val ≠ 39 → 0 < c q.val := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel

/-! ### The endpoints `π₋ = 6283185/2000000` and `η = 4321393/10^8` -/

/-- `π₋ = 6283185/2000000 < π` (`eq:theta-rational-endpoints`, [TeX `manuscript_v2_proposed.tex` lines 2096-2099]); proved from Mathlib's
`Real.pi_gt_d20`, not from Machin's identity `eq:machin-identity`. -/
theorem piMinus_lt_pi : (6283185 / 2000000 : ℝ) < Real.pi := by
  linarith [Real.pi_gt_d20]

/-- The positive Taylor sum of degree 16 at `π₋` already exceeds `1/η` (text: "the positive Taylor sum
`∑_{j=0}^{16} π₋^j/j!` already exceeds `1/η`"). -/
theorem taylor16_gt_inv_eta :
    1 / (4321393 / 10 ^ 8 : ℝ) < ∑ j ∈ range 17, (6283185 / 2000000 : ℝ) ^ j / (j.factorial : ℝ) := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_piMinus_gt_inv_eta :
    1 / (4321393 / 10 ^ 8 : ℝ) < Real.exp (6283185 / 2000000) :=
  lt_of_lt_of_le taylor16_gt_inv_eta (Real.sum_le_exp_of_nonneg (by norm_num) 17)

/-- `η = 4321393/10^8 > e^{-π₋} > e^{-π}` (`eq:theta-rational-endpoints`, [TeX `manuscript_v2_proposed.tex` lines 2096-2099]). -/
theorem eta_endpoint :
    Real.exp (-(6283185 / 2000000 : ℝ)) < 4321393 / 10 ^ 8 ∧
      Real.exp (-Real.pi) < Real.exp (-(6283185 / 2000000 : ℝ)) := by
  refine ⟨?_, Real.exp_lt_exp.mpr (by linarith [piMinus_lt_pi])⟩
  have h := exp_piMinus_gt_inv_eta
  have hp : (0 : ℝ) < Real.exp (6283185 / 2000000) := Real.exp_pos _
  rw [Real.exp_neg]
  exact (inv_lt_comm₀ (by norm_num) hp).mp (by simpa only [one_div] using h)

/-! ### The exact integral formula (`eq:theta-shell-integral-bound`) -/

/-- **`eq:theta-shell-integral-bound`** [TeX `manuscript_v2_proposed.tex` lines 2105-2111].  For `A > 0`,
`∫_1^∞ (r⁴ + r⁻¹) e^{-Ar} dr = e^{-A} [1/A + 4/A² + 12/A³ + 24/A⁴ + 24/A⁵ + ∫_0^∞ e^{-v}/(A+v) dv]`.
There is no extra factor `e^A` in front of the last integral. -/
theorem shell_integral_exact {A : ℝ} (hA : 0 < A) :
    (∫ r in Set.Ici (1 : ℝ), (r ^ 4 + r⁻¹) * Real.exp (-A * r)) =
      Real.exp (-A) * (1 / A + 4 / A ^ 2 + 12 / A ^ 3 + 24 / A ^ 4 + 24 / A ^ 5 +
        ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) / (A + v)) := by
  have h := ThetaExponentialIntegral.weightIntegral
  change (∫ r in Set.Ici (1 : ℝ), ThetaExponentialIntegral.weight A r) = _
  simp_rw [ThetaExponentialIntegral.weight, add_mul]
  rw [integral_add (ThetaExponentialIntegral.integrable_polynomial hA)
      (ThetaExponentialIntegral.integrable_reciprocal hA),
    ThetaExponentialIntegral.integral_polynomial hA,
    ThetaExponentialIntegral.integral_reciprocal hA]
  ring

/-- The normalization used in the text: `∫_1^∞ r⁻¹ e^{-Ar} dr = e^{-A} ∫_0^∞ e^{-v}/(A+v) dv`. -/
theorem reciprocal_normalization {A : ℝ} (hA : 0 < A) :
    (∫ r in Set.Ici (1 : ℝ), r⁻¹ * Real.exp (-A * r)) =
      Real.exp (-A) * ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) / (A + v) :=
  ThetaExponentialIntegral.integral_reciprocal hA

theorem laplace_integral_pos {A : ℝ} (hA : 0 < A) :
    0 < ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) / (A + v) := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun v : ℝ => Real.exp (-v) / (A + v)) ∩ Set.Ioi 0 = Set.Ioi 0 := by
      ext v
      simp only [Function.mem_support, Set.mem_inter_iff, Set.mem_Ioi]
      constructor
      · exact fun h => h.2
      · intro hv
        exact ⟨(div_pos (Real.exp_pos _) (by linarith)).ne', hv⟩
    rw [this]
    simp
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    exact (div_pos (Real.exp_pos _) (by simp only [Set.mem_Ioi] at hv; linarith)).le
  · exact LaplaceReciprocal.reciprocal_integrable hA

/-- The version of `eq:theta-shell-integral-bound` with an extra factor `e^A` in front of the Laplace
integral (the error of the earlier dossier) is false for every `A > 0`. -/
theorem shell_integral_extra_factor_false {A : ℝ} (hA : 0 < A) :
    (∫ r in Set.Ici (1 : ℝ), (r ^ 4 + r⁻¹) * Real.exp (-A * r)) ≠
      Real.exp (-A) * (1 / A + 4 / A ^ 2 + 12 / A ^ 3 + 24 / A ^ 4 + 24 / A ^ 5 +
        Real.exp A * ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) / (A + v)) := by
  rw [shell_integral_exact hA]
  intro h
  have hI := laplace_integral_pos hA
  have hE : 1 < Real.exp A := Real.one_lt_exp_iff.mpr hA
  have h2 := mul_left_cancel₀ (Real.exp_pos (-A)).ne' h
  nlinarith

/-! ### The Laplace integral bound (`eq:reaudit-S022-laplace`) -/

/-- Polynomial division identity of the text [TeX `manuscript_v2_proposed.tex` lines 2118-2122], for `A > 0`, `v ≥ 0`, with `D = A² + 6A + 6`. -/
theorem laplace_division_identity {A v : ℝ} (hA : 0 < A) (hv : 0 ≤ v) :
    1 / (A + v) =
      (v ^ 4 - (A + 12) * v ^ 3 + (A ^ 2 + 12 * A + 48) * v ^ 2 -
        (A ^ 3 + 12 * A ^ 2 + 48 * A + 72) * v +
        (A ^ 4 + 12 * A ^ 3 + 48 * A ^ 2 + 72 * A + 36)) / (A * (A ^ 2 + 6 * A + 6) ^ 2) -
      v * (v ^ 2 - 6 * v + 6) ^ 2 / (A * (A ^ 2 + 6 * A + 6) ^ 2 * (A + v)) :=
  LaplaceReciprocal.reciprocal_identity hA hv

/-- The remainder term of the division identity is nonnegative for `v ≥ 0`. -/
theorem laplace_remainder_nonneg {A v : ℝ} (hA : 0 < A) (hv : 0 ≤ v) :
    0 ≤ v * (v ^ 2 - 6 * v + 6) ^ 2 / (A * (A ^ 2 + 6 * A + 6) ^ 2 * (A + v)) := by
  have hD : 0 < A ^ 2 + 6 * A + 6 := by positivity
  positivity

/-- `∫_0^∞ e^{-v} P_A(v) dv = (A² + 5A + 2) D`, `D = A² + 6A + 6`. -/
theorem laplace_polynomial_integral (A : ℝ) :
    (∫ v in Set.Ioi (0 : ℝ),
      (v ^ 4 - (A + 12) * v ^ 3 + (A ^ 2 + 12 * A + 48) * v ^ 2 -
        (A ^ 3 + 12 * A ^ 2 + 48 * A + 72) * v +
        (A ^ 4 + 12 * A ^ 3 + 48 * A ^ 2 + 72 * A + 36)) * Real.exp (-v)) =
      (A ^ 2 + 5 * A + 2) * (A ^ 2 + 6 * A + 6) :=
  LaplaceReciprocal.polynomial_integral A

/-- **`eq:reaudit-S022-laplace`** [TeX `manuscript_v2_proposed.tex` lines 2113-2124]. -/
theorem laplace_bound {A : ℝ} (hA : 0 < A) :
    (∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) / (A + v)) ≤
      (A ^ 2 + 5 * A + 2) / (A * (A ^ 2 + 6 * A + 6)) :=
  LaplaceReciprocal.integral_upper hA

/-- The remark on the choice of the quadratic `v² + a v + b`: `6 + 2a + b = 0` and `24 + 6a + 2b = 0`
force `a = -6`, `b = 6`. -/
theorem quadratic_orthogonality {a b : ℝ} (h1 : 6 + 2 * a + b = 0) (h2 : 24 + 6 * a + 2 * b = 0) :
    a = -6 ∧ b = 6 := by
  constructor <;> linarith

/-! ### From `J_10` to forty integrals (`eq:theta-shell-integrals`) -/

/-- **`eq:theta-shell-integrals`** [TeX `manuscript_v2_proposed.tex` lines 2101-2103].  With `π₋ = 6283185/2000000`,
`J_10 ≤ ∑_{q=1}^{40} c_q ∫_1^∞ (r⁴ + r⁻¹) e^{-π₋ q r} dr`. -/
theorem J10_le_shell_integrals :
    ThetaDomination.thetaIntegral ThetaDomination.realTheta 10 ≤
      ∑ q ∈ Icc 1 40, (c q : ℝ) *
        ∫ r in Set.Ici (1 : ℝ), (r ^ 4 + r⁻¹) * Real.exp (-((6283185 / 2000000 : ℝ) * q) * r) := by
  have ha : ((ThetaCertificate.a : ℚ) : ℝ) = 6283185 / 2000000 := by
    norm_num [ThetaCertificate.a]
  have hi (q : ℕ) : IntegrableOn
      (fun u => (ThetaPolynomialCertificate.coeff (q+1) : ℝ) *
        ThetaExponentialIntegral.weight (((ThetaCertificate.a : ℚ) : ℝ) * (q+1)) u) (Set.Ici (1 : ℝ)) :=
    (ThetaExponentialIntegral.integrable_weight
      (mul_pos ThetaCertificate.a_pos (by positivity) :
        0 < ((ThetaCertificate.a : ℚ) : ℝ) * (q+1))).const_mul _
  have hs := integrable_finsetSum (range 40) (fun q _ => hi q)
  have h1 : ThetaDomination.thetaIntegral ThetaDomination.realTheta 10 ≤
      ∑ q ∈ range 40, (ThetaPolynomialCertificate.coeff (q+1) : ℝ) *
        ThetaExponentialIntegral.weightIntegral (((ThetaCertificate.a : ℚ) : ℝ) * (q+1)) := by
    calc
      _ ≤ ∫ u in Set.Ici (1 : ℝ), ∑ q ∈ range 40,
          (ThetaPolynomialCertificate.coeff (q+1) : ℝ) *
            ThetaExponentialIntegral.weight (((ThetaCertificate.a : ℚ) : ℝ) * (q+1)) u := by
        apply setIntegral_mono_on ThetaDomination.integrableOn_realThetaIntegrand_ten hs
          measurableSet_Ici
        intro u hu
        exact ThetaBound.integrand_le_finite_sum hu
      _ = _ := by
        rw [integral_finsetSum (range 40) (fun q _ => hi q)]
        simp only [integral_const_mul, ThetaExponentialIntegral.weightIntegral]
  refine h1.trans (le_of_eq ?_)
  rw [sum_Icc_one_forty]
  refine sum_congr rfl fun q _ => ?_
  simp only [ThetaExponentialIntegral.weightIntegral, ThetaExponentialIntegral.weight, ha]
  push_cast
  rfl

/-- The bracket of `eq:theta-finite-rational-comparison` as a function of `A = π₋ q`. -/
def bracket (A : ℝ) : ℝ :=
  1 / A + 4 / A ^ 2 + 12 / A ^ 3 + 24 / A ^ 4 + 24 / A ^ 5 +
    (A ^ 2 + 5 * A + 2) / (A * (A ^ 2 + 6 * A + 6))

/-- **`eq:theta-finite-rational-comparison`** [TeX `manuscript_v2_proposed.tex` lines 2127-2132].
`J_10 ≤ ∑_{q=1}^{40} c_q η^q [ 1/(π₋q) + 4/(π₋q)² + 12/(π₋q)³ + 24/(π₋q)⁴ + 24/(π₋q)⁵
  + ((π₋q)² + 5π₋q + 2)/(π₋q((π₋q)² + 6π₋q + 6)) ]`, `η = 4321393/10^8`. -/
theorem J10_le_finite_rational :
    ThetaDomination.thetaIntegral ThetaDomination.realTheta 10 ≤
      ∑ q ∈ Icc 1 40, (c q : ℝ) * (4321393 / 10 ^ 8 : ℝ) ^ q *
        bracket ((6283185 / 2000000 : ℝ) * q) := by
  have ha : ((ThetaCertificate.a : ℚ) : ℝ) = 6283185 / 2000000 := by
    norm_num [ThetaCertificate.a]
  have hr : ((ThetaCertificate.r : ℚ) : ℝ) = 4321393 / 10 ^ 8 := by
    norm_num [ThetaCertificate.r]
  have h := ThetaBound.integral_le_certificate
  refine h.trans (le_of_eq ?_)
  unfold ThetaPolynomialCertificate.upperReal
  rw [sum_Icc_one_forty]
  refine sum_congr rfl fun q _ => ?_
  simp only [ThetaPolynomialCertificate.factorReal, bracket, ha, hr]
  push_cast
  rfl

/-! ### The forty rational comparisons and their sum -/

/-- The twelve printed numbers (units of `10⁻¹²`; [TeX `manuscript_v2_proposed.tex` lines 2133-2137]). -/
def firstTwelve : List ℕ :=
  [1459125207561, 156702351207, 20570797669, 2199652302, 185983454, 13508923,
    985145, 75076, 5235, 317, 20, 2]

/-- The printed bound for index `q ∈ [1, 40]` ([TeX `manuscript_v2_proposed.tex` lines 2133-2138]): the `q`-th printed number for `q ≤ 12`; for
`13 ≤ q ≤ 40` it is `1`, except that it is `0` for `q = 35, 38, 39`. -/
def textBound (q : ℕ) : ℕ :=
  if q ≤ 12 then firstTwelve.getD (q - 1) 0
  else if q = 35 ∨ q = 38 ∨ q = 39 then 0 else 1

/-- The printed witnesses are the legacy witnesses `ThetaPolynomialCertificate.rounded`. -/
theorem textBound_eq_rounded :
    ∀ i : Fin 40, textBound (i.val + 1) = ThetaPolynomialCertificate.rounded[i.val]! := by
  decide +kernel

/-- The rational term of the finite sum (exact rational arithmetic, `A = π₋ q`). -/
def termQ (q : ℕ) : ℚ :=
  (c q : ℚ) * (4321393 / 10 ^ 8 : ℚ) ^ q *
    (1 / ((6283185 / 2000000 : ℚ) * q) + 4 / ((6283185 / 2000000 : ℚ) * q) ^ 2 +
      12 / ((6283185 / 2000000 : ℚ) * q) ^ 3 + 24 / ((6283185 / 2000000 : ℚ) * q) ^ 4 +
      24 / ((6283185 / 2000000 : ℚ) * q) ^ 5 +
      (((6283185 / 2000000 : ℚ) * q) ^ 2 + 5 * ((6283185 / 2000000 : ℚ) * q) + 2) /
        (((6283185 / 2000000 : ℚ) * q) *
          (((6283185 / 2000000 : ℚ) * q) ^ 2 + 6 * ((6283185 / 2000000 : ℚ) * q) + 6)))

/-- "Cross-multiplication verifies each of the forty comparisons": each rational term is at most the
printed bound times `10⁻¹²`. -/
theorem forty_comparisons :
    ∀ q : Fin 41, 1 ≤ q.val → termQ q.val ≤ (textBound q.val : ℚ) / 10 ^ 12 := by
  have h := ThetaPolynomialCertificate.term_checks
  intro q hq
  obtain ⟨i, hi⟩ : ∃ i : Fin 40, i.val + 1 = q.val := ⟨⟨q.val - 1, by omega⟩, by simp; omega⟩
  have h1 := h i
  rw [← textBound_eq_rounded i] at h1
  rw [← hi]
  have e : termQ (i.val + 1) = ThetaPolynomialCertificate.termQ (i.val + 1) := by
    unfold termQ ThetaPolynomialCertificate.termQ ThetaPolynomialCertificate.factorQ
      ThetaCertificate.a ThetaCertificate.r
    rfl
  rw [e]
  exact h1

/-- The sum of the printed bounds is `1638798566936 · 10⁻¹²` ([TeX `manuscript_v2_proposed.tex` line 2138]). -/
theorem textBound_sum : ∑ q ∈ Icc 1 40, textBound q = 1638798566936 := by
  decide +kernel

theorem textBound_sum_lt : (1638798566936 : ℚ) / 10 ^ 12 < 41 / 25 := by norm_num

/-- The exact rational sum of the forty terms is below `1638798566936 · 10⁻¹²`. -/
theorem rational_sum_le : ∑ q ∈ Icc 1 40, termQ q ≤ (1638798566936 : ℚ) / 10 ^ 12 := by
  calc ∑ q ∈ Icc 1 40, termQ q ≤ ∑ q ∈ Icc 1 40, (textBound q : ℚ) / 10 ^ 12 := by
        apply sum_le_sum
        intro q hq
        have hq' := mem_Icc.mp hq
        exact forty_comparisons ⟨q, by omega⟩ hq'.1
    _ = ((∑ q ∈ Icc 1 40, textBound q : ℕ) : ℚ) / 10 ^ 12 := by
        rw [← sum_div]; push_cast; rfl
    _ = _ := by rw [textBound_sum]; norm_num

/-- Real version of the preceding sum, with the real terms of `J10_le_finite_rational`. -/
theorem real_sum_le :
    (∑ q ∈ Icc 1 40, (c q : ℝ) * (4321393 / 10 ^ 8 : ℝ) ^ q *
        bracket ((6283185 / 2000000 : ℝ) * q)) ≤ (1638798566936 : ℝ) / 10 ^ 12 := by
  have h := (Rat.cast_le (K := ℝ)).2 rational_sum_le
  push_cast at h
  convert h using 1
  refine sum_congr rfl fun q _ => ?_
  simp only [termQ, bracket]
  push_cast
  rfl

/-- `J_10 ≤ 1638798566936 · 10⁻¹² = 1.638798566936`. -/
theorem J10_le_printed_sum :
    ThetaDomination.thetaIntegral ThetaDomination.realTheta 10 ≤ (1638798566936 : ℝ) / 10 ^ 12 :=
  J10_le_finite_rational.trans real_sum_le

/-- **`lem:theta-integral-certificate`** [TeX `manuscript_v2_proposed.tex` lines 2081-2084 and 2138-2139] in the form printed (`J_10 ≤ 41/25`), on the manuscript's
definition `J_d = ∫_1^∞ (r^{d/2-1} + r⁻¹)(ϑ(πr)^d - 1) dr`
(`BecknerOnofri.HighDim.LowScalar.thetaIntegral`). -/
theorem lem_theta_integral_certificate :
    HighDim.LowScalar.thetaIntegral 10 ≤ (41 / 25 : ℝ) := by
  have h := J10_le_printed_sum
  have h2 : (1638798566936 : ℝ) / 10 ^ 12 < 41 / 25 := by norm_num
  exact (le_of_lt (lt_of_le_of_lt h h2))

/-- `J_2 ≤ J_10 / 5 ≤ 41/125` (used in `eq:reaudit-S020-two-central`; [TeX `manuscript_v2_proposed.tex` line 2187]). -/
theorem J2_le_41_125 :
    HighDim.LowScalar.thetaIntegral 2 ≤ HighDim.LowScalar.thetaIntegral 10 / 5 ∧
      HighDim.LowScalar.thetaIntegral 10 / 5 ≤ (41 / 125 : ℝ) := by
  have h := ThetaDomination.realThetaIntegral_le_tenth_unconditional (d := 2) (by norm_num)
  constructor
  · change ThetaDomination.thetaIntegral ThetaDomination.realTheta 2 ≤
      ThetaDomination.thetaIntegral ThetaDomination.realTheta 10 / 5
    have : ((2 : ℕ) : ℝ) / 10 * ThetaDomination.thetaIntegral ThetaDomination.realTheta 10 =
        ThetaDomination.thetaIntegral ThetaDomination.realTheta 10 / 5 := by push_cast; ring
    linarith
  · have := lem_theta_integral_certificate
    linarith

end BecknerOnofri.V2.Reaudit.ShellMargins

end

