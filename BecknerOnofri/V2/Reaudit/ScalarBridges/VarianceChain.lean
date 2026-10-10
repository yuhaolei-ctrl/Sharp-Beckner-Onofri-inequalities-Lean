module

public import BecknerOnofri.V2.FiniteState.FamilyComparison
public import BecknerOnofri.V2.FiniteState.VarianceComparison
public import BecknerOnofri.V2.FiniteState.ExpBound
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! # `d12-spin-lem:perturb` (S052) and `d12-spin-eq:mgflower`, `d12-spin-eq:onesided` (U17)
along the printed argument

Printed proof (V2 TeX 3881-3903):

1. Finite entropy variational inequality.  For a positive vector `p` and real `H`, normalize
   `p_j e^{H_j}` to a probability vector `r` and use nonnegativity of relative entropy,
   obtained "by summing `u log u - u + 1 ≥ 0` against the normalized positive vector":
   `∑ q H - Hr(q | p) ≤ log ∑ p e^H`.   (`gibbs_variational_printed`)
2. With the mass and mean constraints and the centering identity,
   `∑ g_j(p)(q_j - p_j) = ∑ q_j e_j`; applying (1) with `H = -5e` to Corollary 5.18
   gives `F(q) ≥ F(p) - (1/5) log E_p e^{-5e}`.  (`mgflower`)
3. One-sided bound: mean-zero `Y ≤ B < 3`, `B ≥ 0` gives `log E e^Y ≤ E Y² / (2 (1 - B/3))`;
   for `Y ≤ 0` Taylor's integral remainder gives `e^Y ≤ 1 + Y + Y²/2`; for `0 ≤ Y ≤ B`
   use `k! ≥ 2·3^{k-2}` in the exponential series; take expectations and use `log u ≤ u - 1`.
   (`exp_le_quadratic_of_nonpos_integral`, `exp_le_one_sided_printed`,
   `log_expectation_exp_le_printed`, `log_integral_exp_le`)
4. `Y = -5e`, `E_p Y = 0`, `Y ≤ 5/4`:  `(1/5) log E_p e^{-5e} ≤ (30/7) 𝒱`.
   (`scaled_log_mgf_le_printed`; the lemma `perturb_printed`.)
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace BecknerOnofri.V2.Reaudit.ScalarBridges

open scoped BigOperators
open MeasureTheory

/-! ### Step 1: normalization and nonnegativity of relative entropy -/

/-- `u log u - u + 1 ≥ 0` for `u ≥ 0`. -/
theorem xlogx_sub_add_one_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ u * Real.log u - u + 1 := by
  rcases hu.eq_or_lt with rfl | hpos
  · simp
  · have h := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv] at h
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    rw [mul_sub, mul_inv_cancel₀ hpos.ne'] at h2
    nlinarith

section Finite

variable {ι : Type*} [Fintype ι]

/-- Nonnegativity of relative entropy against a normalized positive vector, by summing
`u log u - u + 1 ≥ 0` against it:  `∑ r_i φ(q_i / r_i) = ∑ q log(q/r) - ∑ q + ∑ r`. -/
theorem relEntropy_nonneg_normalized (r q : ι → ℝ) (hr : ∀ i, 0 < r i) (hrm : ∑ i, r i = 1)
    (hq : ∀ i, 0 ≤ q i) (hqm : ∑ i, q i = 1) :
    0 ≤ ∑ i, q i * Real.log (q i / r i) := by
  have h : ∀ i, 0 ≤ r i * ((q i / r i) * Real.log (q i / r i) - q i / r i + 1) :=
    fun i => mul_nonneg (hr i).le (xlogx_sub_add_one_nonneg (div_nonneg (hq i) (hr i).le))
  have e : ∀ i, r i * ((q i / r i) * Real.log (q i / r i) - q i / r i + 1)
      = q i * Real.log (q i / r i) - q i + r i := by
    intro i
    have := (hr i).ne'
    field_simp
  have hs := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) => h i)
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, hqm, hrm] at hs
  linarith

/-- **Finite entropy variational inequality** (printed step): for a positive vector `p`, real `H`
and a probability vector `q`,  `∑ q H - Hr(q | p) ≤ log ∑ p e^H`.  Proved by normalizing
`p_j e^{H_j}` and using nonnegativity of relative entropy.  (Only positivity of `p` is used.) -/
theorem gibbs_variational_printed [Nonempty ι] (p q H : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i) (hqm : ∑ i, q i = 1) :
    (∑ i, q i * H i) - (∑ i, q i * Real.log (q i / p i)) ≤
      Real.log (∑ i, p i * Real.exp (H i)) := by
  set Z : ℝ := ∑ i, p i * Real.exp (H i) with hZdef
  have hZ : 0 < Z :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (Real.exp_pos _)) Finset.univ_nonempty
  set r : ι → ℝ := fun i => p i * Real.exp (H i) / Z with hrdef
  have hr : ∀ i, 0 < r i := fun i => div_pos (mul_pos (hp i) (Real.exp_pos _)) hZ
  have hrm : ∑ i, r i = 1 := by
    simp only [hrdef]
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hrel := relEntropy_nonneg_normalized r q hr hrm hq hqm
  have hterm : ∀ i, q i * Real.log (q i / r i) =
      q i * Real.log (q i / p i) - q i * H i + q i * Real.log Z := by
    intro i
    rcases (hq i).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · have hlogr : Real.log (r i) = Real.log (p i) + H i - Real.log Z := by
        simp only [hrdef]
        rw [Real.log_div (mul_pos (hp i) (Real.exp_pos _)).ne' hZ.ne',
          Real.log_mul (hp i).ne' (Real.exp_pos _).ne', Real.log_exp]
      rw [Real.log_div h0.ne' (hr i).ne', Real.log_div h0.ne' (hp i).ne', hlogr]
      ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hqm,
    one_mul] at hrel
  linarith

end Finite

/-! ### Step 3: the one-sided exponential bound -/

/-- Taylor's integral remainder for the exponential:
`e^y = 1 + y + ∫_0^y (y - s) e^s ds`. -/
theorem exp_sub_one_sub_eq_integral (y : ℝ) :
    Real.exp y - 1 - y = ∫ s in (0 : ℝ)..y, (y - s) * Real.exp s := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) y,
      HasDerivAt (fun s : ℝ => (y - s) * Real.exp s + Real.exp s) ((y - x) * Real.exp x) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => y - s) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub y
    have h2 := (h1.mul (Real.hasDerivAt_exp x)).add (Real.hasDerivAt_exp x)
    convert h2 using 1
    ring
  have hi : IntervalIntegrable (fun s : ℝ => (y - s) * Real.exp s) MeasureTheory.volume 0 y :=
    (by fun_prop : Continuous fun s : ℝ => (y - s) * Real.exp s).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp
  ring

/-- For `y ≤ 0`, Taylor's integral remainder gives `e^y ≤ 1 + y + y²/2`
(printed step, first case of eq:onesided). -/
theorem exp_le_quadratic_of_nonpos_integral {y : ℝ} (hy : y ≤ 0) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  have h1 := exp_sub_one_sub_eq_integral y
  have hsym : ∫ s in (0 : ℝ)..y, (y - s) * Real.exp s = ∫ s in y..(0 : ℝ), (s - y) * Real.exp s := by
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    congr 1
    ext s
    ring
  have hc1 : Continuous fun s : ℝ => (s - y) * Real.exp s := by fun_prop
  have hc2 : Continuous fun s : ℝ => (s - y) := by fun_prop
  have hmono : ∫ s in y..(0 : ℝ), (s - y) * Real.exp s ≤ ∫ s in y..(0 : ℝ), (s - y) := by
    apply intervalIntegral.integral_mono_on hy (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _)
    intro s hs
    have hexp : Real.exp s ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 hs.2
    have hsy : 0 ≤ s - y := by linarith [hs.1]
    nlinarith
  have hval : ∫ s in y..(0 : ℝ), (s - y) = y ^ 2 / 2 := by
    rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ => s) y]
    simp [integral_id]
  linarith

/-- The pointwise one-sided bound (printed): `0 ≤ B < 3`, `y ≤ B` give
`e^y ≤ 1 + y + y²/(2(1 - B/3))`.  Negative `y` use the integral remainder, `0 ≤ y ≤ B` use
`k! ≥ 2·3^{k-2}` in the exponential series (`exp_le_geometric_of_nonneg`). -/
theorem exp_le_one_sided_printed {y B : ℝ} (hB0 : 0 ≤ B) (hB3 : B < 3) (hyB : y ≤ B) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - B / 3)) := by
  have hden : 0 < 2 * (1 - B / 3) := by linarith
  by_cases hy : y ≤ 0
  · have h := exp_le_quadratic_of_nonpos_integral hy
    have h2 : y ^ 2 / 2 ≤ y ^ 2 / (2 * (1 - B / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg y) hden
      nlinarith
    linarith
  · push Not at hy
    have h := BecknerOnofri.V2.FiniteState.exp_le_geometric_of_nonneg hy.le (by linarith)
    have h2 : y ^ 2 / (2 * (1 - y / 3)) ≤ y ^ 2 / (2 * (1 - B / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg y) hden
      linarith
    linarith

section Finite2

variable {ι : Type*} [Fintype ι]

/-- `d12-spin-eq:onesided` for a finite probability space with positive weights:
mean zero, `Y ≤ B < 3`, `B ≥ 0` give `log E e^Y ≤ E Y² / (2(1 - B/3))`.  Expectations then
`log u ≤ u - 1`. -/
theorem log_expectation_exp_le_printed [Nonempty ι] (p Y : ι → ℝ) {B : ℝ}
    (hp : ∀ i, 0 < p i) (hmass : ∑ i, p i = 1) (hmean : ∑ i, p i * Y i = 0)
    (hB0 : 0 ≤ B) (hB3 : B < 3) (hY : ∀ i, Y i ≤ B) :
    Real.log (∑ i, p i * Real.exp (Y i)) ≤
      (∑ i, p i * Y i ^ 2) / (2 * (1 - B / 3)) := by
  have hZ : 0 < ∑ i, p i * Real.exp (Y i) :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (Real.exp_pos _)) Finset.univ_nonempty
  have hpt (i : ι) : p i * Real.exp (Y i) ≤
      p i + p i * Y i + p i * Y i ^ 2 / (2 * (1 - B / 3)) := by
    have h := mul_le_mul_of_nonneg_left (exp_le_one_sided_printed hB0 hB3 (hY i)) (hp i).le
    calc p i * Real.exp (Y i) ≤ p i * (1 + Y i + Y i ^ 2 / (2 * (1 - B / 3))) := h
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpt i)
  have hZ1 : (∑ i, p i * Real.exp (Y i)) ≤
      1 + (∑ i, p i * Y i ^ 2) / (2 * (1 - B / 3)) := by
    simpa only [Finset.sum_add_distrib, ← Finset.sum_div, hmass, hmean, add_zero] using hsum
  have hlog := Real.log_le_sub_one_of_pos hZ
  linarith

/-- Step 4:  `Y = -5e`, `E_p Y = 0`, `Y ≤ 5/4`, so `(1/5) log E_p e^{-5e} ≤ (5/2)/(1 - 5/12) 𝒱 = (30/7) 𝒱`. -/
theorem scaled_log_mgf_le_printed [Nonempty ι] (p e : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hmass : ∑ i, p i = 1) (hmean : ∑ i, p i * e i = 0)
    (he : ∀ i, -(1 / 4 : ℝ) ≤ e i) :
    (1 / 5 : ℝ) * Real.log (∑ i, p i * Real.exp (-5 * e i)) ≤
      (30 / 7 : ℝ) * ∑ i, p i * e i ^ 2 := by
  have hmean' : ∑ i, p i * (-5 * e i) = 0 := by
    have : ∑ i, p i * (-5 * e i) = -5 * ∑ i, p i * e i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hmean]; ring
  have h := log_expectation_exp_le_printed p (fun i => -5 * e i) (B := 5 / 4) hp hmass hmean'
    (by norm_num) (by norm_num) (fun i => by linarith [he i])
  beta_reduce at h
  have hsq : ∑ i, p i * (-5 * e i) ^ 2 = 25 * ∑ i, p i * e i ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hsq] at h
  have hc : (2 : ℝ) * (1 - 5 / 4 / 3) = 7 / 6 := by norm_num
  rw [hc] at h
  have hV : 0 ≤ ∑ i, p i * e i ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i).le (sq_nonneg _))
  linarith

end Finite2

/-- `d12-spin-eq:onesided` for an arbitrary real random variable on a probability space
(`E Y² < ∞` is assumed: otherwise the right side is `+∞` and there is nothing to prove). -/
theorem log_integral_exp_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {B : ℝ}
    (hYm : AEMeasurable Y μ) (hYB : ∀ᵐ ω ∂μ, Y ω ≤ B) (hint : Integrable Y μ)
    (hsq : Integrable (fun ω => Y ω ^ 2) μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (hB0 : 0 ≤ B) (hB3 : B < 3) :
    Real.log (∫ ω, Real.exp (Y ω) ∂μ) ≤ (∫ ω, Y ω ^ 2 ∂μ) / (2 * (1 - B / 3)) := by
  set c : ℝ := 2 * (1 - B / 3) with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hexpint : Integrable (fun ω => Real.exp (Y ω)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp B))
      ((Real.measurable_exp.comp_aemeasurable hYm).aestronglyMeasurable) ?_
    filter_upwards [hYB] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 hω
  have hZ : 0 < ∫ ω, Real.exp (Y ω) ∂μ := integral_exp_pos hexpint
  have hrhs : Integrable (fun ω => 1 + Y ω + Y ω ^ 2 / c) μ :=
    ((integrable_const 1).add hint).add (hsq.div_const c)
  have hle : ∫ ω, Real.exp (Y ω) ∂μ ≤ ∫ ω, (1 + Y ω + Y ω ^ 2 / c) ∂μ := by
    refine integral_mono_ae hexpint hrhs ?_
    filter_upwards [hYB] with ω hω
    exact exp_le_one_sided_printed hB0 hB3 hω
  have hval : ∫ ω, (1 + Y ω + Y ω ^ 2 / c) ∂μ = 1 + (∫ ω, Y ω ^ 2 ∂μ) / c := by
    have i1 : Integrable (fun ω => 1 + Y ω) μ := (integrable_const 1).add hint
    have i2 : Integrable (fun ω => Y ω ^ 2 / c) μ := hsq.div_const c
    have h1 : ∫ ω, (1 + Y ω + Y ω ^ 2 / c) ∂μ =
        ∫ ω, (1 + Y ω) ∂μ + ∫ ω, Y ω ^ 2 / c ∂μ :=
      integral_add (f := fun ω => 1 + Y ω) (g := fun ω => Y ω ^ 2 / c) i1 i2
    have h2 : ∫ ω, (1 + Y ω) ∂μ = ∫ ω, (1 : ℝ) ∂μ + ∫ ω, Y ω ∂μ :=
      integral_add (f := fun _ => (1 : ℝ)) (g := Y) (integrable_const 1) hint
    rw [h1, h2, hmean, integral_div]
    simp
  have hlog := Real.log_le_sub_one_of_pos hZ
  linarith

/-! ### Step 2: `d12-spin-eq:mgflower` -/

open BecknerOnofri.HighDim.Spin
open BecknerOnofri.V2.FiniteState

/-- **`d12-spin-eq:mgflower`.**  For a positive reference vector `p ∈ 𝒫_t` and every `q ∈ 𝒫_t`
(boundary allowed), with `e_j = gradResid t p j` the weighted-regression residual of the
gradient,
`F(q) ≥ F(p) - (1/5) log E_p e^{-5e}`.
Proof as printed: the mass and mean constraints and the centering identity give
`∑ g_j(p)(q_j - p_j) = ∑ q_j e_j`; apply the variational inequality with `H = -5e` to the
Bregman-type lower bound `F(q) ≥ F(p) + ∑ g(q-p) + Hr(q|p)/5` (Corollary 5.18). -/
theorem mgflower {t : ℝ} {p q : Count → ℝ}
    (hp : FeasibleAt t p) (hpos : ∀ j, 0 < p j) (hq : FeasibleAt t q) :
    functional p - (1 / 5 : ℝ) *
        Real.log (∑ j : Count, p j * Real.exp (-5 * gradResid t p j)) ≤ functional q := by
  have hcor := fixed_mean_entropy_convexity_affine hp.1 hpos hq.1 (by rw [hp.2, hq.2])
  have hpm := hp.1.2.1
  have hqx : ∑ j : Count, q j * meanCoordinate j = t := by
    have := hq.2
    simpa [mean, mul_comm] using this
  have hpx' : ∑ j : Count, p j * meanCoordinate j = t := by
    have := hp.2
    simpa [mean, mul_comm] using this
  have hlin := gradient_pairing_eq (g := gradient p) (x := meanCoordinate) hpm hpx' hq.1.2.1 hqx
  have hgibbs := gibbs_variational_printed p q (fun j => -5 * gradResid t p j) hpos hq.1.1
    hq.1.2.1
  have hsc : (∑ j : Count, q j * (-5 * gradResid t p j)) =
      -5 * ∑ j : Count, q j * gradResid t p j := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hre : relativeEntropy q p = ∑ j : Count, q j * Real.log (q j / p j) := rfl
  change _ ≤ functional q at hcor
  rw [hlin] at hcor
  rw [hsc, ← hre] at hgibbs
  have hqe : (∑ j : Count, q j * gradResid t p j) =
      (∑ j : Count, q j * regResid p meanCoordinate (gradient p) t j) := rfl
  linarith

/-! ### Lemma `d12-spin-lem:perturb` assembled from the printed steps -/

/-- **Lemma `d12-spin-lem:perturb`** for a positive reference `p ∈ 𝒫_t`:
if `e_j ≥ -1/4` then every `q ∈ 𝒫_t` has `F(q) ≥ F(p) - (30/7) 𝒱`
(add `12 ψ(t)` on both sides for the printed shape). -/
theorem perturb_generic {t : ℝ} {p q : Count → ℝ}
    (hp : FeasibleAt t p) (hpos : ∀ j, 0 < p j) (hq : FeasibleAt t q)
    (he : ∀ j, -(1 / 4 : ℝ) ≤ gradResid t p j) :
    functional p - (30 / 7 : ℝ) * (∑ j : Count, p j * gradResid t p j ^ 2) ≤ functional q := by
  have h1 := mgflower hp hpos hq
  have hcen := regResid_center (g := gradient p) (x := meanCoordinate) hp.1.2.1
    (by simpa [mean, mul_comm] using hp.2)
  have h2 := scaled_log_mgf_le_printed p (gradResid t p) hpos hp.1.2.1 hcen he
  linarith

/-- **Lemma `d12-spin-lem:perturb`, printed statement.**  Fix `0 ≤ t < 1`.  If `e_j(t) ≥ -1/4`
for every `j`, then every `q ∈ 𝒫_t` satisfies
`F(q) + 12 ψ(t) ≥ f(t) - (30/7) 𝒱(t)`  (eq:variancecomparison), where `f(t) = F(p(t)) + 12 ψ(t)`
(`famF`), `𝒱(t) = ∑ p_j e_j²` (`famResidVar`). -/
theorem perturb_printed {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {q : Count → ℝ}
    (hq : FeasibleAt t q) (he : ∀ j : Count, -(1 / 4 : ℝ) ≤ famResid t j) :
    famF t - (30 / 7 : ℝ) * famResidVar t ≤ functional q + 12 * psiV2 t := by
  have h := perturb_generic (famLaw_feasibleAt_of_nonneg_beta ht0 ht1)
    (famLaw_pos_of_nonneg ht0 ht1) hq he
  have hF : famF t = functional (famLaw t) + 12 * psiV2 t := rfl
  have hV : famResidVar t = ∑ j : Count, famLaw t j * gradResid t (famLaw t) j ^ 2 := rfl
  rw [hF, hV]
  linarith


end BecknerOnofri.V2.Reaudit.ScalarBridges
