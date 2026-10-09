module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# One-sided exponential bound and finite Gibbs variational inequality
(Lemma 5.20 of the 2026-10 manuscript, eq. `d12-spin-eq:onesided`, `d12-spin-eq:mgflower`;
unnumbered obligation U17.)

Compiled against the pinned Mathlib.
Everything is stated for an arbitrary finite index type and arbitrary real functions;
the thirteen-state specialisation is a one-line instance (`ι := Count`).
-/

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState

/-- Taylor integral remainder (Lagrange form) for `y ≤ 0`: `e^y ≤ 1 + y + y^2/2`.
Proof copied from `BecknerOnofri.HighDim.exp_le_quadratic_of_abs_le` with `C = 0`. -/
theorem exp_le_quadratic_of_nonpos {x : ℝ} (hx0 : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  by_cases hx : x = 0
  · simp [hx]
  have hx' : (0 : ℝ) ≠ x := Ne.symm hx
  have hu := uniqueDiffOn_uIcc hx'
  have hd : derivWithin Real.exp (Set.uIcc 0 x) 0 = 1 := by
    simpa using (Real.hasDerivAt_exp 0).hasDerivWithinAt.derivWithin
      (hu 0 (Set.left_mem_uIcc))
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) (f := Real.exp) hx' Real.contDiff_exp.contDiffOn
  have htaylor : taylorWithinEval Real.exp 1 (Set.uIcc 0 x) 0 x = 1 + x := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, taylorWithinEval_succ]
    simp [hd]
  rw [htaylor] at heq
  have hderiv : iteratedDeriv 2 Real.exp = Real.exp := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    simp [Real.deriv_exp]
  rw [hderiv] at heq
  norm_num at heq
  have hy0 : y ≤ 0 := le_trans hy.2.le (max_le le_rfl hx0)
  have hexp := Real.exp_le_exp.mpr hy0
  rw [Real.exp_zero] at hexp
  have hmul := mul_le_mul_of_nonneg_right hexp (sq_nonneg x)
  nlinarith

/-- `k! ≥ 2 * 3^(k-2)`, written with `k = n + 2`. -/
theorem two_mul_three_pow_le_factorial (n : ℕ) : 2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    have h : (n + 1 + 2).factorial = (n + 3) * (n + 2).factorial := by
      rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ]
    rw [h, pow_succ]
    nlinarith

/-- The geometric majorant for `0 ≤ y < 3`: `e^y ≤ 1 + y + y^2 / (2 (1 - y/3))`. -/
theorem exp_le_geometric_of_nonneg {y : ℝ} (hy : 0 ≤ y) (hy3 : y < 3) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - y / 3)) := by
  have hr0 : 0 ≤ y / 3 := by positivity
  have hr1 : y / 3 < 1 := by linarith
  have hexp : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp y
  have hgeo : HasSum (fun n : ℕ => (y ^ 2 / 2) * (y / 3) ^ n)
      ((y ^ 2 / 2) * (1 - y / 3)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left (y ^ 2 / 2)
  have hshift : HasSum (fun n : ℕ => y ^ (n + 2) / ((n + 2).factorial : ℝ))
      (Real.exp y - (1 + y)) := by
    have h := (hasSum_nat_add_iff' 2).mpr hexp
    simpa [Finset.sum_range_succ] using h
  have hterm : ∀ n : ℕ, y ^ (n + 2) / ((n + 2).factorial : ℝ) ≤ (y ^ 2 / 2) * (y / 3) ^ n := by
    intro n
    have hf : (2 : ℝ) * 3 ^ n ≤ ((n + 2).factorial : ℝ) := by
      exact_mod_cast two_mul_three_pow_le_factorial n
    have hpos : (0 : ℝ) < 2 * 3 ^ n := by positivity
    rw [div_le_iff₀ (by exact lt_of_lt_of_le hpos hf)]
    have h1 : (y ^ 2 / 2) * (y / 3) ^ n * ((n + 2).factorial : ℝ) ≥
        (y ^ 2 / 2) * (y / 3) ^ n * (2 * 3 ^ n) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    have h2 : (y ^ 2 / 2) * (y / 3) ^ n * (2 * 3 ^ n) = y ^ (n + 2) := by
      rw [div_pow]; field_simp; ring
    linarith
  have hle := hasSum_le hterm hshift hgeo
  have hinv : (y ^ 2 / 2) * (1 - y / 3)⁻¹ = y ^ 2 / (2 * (1 - y / 3)) := by
    have : (1 - y / 3) ≠ 0 := by linarith
    field_simp
  linarith

/-- **The one-sided bound** (`d12-spin-eq:onesided`, pointwise form):
for `0 ≤ B < 3` and `y ≤ B`, `e^y ≤ 1 + y + y^2 / (2 (1 - B/3))`. -/
theorem exp_le_one_sided {y B : ℝ} (hB0 : 0 ≤ B) (hB3 : B < 3) (hyB : y ≤ B) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - B / 3)) := by
  have hden : 0 < 2 * (1 - B / 3) := by linarith
  by_cases hy : y ≤ 0
  · have h := exp_le_quadratic_of_nonpos hy
    have h2 : y ^ 2 / 2 ≤ y ^ 2 / (2 * (1 - B / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg y) hden
      nlinarith
    linarith
  · push Not at hy
    have h := exp_le_geometric_of_nonneg hy.le (by linarith)
    have h2 : y ^ 2 / (2 * (1 - y / 3)) ≤ y ^ 2 / (2 * (1 - B / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg y) hden
      linarith
    linarith

variable {ι : Type*} [Fintype ι]

/-- Young's inequality `r u ≤ r log r - r + e^u` (`r ≥ 0`), copied from
`BecknerOnofri.HighDim.entropy_young`. -/
theorem young_aux (r u : ℝ) (hr : 0 ≤ r) : r * u ≤ r * Real.log r - r + Real.exp u := by
  by_cases hz : r = 0
  · simpa [hz] using Real.exp_nonneg u
  have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  have h := Real.add_one_le_exp (u - Real.log r)
  rw [Real.exp_sub, Real.exp_log hp] at h
  have hm := (le_div_iff₀ hp).mp h
  nlinarith

theorem mul_log_div_aux (x y : ℝ) (hy : 0 < y) :
    x * Real.log (x / y) = x * Real.log x - x * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_div hx hy.ne']
    ring

/-- **Finite Gibbs variational inequality**, arbitrary real `H`, strictly positive
reference weights `p` (no normalisation of `p` needed), competing probability vector `q`
that may have zero coordinates:
`∑ q H - ∑ q log(q/p) ≤ log ∑ p e^H`. -/
theorem gibbs_variational [Nonempty ι] (p q H : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = 1) :
    (∑ i, q i * H i) - (∑ i, q i * Real.log (q i / p i)) ≤
      Real.log (∑ i, p i * Real.exp (H i)) := by
  set Z : ℝ := ∑ i, p i * Real.exp (H i) with hZdef
  have hZ : 0 < Z :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (Real.exp_pos _)) Finset.univ_nonempty
  have he (i : ι) :
      Real.exp (H i + Real.log (p i) - Real.log Z) = p i * Real.exp (H i) / Z := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_log (hp i), Real.exp_log hZ]
    ring
  have hj (i : ι) : q i * H i - q i * Real.log (q i / p i) ≤
      q i * Real.log Z - q i + p i * Real.exp (H i) / Z := by
    have h := young_aux (q i) (H i + Real.log (p i) - Real.log Z) (hq i)
    rw [he] at h
    rw [mul_log_div_aux _ _ (hp i)]
    nlinarith
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hj i)
  have hz : (∑ i, p i * Real.exp (H i) / Z) = 1 := by
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hmass, one_mul, hz, sub_add_cancel] using h

/-- Centered one-sided bound `log E e^Y ≤ E Y^2 / (2 (1 - B/3))` (`d12-spin-eq:onesided`),
for a mean-zero `Y ≤ B < 3` under a strictly positive probability vector. -/
theorem log_expectation_exp_le [Nonempty ι] (p Y : ι → ℝ) {B : ℝ}
    (hp : ∀ i, 0 < p i) (hmass : ∑ i, p i = 1) (hmean : ∑ i, p i * Y i = 0)
    (hB0 : 0 ≤ B) (hB3 : B < 3) (hY : ∀ i, Y i ≤ B) :
    Real.log (∑ i, p i * Real.exp (Y i)) ≤
      (∑ i, p i * Y i ^ 2) / (2 * (1 - B / 3)) := by
  have hZ : 0 < ∑ i, p i * Real.exp (Y i) :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (Real.exp_pos _)) Finset.univ_nonempty
  have hpt (i : ι) : p i * Real.exp (Y i) ≤
      p i + p i * Y i + p i * Y i ^ 2 / (2 * (1 - B / 3)) := by
    have h := mul_le_mul_of_nonneg_left (exp_le_one_sided hB0 hB3 (hY i)) (hp i).le
    calc p i * Real.exp (Y i) ≤ p i * (1 + Y i + Y i ^ 2 / (2 * (1 - B / 3))) := h
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpt i)
  have hZ1 : (∑ i, p i * Real.exp (Y i)) ≤
      1 + (∑ i, p i * Y i ^ 2) / (2 * (1 - B / 3)) := by
    simpa only [Finset.sum_add_distrib, ← Finset.sum_div, hmass, hmean, add_zero] using hsum
  have hlog := Real.log_le_sub_one_of_pos hZ
  linarith

/-- The exact use in Lemma 5.20: `Y = -5e`, `e ≥ -1/4` (only a one-sided hypothesis), `B = 5/4`.
`(1/5) log E e^{-5e} ≤ (30/7) E e^2`. -/
theorem scaled_log_mgf_le [Nonempty ι] (p e : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hmass : ∑ i, p i = 1) (hmean : ∑ i, p i * e i = 0)
    (he : ∀ i, -(1 / 4 : ℝ) ≤ e i) :
    (1 / 5 : ℝ) * Real.log (∑ i, p i * Real.exp (-5 * e i)) ≤
      (30 / 7 : ℝ) * ∑ i, p i * e i ^ 2 := by
  have hmean' : ∑ i, p i * (-5 * e i) = 0 := by
    have : ∑ i, p i * (-5 * e i) = -5 * ∑ i, p i * e i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hmean]; ring
  have h := log_expectation_exp_le p (fun i => -5 * e i) (B := 5 / 4) hp hmass hmean'
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

end BecknerOnofri.V2.FiniteState
