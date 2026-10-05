module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The common tail for dimensions 3 through 10

This module checks the eight rational comparisons in `eq:delta-common` of
the manuscript, and proves the real logarithmic estimate giving its uniform
large-index margin.  The analytic estimate `eq:delta-tail` is an explicit
hypothesis of the transfer theorem: it is not asserted as an axiom here.
The finite harmonic expressions below are the manuscript's evaluated
integer/half-integer psi combinations, not a new definition of digamma.
-/

namespace Legacy.BecknerOnofri.UniformTail

open Finset

/-- The finite harmonic sum H_m, computed in the rationals. -/
def harmonicQ (m : ℕ) : ℚ := ∑ j ∈ range m, 1 / (j + 1 : ℚ)

/-- The odd-denominator harmonic sum appearing at half-integers. -/
def oddHarmonicQ (m : ℕ) : ℚ := ∑ j ∈ range m, 1 / (2 * j + 1 : ℚ)

/-- Rational lower enclosure of psi(d/2)+2 gamma+2/d. -/
def psiCombinationLowerQ (d : ℕ) : ℚ :=
  if d % 2 = 0 then 5772 / 10000 + harmonicQ (d / 2)
  else 5772 / 10000 - 2 * (693148 / 1000000) +
    2 * oddHarmonicQ (d / 2) + 2 / d

/-- The exact rational lower enclosure of Delta_d used in the manuscript. -/
def deltaLowerQ (d : ℕ) : ℚ :=
  d * (psiCombinationLowerQ d - 1144731 / 1000000 - d / 10 * (41 / 25))

def tailWeightQ (d : ℕ) : ℚ := d * max ((d : ℚ) / 2) 2

/-- All eight numerical checks are kernel-checked rational inequalities. -/
theorem rational_delta_margin (d : ℕ) (hd3 : 3 ≤ d) (hd10 : d ≤ 10) :
    (3 / 200 : ℚ) * tailWeightQ d < deltaLowerQ d := by
  interval_cases d <;>
    norm_num [deltaLowerQ, psiCombinationLowerQ, tailWeightQ,
      harmonicQ, oddHarmonicQ, sum_range_succ]

noncomputable def tailWeight (d : ℕ) : ℝ := d * max ((d : ℝ) / 2) 2

/-- Evaluated psi combination, with gamma and log(2) supplied explicitly. -/
noncomputable def psiCombination (d : ℕ) (gamma logTwo : ℝ) : ℝ :=
  if d % 2 = 0 then gamma + (harmonicQ (d / 2) : ℝ)
  else gamma - 2 * logTwo + 2 * (oddHarmonicQ (d / 2) : ℝ) + 2 / d

noncomputable def delta (d : ℕ) (gamma logPi logTwo J : ℝ) : ℝ :=
  d * (psiCombination d gamma logTwo - logPi - J)

/-- Substitute the three certified scalar constants and the theta-integral
bound. No assertion about the analytic origin of these constants is hidden. -/
theorem delta_gt_common (d : ℕ) (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (gamma logPi logTwo J : ℝ)
    (hgamma : (5772 / 10000 : ℝ) < gamma)
    (hlogPi : logPi < 1144731 / 1000000)
    (hlogTwo : logTwo < 693148 / 1000000)
    (hJ : J ≤ (d : ℝ) / 10 * (41 / 25)) :
    (3 / 200 : ℝ) * tailWeight d < delta d gamma logPi logTwo J := by
  interval_cases d <;>
    norm_num [delta, psiCombination, tailWeight, harmonicQ, oddHarmonicQ,
      sum_range_succ] at * <;> linarith

/-- The dominated d-dimensional integral inherits the common bound. -/
theorem delta_gt_common_of_domination (d : ℕ) (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (gamma logPi logTwo J J10 : ℝ)
    (hgamma : (5772 / 10000 : ℝ) < gamma)
    (hlogPi : logPi < 1144731 / 1000000)
    (hlogTwo : logTwo < 693148 / 1000000)
    (hdom : J ≤ (d : ℝ) / 10 * J10) (hJ10 : J10 < 41 / 25) :
    (3 / 200 : ℝ) * tailWeight d < delta d gamma logPi logTwo J := by
  apply delta_gt_common d hd3 hd10 gamma logPi logTwo J hgamma hlogPi hlogTwo
  exact hdom.trans (mul_le_mul_of_nonneg_left hJ10.le (by positivity))

theorem log_two_upper : Real.log 2 < (693148 / 1000000 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
  have h := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 693148 / 1000000) 10
  norm_num [sum_range_succ] at h
  linarith

theorem log_pi_upper : Real.log Real.pi < (1144731 / 1000000 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp Real.pi_pos).2
  have h := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 1144731 / 1000000) 12
  norm_num [sum_range_succ] at h
  linarith [Real.pi_lt_d6]

theorem inverse_pi_upper : 1 / Real.pi < (8 / 25 : ℝ) := by
  apply (div_lt_iff₀ Real.pi_pos).2
  nlinarith [Real.pi_gt_d2]

theorem tailWeight_ge_six (d : ℕ) (hd3 : 3 ≤ d) : 6 ≤ tailWeight d := by
  have hd : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  have hm : (2 : ℝ) ≤ max ((d : ℝ) / 2) 2 := le_max_right _ _
  unfold tailWeight
  nlinarith

/-- The elementary strict logarithm estimate in the common-tail argument. -/
theorem log_one_add_inv_lt (n : ℕ) (hn : 0 < n) :
    Real.log (1 + 1 / (n : ℝ)) < 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi : 0 < 1 / (n : ℝ) := by positivity
  have h := Real.log_lt_sub_one_of_pos (x := 1 + 1 / (n : ℝ))
    (by positivity) (by linarith)
  linarith

/-- The exact rational remainder at every integer n at least 22. -/
theorem tail_remainder_ge (n : ℕ) (hn : 22 ≤ n) :
    (1 / 2200 : ℝ) ≤ 3 / 200 - 8 / (25 * (n : ℝ)) := by
  have hn' : (22 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 25 * n := by positivity
  have hb : 8 / (25 * (n : ℝ)) ≤ (8 / 550 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  linarith

/-- The logarithmic error is strictly smaller than the rational enclosure. -/
theorem logarithmic_error_lt (d n : ℕ) (hd3 : 3 ≤ d) (hn : 0 < n) :
    tailWeight d / Real.pi * Real.log (1 + 1 / (n : ℝ)) <
      tailWeight d * (8 / (25 * (n : ℝ))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hw : 0 < tailWeight d := lt_of_lt_of_le (by norm_num) (tailWeight_ge_six d hd3)
  have hlog := log_one_add_inv_lt n hn
  have hp := inverse_pi_upper
  calc
    tailWeight d / Real.pi * Real.log (1 + 1 / (n : ℝ))
        < tailWeight d / Real.pi * (1 / (n : ℝ)) :=
      mul_lt_mul_of_pos_left hlog (div_pos hw Real.pi_pos)
    _ < tailWeight d * (8 / 25) * (1 / (n : ℝ)) := by
      apply mul_lt_mul_of_pos_right _ (by positivity)
      simpa only [div_eq_mul_inv, one_mul] using mul_lt_mul_of_pos_left hp hw
    _ = tailWeight d * (8 / (25 * (n : ℝ))) := by ring

/-- Transfer from precisely the analytic lower estimate `eq:delta-tail`.
`gap` may be instantiated by d H_n - lambda_d G_{d,n}; proving that
instantiation satisfies `hgap` is a separate analytic obligation. -/
theorem uniform_large_gap (d n : ℕ) (hd3 : 3 ≤ d) (hn : 22 ≤ n)
    (Delta gap : ℝ)
    (hDelta : (3 / 200 : ℝ) * tailWeight d < Delta)
    (hgap : Delta - tailWeight d / Real.pi * Real.log (1 + 1 / (n : ℝ)) ≤ gap) :
    (3 / 1100 : ℝ) < gap := by
  have hn0 : 0 < n := by omega
  have hw := tailWeight_ge_six d hd3
  have he := logarithmic_error_lt d n hd3 hn0
  have hr := mul_le_mul_of_nonneg_left (tail_remainder_ge n hn) (by linarith : 0 ≤ tailWeight d)
  nlinarith

/-- Complete common-tail transfer after substituting the evaluated constants
and the one-integral domination. All remaining analytic premises are visible. -/
theorem uniform_large_gap_of_domination (d n : ℕ)
    (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (hn : 22 ≤ n)
    (gamma logPi logTwo J J10 gap : ℝ)
    (hgamma : (5772 / 10000 : ℝ) < gamma)
    (hlogPi : logPi < 1144731 / 1000000)
    (hlogTwo : logTwo < 693148 / 1000000)
    (hdom : J ≤ (d : ℝ) / 10 * J10) (hJ10 : J10 < 41 / 25)
    (hgap : delta d gamma logPi logTwo J -
      tailWeight d / Real.pi * Real.log (1 + 1 / (n : ℝ)) ≤ gap) :
    (3 / 1100 : ℝ) < gap := by
  exact uniform_large_gap d n hd3 hn _ gap
    (delta_gt_common_of_domination d hd3 hd10 gamma logPi logTwo J J10
      hgamma hlogPi hlogTwo hdom hJ10) hgap

/-- The same transfer with the actual real logarithms. Their rational upper
enclosures are proved in this file from finite exponential Taylor sums. -/
theorem uniform_large_gap_of_real_constants (d n : ℕ)
    (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (hn : 22 ≤ n)
    (gamma J J10 gap : ℝ)
    (hgamma : (5772 / 10000 : ℝ) < gamma)
    (hdom : J ≤ (d : ℝ) / 10 * J10) (hJ10 : J10 < 41 / 25)
    (hgap : delta d gamma (Real.log Real.pi) (Real.log 2) J -
      tailWeight d / Real.pi * Real.log (1 + 1 / (n : ℝ)) ≤ gap) :
    (3 / 1100 : ℝ) < gap := by
  exact uniform_large_gap_of_domination d n hd3 hd10 hn gamma
    (Real.log Real.pi) (Real.log 2) J J10 gap hgamma log_pi_upper
    log_two_upper hdom hJ10 hgap

/-- Interface for the manuscript's unevaluated psi value. To apply this to
digamma, supply its finite integer/half-integer evaluation `hpsi`, as well as
the actual theta-integral and Gaussian-tail estimates. -/
theorem uniform_large_gap_from_psi (d n : ℕ)
    (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (hn : 22 ≤ n)
    (psi gamma J J10 gap : ℝ)
    (hgamma : (5772 / 10000 : ℝ) < gamma)
    (hpsi : psi + 2 * gamma + 2 / (d : ℝ) =
      psiCombination d gamma (Real.log 2))
    (hdom : J ≤ (d : ℝ) / 10 * J10) (hJ10 : J10 < 41 / 25)
    (hgap : (d : ℝ) * (psi + 2 * gamma + 2 / (d : ℝ) - Real.log Real.pi - J) -
      tailWeight d / Real.pi * Real.log (1 + 1 / (n : ℝ)) ≤ gap) :
    (3 / 1100 : ℝ) < gap := by
  apply uniform_large_gap_of_real_constants d n hd3 hd10 hn gamma J J10 gap
    hgamma hdom hJ10
  simpa only [delta, hpsi] using hgap

end Legacy.BecknerOnofri.UniformTail

#print axioms Legacy.BecknerOnofri.UniformTail.rational_delta_margin
#print axioms Legacy.BecknerOnofri.UniformTail.log_two_upper
#print axioms Legacy.BecknerOnofri.UniformTail.log_pi_upper
#print axioms Legacy.BecknerOnofri.UniformTail.uniform_large_gap_from_psi
