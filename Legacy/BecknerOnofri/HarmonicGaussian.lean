import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Legacy.D10.Binomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The harmonic estimate for the Gaussian parameter

For n at least one, the actual harmonic number and the actual Gaussian
parameter satisfy H_n + log(log(1+1/n)) >= gamma. The proof uses the midpoint
lower bound for a logarithmic increment and a decreasing sequence converging
to the Euler--Mascheroni constant.
-/

namespace Legacy.BecknerOnofri.HarmonicGaussian

open Filter Topology Finset

/-- The first positive term of the atanh expansion gives the midpoint bound. -/
theorem log_step_ge_midpoint (x : ℝ) (hx : 0 < x) :
    1 / (x + 1/2) ≤ Real.log ((x + 1) / x) := by
  have hden : 0 < 2*x + 1 := by positivity
  have ht0 : 0 ≤ 1 / (2*x + 1) := by positivity
  have ht1 : 1 / (2*x + 1) < 1 := by
    apply (div_lt_iff₀ hden).2
    linarith
  have hminus : 1 - 1 / (2*x + 1) ≠ 0 := by linarith
  have h := Real.sum_range_le_log_div ht0 ht1 1
  norm_num only [sum_range_succ, sum_range_zero, mul_zero, zero_add, pow_one,
    Nat.cast_one, div_one] at h
  have harg : (1 + 1 / (2*x + 1)) / (1 - 1 / (2*x + 1)) = (x + 1) / x := by
    field_simp
    ring
  rw [harg] at h
  have hc : 1 / (x + 1/2) = 2 * (1 / (2*x + 1)) := by
    field_simp
  linarith

theorem log_one_add_inv_ge_midpoint (x : ℝ) (hx : 0 < x) :
    1 / (x + 1/2) ≤ Real.log (1 + 1/x) := by
  have harg : (x + 1) / x = 1 + 1/x := by field_simp
  simpa only [harg] using log_step_ge_midpoint x hx

/-- Starting at n+1 avoids a logarithm at zero. -/
noncomputable def midpointSeq (n : ℕ) : ℝ :=
  (harmonic (n+1) : ℝ) - Real.log ((n : ℝ) + 3/2)

theorem midpointSeq_antitone : Antitone midpointSeq := by
  apply antitone_nat_of_succ_le
  intro n
  have hx : (0 : ℝ) < n + 3/2 := by positivity
  have hx1 : (0 : ℝ) < (n + 3/2 : ℝ) + 1 := by positivity
  have hlog := log_step_ge_midpoint ((n : ℝ) + 3/2) hx
  rw [Real.log_div hx1.ne' hx.ne'] at hlog
  have he1 : ((n : ℝ) + 3/2) + 1 = ((n : ℝ) + 1) + 3/2 := by ring
  have he2 : ((n : ℝ) + 3/2) + 1/2 = (n : ℝ) + 1 + 1 := by ring
  rw [he1, he2] at hlog
  simp only [one_div] at hlog
  unfold midpointSeq
  rw [harmonic_succ (n+1)]
  push_cast
  linarith

theorem midpointSeq_tendsto :
    Tendsto midpointSeq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hH := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hR := (Real.tendsto_log_comp_add_sub_log (1/2)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have ht := hH.sub hR
  convert ht using 1
  · funext n
    simp only [midpointSeq, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have he : ((n : ℝ) + 1) + 1/2 = (n : ℝ) + 3/2 := by ring
    rw [he]
    ring
  · simp

theorem gamma_le_midpointSeq (n : ℕ) :
    Real.eulerMascheroniConstant ≤ midpointSeq n :=
  midpointSeq_antitone.le_of_tendsto midpointSeq_tendsto n

/-- The usual harmonic number lies above gamma plus log(n+1/2). -/
theorem harmonic_sub_log_half_ge_gamma (n : ℕ) (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant ≤ (harmonic n : ℝ) - Real.log ((n : ℝ) + 1/2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := gamma_le_midpointSeq m
  simpa only [midpointSeq, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
    show (1 : ℝ) + 1/2 = 3/2 by norm_num, add_assoc] using h

/-- The actual Gaussian parameter is at least the midpoint reciprocal. -/
theorem gaussian_parameter_ge_midpoint (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1/2) ≤ Real.log (1 + 1/(n : ℝ)) := by
  apply log_one_add_inv_ge_midpoint
  exact_mod_cast (show 0 < n by omega)

/-- The logarithm of the Gaussian parameter is controlled with the sharp
Euler constant, with no unproved analytic premise. -/
theorem harmonic_add_log_gaussian_ge_gamma (n : ℕ) (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant ≤
      (harmonic n : ℝ) + Real.log (Real.log (1 + 1/(n : ℝ))) := by
  have hH := harmonic_sub_log_half_ge_gamma n hn
  have hA := gaussian_parameter_ge_midpoint n hn
  have hp : (0 : ℝ) < (n : ℝ) + 1/2 := by positivity
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 1/((n : ℝ) + 1/2)) hA
  rw [Real.log_div (by norm_num) hp.ne', Real.log_one, zero_sub] at hlog
  linarith

/-- The old Legacy.D10 harmonic notation is exactly Mathlib's rational harmonic sum. -/
theorem harmonicNumber_eq_harmonic (n : ℕ) : Legacy.D10.harmonicNumber n = harmonic n := by
  simp only [Legacy.D10.harmonicNumber, harmonic, Nat.cast_add, Nat.cast_one]

theorem harmonicNumber_add_log_gaussian_ge_gamma (n : ℕ) (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant ≤
      (Legacy.D10.harmonicNumber n : ℝ) + Real.log (Real.log (1 + 1/(n : ℝ))) := by
  rw [harmonicNumber_eq_harmonic]
  exact harmonic_add_log_gaussian_ge_gamma n hn

end Legacy.BecknerOnofri.HarmonicGaussian

#print axioms Legacy.BecknerOnofri.HarmonicGaussian.harmonic_add_log_gaussian_ge_gamma
#print axioms Legacy.BecknerOnofri.HarmonicGaussian.harmonicNumber_add_log_gaussian_ge_gamma
