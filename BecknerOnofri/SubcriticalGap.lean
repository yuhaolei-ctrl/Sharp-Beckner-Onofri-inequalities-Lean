import BecknerOnofri.Definitions
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
The spectral coupling is strictly below the collapse coupling in every
integer dimension at least twelve.  A two-dimension Gamma recurrence and
the two initial dimensions give an alternative to the manuscript's
one-dimension Gamma-integral comparison.
-/

noncomputable section

namespace BecknerOnofri.HighDim

theorem spectralThreshold_pos {d : ℕ} (hd : 0 < d) :
    0 < spectralThreshold d := by
  unfold spectralThreshold
  apply div_pos
  · positivity
  · apply Real.Gamma_pos_of_pos
    exact div_pos (Nat.cast_pos.mpr hd) (by norm_num)

theorem spectralThreshold_add_two {d : ℕ} (hd : 0 < d) :
    spectralThreshold (d + 2) =
      (2 * Real.pi / (d : ℝ)) * spectralThreshold d := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hg : Real.Gamma ((d : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < d / 2)).ne'
  have he : ((d + 2 : ℕ) : ℝ) / 2 = (d : ℝ) / 2 + 1 := by
    push_cast
    ring
  unfold spectralThreshold
  rw [he, Real.rpow_add Real.pi_pos, Real.rpow_one,
    Real.Gamma_add_one (by positivity : (d : ℝ) / 2 ≠ 0)]
  field_simp

private theorem pi_six_bound : Real.pi ^ 6 < (1000000 : ℝ) / 729 := by
  have hp : Real.pi < (10 : ℝ) / 3 := by linarith [Real.pi_lt_d2]
  have hh : Real.pi ^ 6 < ((10 : ℝ) / 3) ^ 6 := by gcongr
  norm_num at hh
  exact hh

theorem spectralThreshold_twelve : spectralThreshold 12 = Real.pi ^ 6 / 60 := by
  have hg : Real.Gamma 6 = 120 := by
    convert Real.Gamma_nat_eq_factorial 5 using 1 <;> norm_num
  unfold spectralThreshold
  norm_num only [Nat.cast_ofNat, Real.rpow_ofNat]
  rw [hg]
  ring

theorem spectralThreshold_twelve_lt : spectralThreshold 12 < 2 * (12 : ℝ) := by
  rw [spectralThreshold_twelve]
  have hp := pi_six_bound
  nlinarith

theorem spectralThreshold_thirteen :
    spectralThreshold 13 = 128 * Real.pi ^ 6 / 10395 := by
  have hg : Real.Gamma ((13 : ℝ) / 2) = 10395 * Real.sqrt Real.pi / 64 := by
    convert Real.Gamma_nat_add_half 6 using 1 <;> norm_num
  have hp : Real.pi ^ ((13 : ℝ) / 2) = Real.pi ^ (6 : ℕ) * Real.sqrt Real.pi := by
    rw [show (13 : ℝ) / 2 = (6 : ℕ) + (1 / 2 : ℝ) by norm_num,
      Real.rpow_add Real.pi_pos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  unfold spectralThreshold
  norm_num only [Nat.cast_ofNat]
  rw [hg, hp]
  field_simp
  ring

theorem spectralThreshold_thirteen_lt : spectralThreshold 13 < 2 * (13 : ℝ) := by
  rw [spectralThreshold_thirteen]
  have hp := pi_six_bound
  nlinarith

/-- The strict subcritical gap required for minimizer selection, including odd dimensions. -/
theorem spectral_subcritical_gap {d : ℕ} (hd : 12 ≤ d) :
    spectralThreshold d < 2 * (d : ℝ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases h12 : d = 12
      · subst d
        exact spectralThreshold_twelve_lt
      by_cases h13 : d = 13
      · subst d
        exact spectralThreshold_thirteen_lt
      have hm : 12 ≤ d - 2 := by omega
      have hmp : 0 < d - 2 := by omega
      have hprev := ih (d - 2) (by omega) hm
      have hde : d = d - 2 + 2 := by omega
      have hc : (d : ℝ) = (d - 2 : ℕ) + 2 := by exact_mod_cast hde
      have hp : (0 : ℝ) < (d - 2 : ℕ) := Nat.cast_pos.mpr hmp
      have hr : 0 < 2 * Real.pi / (d - 2 : ℕ) := by positivity
      calc
        spectralThreshold d =
            (2 * Real.pi / (d - 2 : ℕ)) * spectralThreshold (d - 2) := by
          conv_lhs => rw [hde]
          exact spectralThreshold_add_two hmp
        _ < (2 * Real.pi / (d - 2 : ℕ)) * (2 * (d - 2 : ℕ)) :=
          mul_lt_mul_of_pos_left hprev hr
        _ = 4 * Real.pi := by field_simp; ring
        _ < 2 * (d : ℝ) := by
          have hd' : (12 : ℝ) ≤ d := by exact_mod_cast hd
          linarith [Real.pi_lt_four]

end BecknerOnofri.HighDim
