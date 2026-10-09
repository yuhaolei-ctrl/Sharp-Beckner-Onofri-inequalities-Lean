module

public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import BecknerOnofri.SpinProductDefinitions
public import BecknerOnofri.V2.Circle.ScalarBernstein

@[expose] public section

/-! # Power series of `I_B` and the base expansion of Lemma 5.16 (`d12-circle-eq:baseexpand`)

* `binaryCost_hasSum`: `2 I_B(t) = sum_{k>=0} (t^2)^(k+1)/((k+1)(2k+1))` for `|t| < 1`
  (`I_B = Spin.binaryCost`, `eq:section5-binary-entropy`).
* `Iminus`: `I_-(t) = 29/48 u + 5/96 u^2 + u^3/144 - 19/48 log(1-u)`, `u = t^2`
  (`d12-circle-eq:Iminus`).
* `baseexpand_hasSum`: the printed expansion
  `((1-c) I_- + c u - 2 I_B)/u^2 = -41/480 - 31/1440 u + (247/7680 - 1/28) u^2
   + sum_{k>=5} (1/k)(247/1920 - 1/(2k-1)) u^(k-2)`, `c = 27/40`, as a `HasSum`.
* `base_ge_J`: with `J` the `k = 12` truncation, `(1-c) I_- + c u - 2 I_B >= u^2 J(u)`; this is
  the product form, valid also at `t = 0` (no division by `u^2`).  The first three coefficients
  are kept verbatim (they are not all nonnegative); only the terms `k >= 5` are dropped by sign. -/
noncomputable section
open BecknerOnofri.HighDim
namespace BecknerOnofri.V2.Circle

/-- Power series of the binary entropy cost:
`2 I_B(t) = ∑_{k ≥ 0} (t²)^(k+1) / ((k+1)(2k+1))`, `|t| < 1`. -/
theorem binaryCost_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (fun k : ℕ => (t ^ 2) ^ (k + 1) / ((k + 1) * (2 * k + 1))) (2 * Spin.binaryCost t) := by
  have ht2 : |t ^ 2| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg t) ht (by norm_num)
  have h1 := Real.hasSum_log_sub_log_of_abs_lt_one ht
  have h2 := Real.hasSum_pow_div_log_of_abs_lt_one ht2
  have h3 := (h1.mul_left t).sub h2
  have hlog : Real.log (1 - t ^ 2) = Real.log (1 + t) + Real.log (1 - t) := by
    have a : 1 + t ≠ 0 := by have := (abs_lt.mp ht).1; linarith
    have b : 1 - t ≠ 0 := by have := (abs_lt.mp ht).2; linarith
    rw [← Real.log_mul a b]; congr 1; ring
  have hval : t * (Real.log (1 + t) - Real.log (1 - t)) - -Real.log (1 - t ^ 2) =
      2 * Spin.binaryCost t := by
    rw [hlog]; unfold Spin.binaryCost; ring
  rw [hval] at h3
  convert h3 using 1
  funext k
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (2 * k + 1 : ℝ) ≠ 0 := by positivity
  rw [← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ t (2 * k + 1)]
  field_simp
  ring

/-- The Cramer minorant `I_-` of Lemma 5.15 (`d12-circle-eq:Iminus`), `u = t²`. -/
noncomputable def Iminus (t : ℝ) : ℝ :=
  29 / 48 * t ^ 2 + 5 / 96 * (t ^ 2) ^ 2 + 1 / 144 * (t ^ 2) ^ 3 - 19 / 48 * Real.log (1 - t ^ 2)

/-- The left side of `d12-circle-eq:baseexpand` before division by `u²`:
`(1-c) I_-(t) + c u - 2 I_B(t)` with `c = 27/40`. -/
noncomputable def baseLHS (t : ℝ) : ℝ :=
  (1 - 27 / 40) * Iminus t + 27 / 40 * t ^ 2 - 2 * Spin.binaryCost t

/-- the general term `(1/n)(247/1920 - 1/(2n-1)) u^n`, `n = k+1`. -/
noncomputable def hterm (u : ℝ) (k : ℕ) : ℝ :=
  u ^ (k + 1) / (k + 1) * (247 / 1920 - 1 / (2 * (k + 1) - 1))

theorem hterm_nonneg {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 4 ≤ k) : 0 ≤ hterm u k := by
  unfold hterm
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  apply mul_nonneg (div_nonneg (pow_nonneg hu _) (by positivity))
  have : 1 / (2 * ((k : ℝ) + 1) - 1) ≤ 1 / 9 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  linarith

theorem baseLHS_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (hterm (t ^ 2)) (baseLHS t - (13 / 40 * (29 / 48 * t ^ 2 + 5 / 96 * (t ^ 2) ^ 2 + 1 / 144 * (t ^ 2) ^ 3)
      + 27 / 40 * t ^ 2)) := by
  have ht2 : |t ^ 2| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg t) ht (by norm_num)
  have h2 := (Real.hasSum_pow_div_log_of_abs_lt_one ht2).mul_left (247 / 1920)
  have h3 := h2.sub (binaryCost_hasSum ht)
  convert h3 using 1
  · funext k
    unfold hterm
    have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (2 * ((k : ℝ) + 1) - 1) ≠ 0 := by
      have : (0:ℝ) < 2 * ((k : ℝ) + 1) - 1 := by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
      exact this.ne'
    have h2' : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have e : (2 * ((k : ℝ) + 1) - 1) = 2 * k + 1 := by ring
    rw [e]
    field_simp
  · unfold baseLHS Iminus
    ring

theorem poly_part_twelve (u : ℝ) :
    13 / 40 * (29 / 48 * u + 5 / 96 * u ^ 2 + 1 / 144 * u ^ 3) + 27 / 40 * u +
      ∑ k ∈ Finset.range 12, hterm u k = u ^ 2 * J u := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hterm, J, tailTerm]
  push_cast
  ring

theorem poly_part_four (u : ℝ) :
    13 / 40 * (29 / 48 * u + 5 / 96 * u ^ 2 + 1 / 144 * u ^ 3) + 27 / 40 * u +
      ∑ k ∈ Finset.range 4, hterm u k =
      u ^ 2 * (-(41 / 480) - 31 / 1440 * u + (247 / 7680 - 1 / 28) * u ^ 2) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hterm]
  push_cast
  ring

/-- `d12-circle-eq:baseexpand`, multiplied out: for `|t| < 1`, `u = t²`,
`(1-c) I_-(t) + c u - 2 I_B(t) ≥ u² J(u)`, where `J` is the `k = 12` truncation. -/
theorem base_ge_J {t : ℝ} (ht : |t| < 1) : (t ^ 2) ^ 2 * J (t ^ 2) ≤ baseLHS t := by
  have hu : 0 ≤ t ^ 2 := sq_nonneg t
  have h := (hasSum_nat_add_iff' 12).mpr (baseLHS_hasSum ht)
  have hnn : 0 ≤ baseLHS t - (13 / 40 * (29 / 48 * t ^ 2 + 5 / 96 * (t ^ 2) ^ 2 + 1 / 144 * (t ^ 2) ^ 3)
      + 27 / 40 * t ^ 2) - ∑ i ∈ Finset.range 12, hterm (t ^ 2) i := by
    apply h.nonneg
    intro n
    exact hterm_nonneg hu (by omega)
  have := poly_part_twelve (t ^ 2)
  linarith

/-- The series expansion `d12-circle-eq:baseexpand` for `0 < |t| < 1`:
`((1-c) I_-(t) + c u - 2 I_B(t))/u² = -41/480 - 31/1440 u + (247/7680 - 1/28) u²
 + ∑_{k ≥ 5} (1/k)(247/1920 - 1/(2k-1)) u^(k-2)`. -/
theorem baseexpand_hasSum {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    HasSum (fun m : ℕ => tailTerm ((m : ℝ) + 5) (t ^ 2) (m + 3))
      (baseLHS t / (t ^ 2) ^ 2 -
        (-(41 / 480) - 31 / 1440 * t ^ 2 + (247 / 7680 - 1 / 28) * (t ^ 2) ^ 2)) := by
  have hu : 0 < t ^ 2 := by positivity
  have h := (hasSum_nat_add_iff' 4).mpr (baseLHS_hasSum ht)
  have h' := h.div_const ((t ^ 2) ^ 2)
  have h4 := poly_part_four (t ^ 2)
  have hne : (t ^ 2) ^ 2 ≠ 0 := by positivity
  convert h' using 1
  · funext m
    unfold hterm tailTerm
    have e1 : (m + 4 + 1 : ℕ) = m + 3 + 2 := by ring
    rw [e1, pow_add]
    push_cast
    have : ((m : ℝ) + 4 + 1) = (m : ℝ) + 5 := by ring
    rw [this]
    have h5 : ((m : ℝ) + 5) ≠ 0 := by positivity
    have h2 : (2 * ((m : ℝ) + 5) - 1) ≠ 0 := by
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      intro h; linarith
    field_simp
    ring
  · field_simp
    have : baseLHS t - (13 / 40 * (29 / 48 * t ^ 2 + 5 / 96 * (t ^ 2) ^ 2 + 1 / 144 * (t ^ 2) ^ 3)
      + 27 / 40 * t ^ 2) - ∑ i ∈ Finset.range 4, hterm (t ^ 2) i = baseLHS t -
        (t ^ 2) ^ 2 * (-(41 / 480) - 31 / 1440 * t ^ 2 + (247 / 7680 - 1 / 28) * (t ^ 2) ^ 2) := by
      linarith
    linarith

end BecknerOnofri.V2.Circle
