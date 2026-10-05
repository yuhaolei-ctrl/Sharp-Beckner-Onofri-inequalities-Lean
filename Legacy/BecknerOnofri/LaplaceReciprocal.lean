module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Convert

@[expose] public section

/-!
A rational upper bound for the Laplace integral of a reciprocal affine
function. This supplies an alternative analytic certificate for the scalar
integral estimate; it is independent of numerical quadrature and does not
modify the manuscript or assert the complete torus endpoint theorem.
-/

open MeasureTheory Set

namespace Legacy.BecknerOnofri.LaplaceReciprocal

noncomputable def denominator (A : ℝ) : ℝ := A ^ 2 + 6 * A + 6

noncomputable def polynomial (A v : ℝ) : ℝ :=
  v ^ 4 - (A + 12) * v ^ 3 + (A ^ 2 + 12 * A + 48) * v ^ 2 -
    (A ^ 3 + 12 * A ^ 2 + 48 * A + 72) * v +
    (A ^ 4 + 12 * A ^ 3 + 48 * A ^ 2 + 72 * A + 36)

theorem denominator_pos {A : ℝ} (hA : 0 < A) : 0 < denominator A := by
  unfold denominator
  positivity

/-- Exact algebraic remainder; the remainder being subtracted is nonnegative
on the positive integration half-line. -/
theorem reciprocal_identity {A v : ℝ} (hA : 0 < A) (hv : 0 ≤ v) :
    1 / (A + v) = polynomial A v / (A * denominator A ^ 2) -
      v * (v ^ 2 - 6 * v + 6) ^ 2 /
        (A * denominator A ^ 2 * (A + v)) := by
  have hAv : A + v ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hA hv)
  have hC := (denominator_pos hA).ne'
  unfold polynomial denominator at *
  field_simp [hA.ne', hAv, hC]
  ring

theorem reciprocal_upper {A v : ℝ} (hA : 0 < A) (hv : 0 ≤ v) :
    1 / (A + v) ≤ polynomial A v / (A * denominator A ^ 2) := by
  rw [reciprocal_identity hA hv]
  apply sub_le_self
  exact div_nonneg (mul_nonneg hv (sq_nonneg _))
    (mul_nonneg (mul_nonneg hA.le (sq_nonneg _)) (add_nonneg hA.le hv))

theorem reciprocal_integrable {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun v : ℝ => Real.exp (-v) / (A + v)) (Ioi 0) := by
  have hm : Measurable (fun v : ℝ => Real.exp (-v) / (A + v)) := by
    fun_prop
  apply ((integrableOn_exp_neg_Ioi 0).div_const A).mono'
    hm.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
  have hv0 : 0 ≤ v := le_of_lt hv
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le (add_nonneg hA.le hv0))]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hA (le_add_of_nonneg_right hv0)

theorem moment_integral (n : ℕ) :
    (∫ v : ℝ in Ioi 0, v ^ n * Real.exp (-v)) = (n.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := 1) (by positivity) (by norm_num)
  simpa [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using h

theorem moment_integrable (n : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ n * Real.exp (-v)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [moment_integral]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

theorem weighted_polynomial_expansion (A : ℝ) :
    (fun v : ℝ => polynomial A v * Real.exp (-v)) =
      (fun v : ℝ =>
        (v ^ 4 * Real.exp (-v) - (A + 12) * (v ^ 3 * Real.exp (-v)) +
          (A ^ 2 + 12 * A + 48) * (v ^ 2 * Real.exp (-v)) -
          (A ^ 3 + 12 * A ^ 2 + 48 * A + 72) * (v ^ 1 * Real.exp (-v))) +
          (A ^ 4 + 12 * A ^ 3 + 48 * A ^ 2 + 72 * A + 36) *
            (v ^ 0 * Real.exp (-v))) := by
  funext v
  unfold polynomial
  ring

theorem polynomial_integrable (A : ℝ) :
    IntegrableOn (fun v : ℝ => polynomial A v * Real.exp (-v)) (Ioi 0) := by
  rw [weighted_polynomial_expansion]
  exact ((((moment_integrable 4).sub ((moment_integrable 3).const_mul _)).add
    ((moment_integrable 2).const_mul _)).sub ((moment_integrable 1).const_mul _)).add
      ((moment_integrable 0).const_mul _)

theorem polynomial_integral (A : ℝ) :
    (∫ v : ℝ in Ioi 0, polynomial A v * Real.exp (-v)) =
      (A ^ 2 + 5 * A + 2) * denominator A := by
  rw [weighted_polynomial_expansion]
  have h4 := moment_integrable 4
  have h3 := (moment_integrable 3).const_mul (A + 12)
  have h2 := (moment_integrable 2).const_mul (A ^ 2 + 12 * A + 48)
  have h1 := (moment_integrable 1).const_mul (A ^ 3 + 12 * A ^ 2 + 48 * A + 72)
  have h0 := (moment_integrable 0).const_mul
    (A ^ 4 + 12 * A ^ 3 + 48 * A ^ 2 + 72 * A + 36)
  have h43 : IntegrableOn (fun v : ℝ =>
      v ^ 4 * Real.exp (-v) - (A + 12) * (v ^ 3 * Real.exp (-v))) (Ioi 0) :=
    h4.sub h3
  have h432 : IntegrableOn (fun v : ℝ =>
      v ^ 4 * Real.exp (-v) - (A + 12) * (v ^ 3 * Real.exp (-v)) +
        (A ^ 2 + 12 * A + 48) * (v ^ 2 * Real.exp (-v))) (Ioi 0) :=
    h43.add h2
  have h4321 : IntegrableOn (fun v : ℝ =>
      v ^ 4 * Real.exp (-v) - (A + 12) * (v ^ 3 * Real.exp (-v)) +
        (A ^ 2 + 12 * A + 48) * (v ^ 2 * Real.exp (-v)) -
        (A ^ 3 + 12 * A ^ 2 + 48 * A + 72) * (v ^ 1 * Real.exp (-v))) (Ioi 0) :=
    h432.sub h1
  rw [integral_add h4321 h0, integral_sub h432 h1,
    integral_add h43 h2, integral_sub h4 h3]
  simp only [integral_const_mul, moment_integral]
  norm_num [Nat.factorial, denominator]
  ring

/-- A proved rational majorant for the actual improper integral. All
integrability claims are established independently of the inequality. -/
theorem integral_upper {A : ℝ} (hA : 0 < A) :
    (∫ v : ℝ in Ioi 0, Real.exp (-v) / (A + v)) ≤
      (A ^ 2 + 5 * A + 2) / (A * (A ^ 2 + 6 * A + 6)) := by
  have hp := (polynomial_integrable A).div_const (A * denominator A ^ 2)
  calc
    _ ≤ ∫ v : ℝ in Ioi 0,
        (polynomial A v * Real.exp (-v)) / (A * denominator A ^ 2) := by
      apply integral_mono_ae (reciprocal_integrable hA) hp
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have h := mul_le_mul_of_nonneg_left (reciprocal_upper hA (le_of_lt hv))
        (Real.exp_pos (-v)).le
      convert h using 1 <;> first | rfl | ring
    _ = _ := by
      rw [integral_div, polynomial_integral]
      have hC := (denominator_pos hA).ne'
      change ((A ^ 2 + 5 * A + 2) * denominator A) /
        (A * denominator A ^ 2) = (A ^ 2 + 5 * A + 2) / (A * denominator A)
      field_simp [hA.ne', hC]

end Legacy.BecknerOnofri.LaplaceReciprocal
