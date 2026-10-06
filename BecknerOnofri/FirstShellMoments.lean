module

public import BecknerOnofri.LocalFirstShell
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Exact Haar moments of the first shell, including absence of cubic resonance
and the unslaved fourth cumulant used in the Lyapunov--Schmidt calculation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim

theorem circle_doubleCosine_complex (x : UnitAddCircle) :
    ((2 * circleCosine x : ℝ) : ℂ) = fourier 1 x + fourier (-1) x := by
  rw [fourier_neg, Complex.add_conj]
  simp [circleCosine]

theorem circle_doubleCosine_pow_integral (n : ℕ) :
    ((∫ x : UnitAddCircle, (2 * circleCosine x) ^ n ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * (if (j : ℤ) - ((n - j : ℕ) : ℤ) = 0 then 1 else 0) := by
  rw [← integral_complex_ofReal]
  simp_rw [Complex.ofReal_pow, circle_doubleCosine_complex, add_pow]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    have he (x : UnitAddCircle) :
        (fourier 1 x) ^ j * (fourier (-1) x) ^ (n - j) * (n.choose j : ℂ) =
          (n.choose j : ℂ) * fourier ((j : ℤ) - ((n - j : ℕ) : ℤ)) x := by
      rw [← circle_fourier_nat_mul 1 j, ← circle_fourier_nat_mul (-1) (n-j)]
      simp only [mul_one, mul_neg_one]
      rw [← fourier_add]
      rw [sub_eq_add_neg]
      ring
    simp_rw [he]
    rw [integral_const_mul, circle_fourier_integral]
  · intro j hj
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _

theorem circle_doubleCosine_moments :
    (∫ x : UnitAddCircle, (2 * circleCosine x) ∂AddCircle.haarAddCircle) = 0 ∧
    (∫ x : UnitAddCircle, (2 * circleCosine x) ^ 2 ∂AddCircle.haarAddCircle) = 2 ∧
    (∫ x : UnitAddCircle, (2 * circleCosine x) ^ 3 ∂AddCircle.haarAddCircle) = 0 ∧
    (∫ x : UnitAddCircle, (2 * circleCosine x) ^ 4 ∂AddCircle.haarAddCircle) = 6 := by
  have h1 := circle_doubleCosine_pow_integral 1
  have h2 := circle_doubleCosine_pow_integral 2
  have h3 := circle_doubleCosine_pow_integral 3
  have h4 := circle_doubleCosine_pow_integral 4
  norm_num [Finset.sum_range_succ, Nat.choose] at h1 h2 h3 h4
  exact ⟨by exact_mod_cast h1, by simpa using congrArg Complex.re h2, by exact_mod_cast h3, by simpa using congrArg Complex.re h4⟩

def circleMoment (n : ℕ) : ℝ :=
  ∫ x : UnitAddCircle, (2 * circleCosine x) ^ n ∂AddCircle.haarAddCircle

def firstShellMoment {d : ℕ} (t : Fin d → ℝ) (n : ℕ) : ℝ :=
  ∫ x, firstShellPotential t x ^ n ∂torusMeasure d

@[simp] theorem circleMoment_zero : circleMoment 0 = 1 := by simp [circleMoment]
@[simp] theorem circleMoment_one : circleMoment 1 = 0 := by
  simpa [circleMoment] using circle_doubleCosine_moments.1
@[simp] theorem circleMoment_two : circleMoment 2 = 2 := circle_doubleCosine_moments.2.1
@[simp] theorem circleMoment_three : circleMoment 3 = 0 := circle_doubleCosine_moments.2.2.1
@[simp] theorem circleMoment_four : circleMoment 4 = 6 := circle_doubleCosine_moments.2.2.2
@[simp] theorem firstShellMoment_zero {d : ℕ} (t : Fin d → ℝ) : firstShellMoment t 0 = 1 := by
  simp [firstShellMoment]

theorem firstShellMoment_succ {d : ℕ} (t : Fin (d+1) → ℝ) (p : ℕ) :
    firstShellMoment t p = ∑ j ∈ Finset.range (p+1),
      t 0 ^ j * circleMoment j * firstShellMoment (fun i => t i.succ) (p-j) * (p.choose j : ℝ) := by
  have hsplit : firstShellMoment t p =
      ∫ x : UnitAddCircle × Torus d,
        (t 0 * (2 * circleCosine x.1) + firstShellPotential (fun i => t i.succ) x.2) ^ p
          ∂AddCircle.haarAddCircle.prod (torusMeasure d) := by
    unfold firstShellMoment torusMeasure
    rw [← ((measurePreserving_piFinSuccAbove
      (fun _ : Fin (d+1) => AddCircle.haarAddCircle) 0).symm).integral_comp']
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      firstShellPotential, Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk,
      Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    congr 1
    funext x
    congr 1
    ring
  rw [hsplit]
  simp_rw [add_pow]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    simp_rw [mul_pow]
    rw [integral_mul_const]
    have hi : (∫ x : UnitAddCircle × Torus d,
        (t 0 ^ j * (2 * circleCosine x.1) ^ j) * firstShellPotential (fun i => t i.succ) x.2 ^ (p-j)
          ∂AddCircle.haarAddCircle.prod (torusMeasure d)) =
        t 0 ^ j * circleMoment j * firstShellMoment (fun i => t i.succ) (p-j) := by
      have hprod := integral_prod_mul
        (fun x : UnitAddCircle => t 0 ^ j * (2 * circleCosine x) ^ j)
        (fun x : Torus d => firstShellPotential (fun i => t i.succ) x ^ (p-j))
        (μ := AddCircle.haarAddCircle) (ν := torusMeasure d)
      rw [hprod, integral_const_mul]
      rfl
    simpa only [mul_pow] using congrArg (fun z : ℝ => z * (p.choose j : ℝ)) hi
  · intro j hj
    apply Continuous.integrable_of_hasCompactSupport
    · unfold firstShellPotential circleCosine
      fun_prop
    · exact HasCompactSupport.of_compactSpace _

theorem firstShell_moments (d : ℕ) (t : Fin d → ℝ) :
    firstShellMoment t 1 = 0 ∧
    firstShellMoment t 2 = 2 * ∑ i, t i ^ 2 ∧
    firstShellMoment t 3 = 0 ∧
    firstShellMoment t 4 = 12 * (∑ i, t i ^ 2) ^ 2 - 6 * ∑ i, t i ^ 4 := by
  induction d with
  | zero => simp [firstShellMoment, firstShellPotential]
  | succ d ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (fun i => t i.succ)
    constructor
    · rw [firstShellMoment_succ]
      norm_num [Finset.sum_range_succ, Nat.choose, h1]
    constructor
    · rw [firstShellMoment_succ]
      norm_num [Finset.sum_range_succ, Nat.choose, h1, h2, Fin.sum_univ_succ]
      ring
    constructor
    · rw [firstShellMoment_succ]
      norm_num [Finset.sum_range_succ, Nat.choose, h1, h2, h3]
    · rw [firstShellMoment_succ]
      norm_num [Finset.sum_range_succ, Nat.choose, h1, h2, h3, h4, Fin.sum_univ_succ]
      ring

theorem firstShell_no_cubic_resonance {d : ℕ} (t : Fin d → ℝ) :
    (∫ x, firstShellPotential t x ^ 3 ∂torusMeasure d) = 0 := (firstShell_moments d t).2.2.1

theorem firstShell_fourth_cumulant {d : ℕ} (t : Fin d → ℝ) :
    (1/24:ℝ) * (∫ x, firstShellPotential t x ^ 4 ∂torusMeasure d) -
      (1/8:ℝ) * (∫ x, firstShellPotential t x ^ 2 ∂torusMeasure d) ^ 2 =
        -(1/4:ℝ) * ∑ i, t i ^ 4 := by
  change (1/24:ℝ) * firstShellMoment t 4 - (1/8:ℝ) * firstShellMoment t 2 ^ 2 = _
  rw [(firstShell_moments d t).2.2.2, (firstShell_moments d t).2.1]
  ring

#print axioms circle_doubleCosine_moments
#print axioms firstShell_no_cubic_resonance
#print axioms firstShell_fourth_cumulant
end BecknerOnofri.HighDim
