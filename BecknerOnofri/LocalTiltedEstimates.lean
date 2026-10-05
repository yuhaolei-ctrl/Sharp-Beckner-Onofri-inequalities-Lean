import BecknerOnofri.LocalFirstShell
import BecknerOnofri.CenteredExponential
import Mathlib.MeasureTheory.Measure.Tilted

/-! Actual tilted probability measures and the bounded higher-mode exponential estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim

lemma firstShell_exp_integrable {d : ℕ} (t : Fin d → ℝ) :
    Integrable (fun x => Real.exp (firstShellPotential t x)) (torusMeasure d) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold firstShellPotential circleCosine
    fun_prop
  · exact HasCompactSupport.of_compactSpace _

lemma firstShell_partition_ge_one {d : ℕ} (t : Fin d → ℝ) :
    1 ≤ ∫ x, Real.exp (firstShellPotential t x) ∂torusMeasure d := by
  rw [firstShell_partition]
  exact Finset.one_le_prod (fun i _ => one_le_besselI0Two (t i))

lemma firstShellPotential_le {d : ℕ} (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i) (x : Torus d) :
    firstShellPotential t x ≤ 2 * ∑ i, t i := by
  unfold firstShellPotential
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hc : circleCosine (x i) ≤ 1 := by
    exact (Complex.re_le_norm _).trans_eq (circle_fourier_norm 1 (x i))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num) (ht i))

lemma firstShellTilt_le_exp {d : ℕ} (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i) (x : Torus d) :
    firstShellTilt t x ≤ Real.exp (2 * ∑ i, t i) := by
  rw [firstShellTilt_eq_exp]
  have hz := firstShell_partition_ge_one t
  have hpos : 0 < ∫ y, Real.exp (firstShellPotential t y) ∂torusMeasure d := zero_lt_one.trans_le hz
  calc
    _ ≤ Real.exp (firstShellPotential t x) :=
      (div_le_self (Real.exp_nonneg _) hz)
    _ ≤ _ := Real.exp_le_exp.mpr (firstShellPotential_le t ht x)

def firstShellTiltMeasure {d : ℕ} (t : Fin d → ℝ) : Measure (Torus d) :=
  (torusMeasure d).tilted (firstShellPotential t)

instance firstShellTiltMeasure_probability {d : ℕ} (t : Fin d → ℝ) :
    IsProbabilityMeasure (firstShellTiltMeasure t) :=
  isProbabilityMeasure_tilted (firstShell_exp_integrable t)

lemma integral_firstShellTiltMeasure {d : ℕ} (t : Fin d → ℝ) (g : Torus d → ℝ) :
    (∫ x, g x ∂firstShellTiltMeasure t) = ∫ x, firstShellTilt t x * g x ∂torusMeasure d := by
  rw [firstShellTiltMeasure, integral_tilted]
  simp only [← firstShellTilt_eq_exp, smul_eq_mul]

lemma firstShellTiltMeasure_variance_bound {d : ℕ} (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i)
    (w : Torus d → ℝ) (B : ℝ) (hw : AEStronglyMeasurable w (torusMeasure d))
    (_hB : 0 ≤ B) (hbound : ∀ᵐ x ∂torusMeasure d, |w x| ≤ B) :
    ProbabilityTheory.variance w (firstShellTiltMeasure t) ≤
      Real.exp (2 * ∑ i, t i) * ∫ x, w x ^ 2 ∂torusMeasure d := by
  have hac : firstShellTiltMeasure t ≪ torusMeasure d := tilted_absolutelyContinuous _ _
  have hwtilt : AEStronglyMeasurable w (firstShellTiltMeasure t) := hw.mono_ac hac
  have hsq := integrable_sq_of_ae_abs_le hw hbound
  have hprod : Integrable (fun x => firstShellTilt t x * w x ^ 2) (torusMeasure d) := by
    apply Integrable.of_bound ((firstShellTilt_integrable t).1.mul (hw.pow 2))
      (Real.exp (2 * ∑ i, t i) * B ^ 2)
    filter_upwards [hbound] with x hx
    change ‖firstShellTilt t x * w x ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (firstShellTilt_pos t x).le (sq_nonneg _))]
    exact mul_le_mul (firstShellTilt_le_exp t ht x)
      (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (w x)) hx 2) (sq_nonneg _) (Real.exp_nonneg _)
  have h := ProbabilityTheory.variance_le_expectation_sq hwtilt
  change ProbabilityTheory.variance w (firstShellTiltMeasure t) ≤
    ∫ x, w x ^ 2 ∂firstShellTiltMeasure t at h
  rw [integral_firstShellTiltMeasure] at h
  refine h.trans ?_
  rw [← integral_const_mul]
  exact integral_mono_ae hprod (hsq.const_mul _)
    (Filter.Eventually.of_forall (fun x => mul_le_mul_of_nonneg_right
      (firstShellTilt_le_exp t ht x) (sq_nonneg _)))

lemma firstShell_add_log_partition_bound {d : ℕ} (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i)
    (w : Torus d → ℝ) (B : ℝ) (hw : AEStronglyMeasurable w (torusMeasure d))
    (hB : 0 ≤ B) (hbound : ∀ᵐ x ∂torusMeasure d, |w x| ≤ B) :
    Real.log (∫ x, Real.exp (firstShellPotential t x + w x) ∂torusMeasure d) ≤
      Real.log (∫ x, Real.exp (firstShellPotential t x) ∂torusMeasure d) +
      (∫ x, firstShellTilt t x * w x ∂torusMeasure d) +
      (Real.exp (2 * ∑ i, t i + 2 * B) / 2) * ∫ x, w x ^ 2 ∂torusMeasure d := by
  have hac : firstShellTiltMeasure t ≪ torusMeasure d := tilted_absolutelyContinuous _ _
  have hwtilt : AEStronglyMeasurable w (firstShellTiltMeasure t) := hw.mono_ac hac
  have hbtilt : ∀ᵐ x ∂firstShellTiltMeasure t, |w x| ≤ B := hac.ae_le hbound
  have hh := centered_exponential_variance_bound (firstShellTiltMeasure t) w B hwtilt hB hbtilt
  have hv := firstShellTiltMeasure_variance_bound t ht w B hw hB hbound
  have he := integral_exp_tilted (μ := torusMeasure d) (firstShellPotential t) w
  change (∫ x, Real.exp (w x) ∂firstShellTiltMeasure t) =
    (∫ x, Real.exp (firstShellPotential t x + w x) ∂torusMeasure d) /
      (∫ x, Real.exp (firstShellPotential t x) ∂torusMeasure d) at he
  have hZpos := integral_exp_pos (firstShell_exp_integrable t)
  have htpos := integral_exp_pos (integrable_exp_of_ae_abs_le hwtilt hbtilt)
  have hsumpos : 0 < ∫ x, Real.exp (firstShellPotential t x + w x) ∂torusMeasure d := by
    have := (div_pos_iff.mp (he ▸ htpos))
    rcases this with h | h
    · exact h.1
    · exact False.elim (not_lt_of_ge hZpos.le h.2)
  rw [he, Real.log_div hsumpos.ne' hZpos.ne', integral_firstShellTiltMeasure] at hh
  have hscale := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ Real.exp (2 * B) / 2)
  rw [Real.exp_add]
  nlinarith

#print axioms firstShell_add_log_partition_bound
end BecknerOnofri.HighDim
