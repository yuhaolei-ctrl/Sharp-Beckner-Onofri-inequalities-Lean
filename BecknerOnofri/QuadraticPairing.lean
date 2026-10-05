import BecknerOnofri.QuadraticCoefficients

/-! Actual Haar pairings of the quadratic source with its finite Fourier modes. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.QuadraticModes
open ContinuousGibbs ContinuousFirstShell

/-- The actual Haar L² pairing of real continuous functions. -/
def pairing {d : ℕ} (f : Space d) : Space d →L[ℝ] ℝ :=
  (mean d).comp (ContinuousLinearMap.mul ℝ (Space d) f)

@[simp] theorem pairing_apply {d : ℕ} (f g : Space d) : pairing f g = mean d (f*g) := rfl

theorem pairing_synthesis {d : ℕ} (f : Space d) (k : Frequency d) (z : ℂ) :
    pairing f (synthesis k z) = 2 * (conj z * coefficient k f).re := by
  rw [pairing_apply, mean_apply]
  have hi : Integrable (fun x : Torus d => z * UnitAddTorus.mFourier k x * (f x : ℂ))
      (torusMeasure d) :=
    ((continuous_const.mul (UnitAddTorus.mFourier k).continuous).mul
      (Complex.continuous_ofReal.comp f.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = 2 * (∫ x, (z * UnitAddTorus.mFourier k x * (f x:ℂ)).re ∂torusMeasure d) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [ContinuousMap.mul_apply, synthesis_apply, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        ring)
    _ = 2 * (∫ x, z * UnitAddTorus.mFourier k x * (f x:ℂ) ∂torusMeasure d).re := by
      exact congrArg (fun r : ℝ => 2*r) (integral_re hi)
    _ = 2 * (z * coefficient (-k) f).re := by
      rw [coefficient_integral]
      simp only [neg_neg, ← integral_const_mul, mul_assoc]
    _ = _ := by
      rw [coefficient_neg]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring

theorem pairing_double {d : ℕ} (z : Coordinates d) (i : Fin d) :
    pairing (quadraticSource z).val (synthesis (axisFrequency i+axisFrequency i) (z i^2)) =
      2 * ‖z i‖^4 := by
  rw [pairing_synthesis, quadraticSource_double]
  rw [← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq, norm_pow]
  ring

theorem pairing_sum {d : ℕ} (z : Coordinates d) {i j : Fin d} (hij : i ≠ j) :
    pairing (quadraticSource z).val (synthesis (axisFrequency i+axisFrequency j) (z i*z j)) =
      4 * ‖z i‖^2 * ‖z j‖^2 := by
  rw [pairing_synthesis, quadraticSource_sum z hij]
  have h : conj (z i*z j)*(2*z i*z j) = 2*(conj (z i*z j)*(z i*z j)) := by ring
  rw [h, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.normSq_eq_norm_sq, norm_mul]
  norm_num
  ring

theorem pairing_diff {d : ℕ} (z : Coordinates d) {i j : Fin d} (hij : i ≠ j) :
    pairing (quadraticSource z).val (synthesis (axisFrequency i-axisFrequency j) (z i*conj (z j))) =
      4 * ‖z i‖^2 * ‖z j‖^2 := by
  rw [pairing_synthesis, quadraticSource_diff z hij]
  have h : conj (z i*conj (z j))*(2*z i*conj (z j)) =
      2*(conj (z i*conj (z j))*(z i*conj (z j))) := by ring
  rw [h, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_conj]
  norm_num
  ring

#print axioms pairing_double
#print axioms pairing_sum
end BecknerOnofri.HighDim.QuadraticModes
