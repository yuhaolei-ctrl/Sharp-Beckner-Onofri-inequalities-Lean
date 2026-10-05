module

public import BecknerOnofri.SpinBinaryJensen

@[expose] public section

noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.Spin

theorem binary_entropy_split {p q A : ℝ} (hp : 0 < p) (hq : 0 < q) (hA : 0 < A) :
    p * Real.log (2 * A * p) + q * Real.log (2 * A * q) =
      (p + q) * Real.log (A * (p + q)) +
        (p + q) * binaryCost ((p - q) / (p + q)) := by
  have hm : 0 < p + q := add_pos hp hq
  have hplus : 1 + (p - q) / (p + q) = 2 * p / (p + q) := by field_simp; ring
  have hminus : 1 - (p - q) / (p + q) = 2 * q / (p + q) := by field_simp; ring
  unfold binaryCost
  rw [hplus, hminus]
  rw [Real.log_mul (by positivity : (2 * A : ℝ) ≠ 0) hp.ne',
    Real.log_mul (by positivity : (2 * A : ℝ) ≠ 0) hq.ne',
    Real.log_mul hA.ne' hm.ne', Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hA.ne',
    Real.log_div (by positivity : (2 * p : ℝ) ≠ 0) hm.ne',
    Real.log_div (by positivity : (2 * q : ℝ) ≠ 0) hm.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq.ne']
  field_simp
  ring

#print axioms binary_entropy_split
end BecknerOnofri.HighDim.Spin
