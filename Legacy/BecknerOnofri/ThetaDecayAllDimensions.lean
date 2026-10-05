import Legacy.BecknerOnofri.ThetaIntegrability

open MeasureTheory Set
open scoped BigOperators
namespace Legacy.BecknerOnofri.ThetaDomination

/-- A finite constant majorizing every finite-dimensional theta power. -/
noncomputable def thetaDecayConstant (d : ℕ) : ℝ :=
  (∑ i ∈ Finset.range d, realTheta Real.pi ^ i) *
    (Real.exp Real.pi * (realTheta Real.pi - 1))

theorem thetaDecayConstant_nonneg (d : ℕ) : 0 ≤ thetaDecayConstant d := by
  unfold thetaDecayConstant
  exact mul_nonneg (Finset.sum_nonneg (fun i _ ↦ pow_nonneg
    (le_trans zero_le_one (one_le_realTheta Real.pi_pos)) _))
    (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (one_le_realTheta Real.pi_pos)))

theorem realTheta_pow_sub_one_le (d : ℕ) {t : ℝ} (ht : Real.pi ≤ t) :
    realTheta t ^ d - 1 ≤ thetaDecayConstant d * Real.exp (-t) := by
  have htpos : 0 < t := lt_of_lt_of_le Real.pi_pos ht
  have ht1 := one_le_realTheta htpos
  have hmono := realTheta_antitone Real.pi_pos ht
  have hs : (∑ i ∈ Finset.range d, realTheta t ^ i) ≤
      ∑ i ∈ Finset.range d, realTheta Real.pi ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ (le_trans zero_le_one ht1) hmono i
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range d, realTheta Real.pi ^ i :=
    Finset.sum_nonneg (fun i _ ↦ pow_nonneg
      (le_trans zero_le_one (one_le_realTheta Real.pi_pos)) _)
  calc
    realTheta t ^ d - 1 = (∑ i ∈ Finset.range d, realTheta t ^ i) * (realTheta t - 1) :=
      (geom_sum_mul (realTheta t) d).symm
    _ ≤ (∑ i ∈ Finset.range d, realTheta Real.pi ^ i) * (realTheta t - 1) :=
      mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr ht1)
    _ ≤ (∑ i ∈ Finset.range d, realTheta Real.pi ^ i) *
        (Real.exp (Real.pi - t) * (realTheta Real.pi - 1)) :=
      mul_le_mul_of_nonneg_left (realTheta_sub_one_le ht) hsum0
    _ = thetaDecayConstant d * Real.exp (-t) := by
      rw [sub_eq_add_neg, Real.exp_add]
      unfold thetaDecayConstant
      ring


end Legacy.BecknerOnofri.ThetaDomination
