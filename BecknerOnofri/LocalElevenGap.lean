import BecknerOnofri.ComplementGap

/-! Spectral complement gap in every dimension d ≥ 11. The useful bound is 32, rather than the d ≥ 12 bound 64. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven
theorem complement_eigenvalue_ge_thirtytwo {d : ℕ} (hd : 11 ≤ d)
    {k : Frequency d} (hk : ComplementFrequency k) : 32 ≤ frequencyLength k ^ d := by
  have hexp : (5:ℝ) ≤ (d:ℝ)/2 := by
    have : (11:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hexp
  norm_num at h
  exact h.trans (complement_eigenvalue_lower hk)

/-- Uniform complement coercivity in the useful neighborhood 0≤β/σ≤2. -/
theorem complement_linearized_gap {d : ℕ} (hd : 11 ≤ d) {μ : ℝ}
    (_hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {k : Frequency d} (hk : ComplementFrequency k) :
    (15/16:ℝ) ≤ 1 - μ / frequencyLength k ^ d := by
  have hEig := complement_eigenvalue_ge_thirtytwo hd hk
  have hEig0 : 0 < frequencyLength k ^ d := by linarith
  have hdiv : μ / frequencyLength k ^ d ≤ (1/16:ℝ) := by
    apply (div_le_iff₀ hEig0).mpr
    linarith
  linarith

theorem complementInverseMultiplier_nonneg {d : ℕ} (hd : 11 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (k : Frequency d) :
    0 ≤ complementInverseMultiplier μ k := by
  unfold complementInverseMultiplier
  split_ifs with hk
  · exact inv_nonneg.mpr (by linarith [complement_linearized_gap hd hμ0 hμ2 hk])
  · rfl

theorem complementInverseMultiplier_bound {d : ℕ} (hd : 11 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (k : Frequency d) :
    complementInverseMultiplier μ k ≤ (16/15:ℝ) := by
  unfold complementInverseMultiplier
  split_ifs with hk
  · have hg := complement_linearized_gap hd hμ0 hμ2 hk
    have hp : 0 < 1 - μ / frequencyLength k ^ d := by linarith
    apply (inv_le_comm₀ hp (by norm_num : (0:ℝ)<16/15)).mpr
    norm_num
    exact hg
  · norm_num


theorem complementInverse_left {d : ℕ} (hd : 11 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {a : Frequency d → ℂ} (ha : ComplementSupported a) :
    complementInverse μ (complementLinearized μ a) = a := by
  funext k
  by_cases hk : ComplementFrequency k
  · have hpos : 0 < 1 - μ / frequencyLength k ^ d := by
      linarith [complement_linearized_gap hd hμ0 hμ2 hk]
    have hne : ((1 - μ / frequencyLength k ^ d : ℝ):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hpos.ne'
    simp only [complementInverse, complementLinearized, complementInverseMultiplier,
      if_pos hk, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · simp [complementInverse, complementLinearized, ha k hk]

theorem complementInverse_right {d : ℕ} (hd : 11 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {a : Frequency d → ℂ} (ha : ComplementSupported a) :
    complementLinearized μ (complementInverse μ a) = a := by
  funext k
  by_cases hk : ComplementFrequency k
  · have hpos : 0 < 1 - μ / frequencyLength k ^ d := by
      linarith [complement_linearized_gap hd hμ0 hμ2 hk]
    have hne : ((1 - μ / frequencyLength k ^ d : ℝ):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hpos.ne'
    simp only [complementInverse, complementLinearized, complementInverseMultiplier,
      if_pos hk, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  · simp [complementInverse, complementLinearized, ha k hk]

theorem complementInverse_norm_bound {d : ℕ} (hd : 11 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : Frequency d → ℂ) (k : Frequency d) :
    ‖complementInverse μ a k‖ ≤ (16/15:ℝ)*‖a k‖ := by
  simp only [complementInverse, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (complementInverseMultiplier_nonneg hd hμ0 hμ2 k)]
  exact mul_le_mul_of_nonneg_right (complementInverseMultiplier_bound hd hμ0 hμ2 k) (norm_nonneg _)


#print axioms complement_linearized_gap
end BecknerOnofri.HighDim.LocalEleven
