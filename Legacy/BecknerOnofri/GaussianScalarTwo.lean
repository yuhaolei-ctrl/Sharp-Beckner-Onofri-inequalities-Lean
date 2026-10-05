module

public import Legacy.BecknerOnofri.GaussianHeatTwo
public import Legacy.BecknerOnofri.GaussianScalarTwoFinite
public import Legacy.BecknerOnofri.GaussianScalarTail

@[expose] public section

/-! The complete two-dimensional scalar inequality for the actual integer-lattice energy. -/
namespace Legacy.BecknerOnofri.GaussianScalarTwo
open GaussianLattice GaussianScalarTail GaussianScalarTwoFinite ThetaDomination

/-- The s=1 tail already works from n=4; all constants refer to the actual theta integral. -/
theorem large_indices_lattice_gap {n : ℕ} (hn : 4 ≤ n) :
    (3/1100 : ℝ) < 2 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) -
      (2 * endpointConstant 2) * binomialEnergy 2 n := by
  let a := Real.log (1+1/(n : ℝ))
  have ha : 0 < a := log_parameter_pos (by omega)
  have hap : a < Real.pi := gaussian_parameter_lt_pi n (by omega)
  have hgauss := GaussianHeatTwo.gaussianEnergy_two_le ha hap
  have henergy : (2 * endpointConstant 2) * binomialEnergy 2 n ≤
      2 * (Real.log Real.pi - Real.log a - 1 + thetaIntegral realTheta 2) + 2 * (a/Real.pi) := by
    calc
      _ ≤ (2 / Real.pi) * gaussianEnergy 2 a := by
        rw [lambda_two]
        exact mul_le_mul_of_nonneg_left (binomialEnergy_le_gaussianEnergy (by omega : 0 < n))
          (by positivity)
      _ ≤ (2 / Real.pi) *
          (Real.pi * (Real.log Real.pi - Real.log a - 1 + thetaIntegral realTheta 2) + a) :=
        mul_le_mul_of_nonneg_left hgauss (by positivity)
      _ = _ := by field_simp <;> ring
  have hsmall : a/Real.pi < (1/12 : ℝ) := by
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hrecip : 1/(n : ℝ) ≤ (1/4 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hnR
    have hlog := UniformTail.log_one_add_inv_lt n (by omega)
    have ha4 : a < (1/4 : ℝ) := hlog.trans_le hrecip
    apply (div_lt_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  have hH := HarmonicGaussian.harmonic_add_log_gaussian_ge_gamma n (by omega)
  rw [← harmonic_eq_harmonic] at hH
  change Real.eulerMascheroniConstant ≤ (Legacy.D10.FiniteScalar.harmonic n : ℝ) + Real.log a at hH
  have hJ : thetaIntegral realTheta 2 < (41/125 : ℝ) := by
    convert! ThetaBound.realThetaIntegral_lt (d := 2) (by decide) (by decide) using 1 <;> norm_num
  nlinarith only [henergy, hsmall, hH, hJ, EulerLower.gamma_lower, UniformTail.log_pi_upper]

/-- Every positive binomial index has the same strict margin used in d=3,...,10. -/
theorem all_indices_lattice_gap {n : ℕ} (hn : 1 ≤ n) :
    (3/1100 : ℝ) < 2 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) -
      (2 * endpointConstant 2) * binomialEnergy 2 n := by
  by_cases hs : n ≤ 3
  · exact small_indices_lattice_gap hn hs
  · exact large_indices_lattice_gap (by omega)

/-- The actual lattice inequality includes n=0, without an analytic premise. -/
theorem all_indices_lattice_bound (n : ℕ) :
    (2 * endpointConstant 2) * binomialEnergy 2 n ≤
      2 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [binomialEnergy_zero, Legacy.D10.FiniteScalar.harmonic]
  · have h := all_indices_lattice_gap (show 1 ≤ n by omega)
    linarith

theorem all_indices_lattice_indicator_bound (n : ℕ) :
    (2 * endpointConstant 2) * binomialEnergy 2 n +
      (if n = 0 then 0 else (3/1100 : ℝ)) ≤
        2 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [binomialEnergy_zero, Legacy.D10.FiniteScalar.harmonic]
  · rw [if_neg hn]
    have h := all_indices_lattice_gap (show 1 ≤ n by omega)
    linarith

#print axioms all_indices_lattice_gap
#print axioms all_indices_lattice_bound
#print axioms all_indices_lattice_indicator_bound
end Legacy.BecknerOnofri.GaussianScalarTwo
