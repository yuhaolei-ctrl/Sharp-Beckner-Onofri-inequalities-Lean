module

public import Legacy.BecknerOnofri.ScalarAssembly
public import Legacy.BecknerOnofri.GaussianCentral
public import Legacy.BecknerOnofri.HarmonicGaussian
public import Legacy.BecknerOnofri.LatticePolynomialBridge
public import Legacy.BecknerOnofri.GaussianHeatSplit

@[expose] public section

/-! The unconditional scalar tail and all-index scalar gap in dimensions
three through ten, for the full radial polynomial and actual lattice sum. -/

namespace Legacy.BecknerOnofri.GaussianScalarTail
open GaussianLattice GaussianCentral ThetaDomination UniformTail
open scoped BigOperators

theorem harmonic_eq_harmonic (n : ℕ) : Legacy.D10.FiniteScalar.harmonic n = harmonic n := by
  unfold Legacy.D10.FiniteScalar.harmonic harmonic
  have h := List.sum_toFinset (fun j : ℕ => (1 : ℚ) / ((j : ℚ)+1))
    (List.nodup_range (n := n))
  have hr : (List.range n).toFinset = Finset.range n := by ext k; simp
  simpa [hr, Nat.cast_add, Nat.cast_one] using h.symm

theorem gaussian_parameter_lt_pi (n : ℕ) (hn : 1 ≤ n) :
    Real.log (1+1/(n:ℝ)) < Real.pi := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h := log_one_add_inv_lt n (by omega)
  have hi : 1/(n:ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hnR
  linarith [Real.pi_gt_d2]

theorem coefficient_nonneg {d : ℕ} (hd : 0 < d) : 0 ≤ 2 * endpointConstant d := by
  unfold endpointConstant
  exact mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg d)
    (Legacy.TorusEndpoint.endpointSigma_pos hd).le)

theorem coefficient_gamma_normalization {d : ℕ} (hd : 0 < d) :
    (2 * endpointConstant d) * (Real.pi^((d:ℝ)/2) / Real.Gamma ((d:ℝ)/2)) = d := by
  have hg : Real.Gamma ((d:ℝ)/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (div_pos (Nat.cast_pos.mpr hd) (by norm_num))).ne'
  have hp : Real.pi^((d:ℝ)/2) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  rw [twice_endpointConstant_eq_gamma]
  field_simp

theorem psiCombination_add_gamma (d : ℕ) (gamma : ℝ) :
    psiCombination d gamma (Real.log 2) = psiCombination d 0 (Real.log 2) + gamma := by
  unfold psiCombination
  split_ifs <;> ring

/-- Algebraic transfer for a single positive index. The only analytic premise
here is the displayed genuine Gaussian-energy estimate. -/
theorem scalar_gap_lower_of_heat_bound {d n : ℕ}
    (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n)
    (hHeat : gaussianEnergy d (Real.log (1+1/(n:ℝ))) ≤
      (Real.pi^((d:ℝ)/2) / Real.Gamma ((d:ℝ)/2)) *
        (central ((d:ℝ)/2) (Real.log (1+1/(n:ℝ))/Real.pi) + thetaIntegral realTheta d)) :
    scalarDelta d - tailWeight d / Real.pi * Real.log (1+1/(n:ℝ)) ≤ scalarGap d n := by
  let a := Real.log (1+1/(n:ℝ))
  have ha : 0 < a := log_parameter_pos (by omega)
  have hap : a < Real.pi := gaussian_parameter_lt_pi n hn
  have hd0 : 0 < d := by omega
  have hdR : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hc := central_le_dimension d hd3 hd10 (a/Real.pi)
    (div_pos ha Real.pi_pos) ((div_lt_one Real.pi_pos).mpr hap)
  rw [Real.log_div ha.ne' Real.pi_pos.ne'] at hc
  have hH := HarmonicGaussian.harmonic_add_log_gaussian_ge_gamma n hn
  rw [← harmonic_eq_harmonic] at hH
  have hEnergy : (2 * endpointConstant d) * FiniteScalar.polynomialEnergy d n ≤
      (d:ℝ) * (central ((d:ℝ)/2) (a/Real.pi) + thetaIntegral realTheta d) := by
    rw [LatticePolynomial.polynomialEnergy_eq_binomialEnergy]
    calc
      (2 * endpointConstant d) * binomialEnergy d n ≤
          (2 * endpointConstant d) * gaussianEnergy d a :=
        mul_le_mul_of_nonneg_left (binomialEnergy_le_gaussianEnergy (by omega))
          (coefficient_nonneg hd0)
      _ ≤ (2 * endpointConstant d) *
          ((Real.pi^((d:ℝ)/2) / Real.Gamma ((d:ℝ)/2)) *
            (central ((d:ℝ)/2) (a/Real.pi) + thetaIntegral realTheta d)) :=
        mul_le_mul_of_nonneg_left hHeat (coefficient_nonneg hd0)
      _ = _ := by rw [← mul_assoc, coefficient_gamma_normalization hd0]
  have hc' := mul_le_mul_of_nonneg_left hc hdR
  have hH' := mul_le_mul_of_nonneg_left hH hdR
  unfold scalarDelta delta scalarGap tailWeight
  rw [psiCombination_add_gamma]
  change _ ≤ (d:ℝ) * (Legacy.D10.FiniteScalar.harmonic n:ℝ) - _
  dsimp only [a] at hc' hEnergy
  simp only [div_eq_mul_inv] at hc' hEnergy hH' ⊢
  nlinarith only [hEnergy, hc', hH']

/-- The genuine Gaussian estimate now discharges the former analytic tail
premise. This scalar theorem is not the endpoint for arbitrary densities. -/
theorem gaussianTailBound {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10) : GaussianTailBound d := by
  intro n hn
  apply scalar_gap_lower_of_heat_bound hd3 hd10 (by omega : 1 ≤ n)
  exact GaussianHeatSplit.gaussianEnergy_le_central hd3 hd10
    (log_parameter_pos (by omega : 0 < n)) (gaussian_parameter_lt_pi n (by omega))

/-- Unconditional, strict scalar margin at every positive natural index. -/
theorem all_indices_scalar_gap {d n : ℕ}
    (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n) :
    (3/1100 : ℝ) < scalarGap d n :=
  all_indices_scalar_gap_of_gaussian hd3 hd10 hn (gaussianTailBound hd3 hd10)

/-- The same strict margin expressed directly on the actual integer lattice. -/
theorem all_indices_lattice_gap {d n : ℕ}
    (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n) :
    (3/1100 : ℝ) < (d:ℝ) * (Legacy.D10.FiniteScalar.harmonic n:ℝ) -
      (2 * endpointConstant d) * binomialEnergy d n := by
  simpa only [scalarGap, LatticePolynomial.polynomialEnergy_eq_binomialEnergy] using
    all_indices_scalar_gap hd3 hd10 hn

theorem binomialEnergy_zero (d : ℕ) : binomialEnergy d 0 = 0 := by
  rw [← LatticePolynomial.polynomialEnergy_eq_binomialEnergy]
  simp [FiniteScalar.polynomialEnergy, Legacy.D10.FiniteScalar.binomialPolynomial,
    Polynomial.coeff_one]

/-- The zero index is included, as needed when integrating latent indices. -/
theorem all_indices_lattice_bound {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (n : ℕ) :
    (2 * endpointConstant d) * binomialEnergy d n ≤
      (d:ℝ) * (Legacy.D10.FiniteScalar.harmonic n:ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [binomialEnergy_zero, Legacy.D10.FiniteScalar.harmonic]
  · have h := all_indices_lattice_gap hd3 hd10 (show 1 ≤ n by omega)
    linarith

/-- The positive-index margin persists with an explicit zero-index indicator. -/
theorem all_indices_lattice_indicator_bound {d : ℕ}
    (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (n : ℕ) :
    (2 * endpointConstant d) * binomialEnergy d n +
      (if n = 0 then 0 else (3/1100 : ℝ)) ≤
        (d:ℝ) * (Legacy.D10.FiniteScalar.harmonic n:ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [binomialEnergy_zero, Legacy.D10.FiniteScalar.harmonic]
  · rw [if_neg hn]
    have h := all_indices_lattice_gap hd3 hd10 (show 1 ≤ n by omega)
    linarith

#print axioms gaussianTailBound
#print axioms all_indices_scalar_gap
#print axioms all_indices_lattice_gap
#print axioms all_indices_lattice_bound
#print axioms all_indices_lattice_indicator_bound

end Legacy.BecknerOnofri.GaussianScalarTail
