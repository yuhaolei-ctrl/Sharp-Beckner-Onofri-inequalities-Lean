import BecknerOnofri.ElevenScalarFinite.Certificates
import BecknerOnofri.ElevenConstants
import BecknerOnofri.ElevenScalarDefinitions
import Legacy.BecknerOnofri.LatticePolynomialBridge

/-! Section 4's strict scalar gap for 1 ≤ n ≤ 21, on the actual binomial
lattice sum. The positive polynomial tail is included using an upper bound
for its whole mass; it is not discarded at the finite array cutoff. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.Eleven.ScalarFinite
open Legacy.BecknerOnofri Legacy.D10.FiniteScalar

theorem betaLambda_nonneg : 0 ≤ (betaLambda : ℝ) := by norm_num [betaLambda]

theorem coefficient_le : ((3543 : ℝ)/200) / spectralThreshold 11 ≤ (betaLambda : ℝ) := by
  rw [spectralThreshold_eleven]
  calc
    (3543/200) / (64 * Real.pi^5 / 945) = (3543/200 * 945/64) / Real.pi^5 := by
      field_simp
    _ ≤ (3543/200 * 945/64) / ((314159 : ℝ)/100000)^5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      gcongr
      linarith [Real.pi_gt_d6]
    _ = (betaLambda : ℝ) := by norm_num [betaLambda]

theorem finite_polynomial_gap {n : ℕ} (hn : 1 ≤ n) (hn21 : n ≤ 21) :
    (1/2000 : ℝ) < 11 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) -
      ((3543 : ℝ)/200) / spectralThreshold 11 * FiniteScalar.polynomialEnergy 11 n := by
  have hQ := checks ⟨n-1, by omega⟩
  simp only [Nat.sub_add_cancel hn] at hQ
  have hR0 := (Rat.cast_lt (K := ℝ)).mpr hQ
  have hR : (betaLambda : ℝ) * (FiniteScalar.energyUpper 11 n : ℝ) + 1/2000 <
      11 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hR0
  have hE := FiniteScalar.polynomialEnergy_le_upper hn hn21 11 (fun _ h h' => weight_check h h')
  have hnE : 0 ≤ FiniteScalar.polynomialEnergy 11 n := by
    unfold FiniteScalar.polynomialEnergy
    positivity
  have h1 := mul_le_mul_of_nonneg_left hE betaLambda_nonneg
  have h2 := mul_le_mul_of_nonneg_right coefficient_le hnE
  linarith

theorem finite_lattice_gap {n : ℕ} (hn : 1 ≤ n) (hn21 : n ≤ 21) :
    (1/2000 : ℝ) < 11 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) -
      ((3543 : ℝ)/200) / spectralThreshold 11 * GaussianLattice.binomialEnergy 11 n := by
  simpa only [LatticePolynomial.polynomialEnergy_eq_binomialEnergy] using finite_polynomial_gap hn hn21

theorem scalarEnergy_eq_legacy (n : ℕ) :
    scalarEnergy n = GaussianLattice.binomialEnergy 11 n := by
  apply tsum_congr
  intro k
  unfold GaussianLattice.binomialTerm GaussianLattice.binomialProduct
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (Legacy.D10.binomialCoeffReal_formula n (k i).natAbs).symm

theorem harmonic_eq (n : ℕ) : Legacy.D10.FiniteScalar.harmonic n = _root_.harmonic n := by
  unfold Legacy.D10.FiniteScalar.harmonic _root_.harmonic
  have h := List.sum_toFinset (fun j : ℕ => (1 : ℚ) / ((j : ℚ)+1))
    (List.nodup_range (n := n))
  have hr : (List.range n).toFinset = Finset.range n := by ext k; simp
  simpa [hr, Nat.cast_add, Nat.cast_one] using h.symm

theorem finite_scalar_gap {n : ℕ} (hn : 1 ≤ n) (hn21 : n ≤ 21) :
    (1/2000 : ℝ) < 11 * (_root_.harmonic n : ℝ) -
      ((3543 : ℝ)/200) / spectralThreshold 11 * scalarEnergy n := by
  rw [scalarEnergy_eq_legacy, ← harmonic_eq]
  exact finite_lattice_gap hn hn21

#print axioms finite_lattice_gap
#print axioms finite_scalar_gap
end BecknerOnofri.HighDim.Eleven.ScalarFinite
