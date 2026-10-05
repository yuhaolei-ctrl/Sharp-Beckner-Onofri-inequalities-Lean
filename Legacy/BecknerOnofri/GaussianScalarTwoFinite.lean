import Legacy.BecknerOnofri.FiniteScalar
import Legacy.BecknerOnofri.LatticePolynomialBridge

/-! Three complete finite polynomial certificates for the two-dimensional scalar bound. -/
namespace Legacy.BecknerOnofri.GaussianScalarTwoFinite
open FiniteScalar
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem weight_checks_two : ∀ j : Fin 65,
    scale^2 ≤ reciprocalUnits 2 (j.val+1)^2 * (j.val+1)^2 := by
  decide +kernel

theorem finite_checks_two : ∀ j : Fin 3, FiniteCheck 2 (j.val+1) := by
  decide +kernel

theorem lambda_two : 2 * endpointConstant 2 = 2 / Real.pi := by
  have h := twice_endpointConstant_even 1 (by decide)
  norm_num at h
  exact h

theorem lambda_two_le_upper : 2 * endpointConstant 2 ≤ (lambdaUpper 2 : ℝ) := by
  rw [lambda_two, lambdaUpper_cast]
  norm_num [scalarFactorQ]
  have hp : (314159/100000 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]
  convert! div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2 by norm_num)
    (show (0 : ℝ) < 314159/100000 by norm_num) hp using 1 <;> norm_num

/-- The full radial polynomial and its true lattice energy satisfy all three small cases. -/
theorem small_indices_lattice_gap {n : ℕ} (hn : 1 ≤ n) (hn3 : n ≤ 3) :
    (3/1100 : ℝ) < 2 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) -
      (2 * endpointConstant 2) * GaussianLattice.binomialEnergy 2 n := by
  have hQ := (finite_checks_two ⟨n-1, by omega⟩).2.2
  rw [Nat.sub_add_cancel hn] at hQ
  have hR : (lambdaUpper 2 : ℝ) * (energyUpper 2 n : ℝ) + 3/1100 <
      2 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
    convert! (Rat.cast_lt (K := ℝ)).mpr hQ using 1 <;> push_cast <;> norm_num
  have hE := polynomialEnergy_le_upper hn (by omega : n ≤ 21) 2
    (fun q hq hq65 => by
      have h := weight_checks_two ⟨q-1, by omega⟩
      simpa [Nat.sub_add_cancel hq] using h)
  have h1 := mul_le_mul_of_nonneg_left hE (lambdaUpper_nonneg 2)
  have h2 := mul_le_mul_of_nonneg_right lambda_two_le_upper (polynomialEnergy_nonneg 2 n)
  rw [LatticePolynomial.polynomialEnergy_eq_binomialEnergy] at h1 h2
  linarith

#print axioms finite_checks_two
#print axioms small_indices_lattice_gap
end Legacy.BecknerOnofri.GaussianScalarTwoFinite
