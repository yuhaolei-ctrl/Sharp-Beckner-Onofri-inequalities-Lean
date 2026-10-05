import Legacy.BecknerOnofri.FiniteCertificates
import Legacy.BecknerOnofri.FiniteScalarSemantics
import Legacy.BecknerOnofri.ScalarNormalization

/-! The complete finite polynomial estimate, including its actual Gamma/pi
coefficient. The Fourier/lattice identification remains a separate obligation. -/
namespace Legacy.BecknerOnofri.FiniteScalar
open scoped BigOperators
attribute [local irreducible] reciprocalUnits Legacy.D10.FiniteScalar.central

 theorem polynomialEnergy_nonneg (d n : Nat) : 0 ≤ polynomialEnergy d n := by
  unfold polynomialEnergy
  positivity

 theorem lambdaUpper_nonneg (d : Nat) : 0 ≤ (lambdaUpper d : ℝ) := by
  rw [Legacy.BecknerOnofri.lambdaUpper_cast]
  exact div_nonneg (by exact_mod_cast Legacy.BecknerOnofri.scalarFactorQ_nonneg d)
    (by positivity)

/-- Every one of the manuscript's 168 finite cases, with full polynomial tail
mass accounted for, satisfies the required strict 3/1100 margin. -/
theorem finite_polynomial_gap {d n : Nat}
    (hd : 3 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n) (hn21 : n ≤ 21) :
    (3/1100 : ℝ) <
      (d : ℝ) * (Legacy.D10.FiniteScalar.harmonic n : ℝ) -
        (2 * endpointConstant d) * polynomialEnergy d n := by
  have hQ := (finite_check hd hd10 hn hn21).2.2
  have hR0 := (Rat.cast_lt (K := ℝ)).mpr hQ
  have hR : (lambdaUpper d : ℝ) * (energyUpper d n : ℝ) + 3/1100 <
      (d : ℝ) * (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hR0
  have hE := polynomialEnergy_le_certified_upper hn hn21 hd hd10
  have hL := twice_endpointConstant_le_lambdaUpper d hd hd10
  have h1 := mul_le_mul_of_nonneg_left hE (lambdaUpper_nonneg d)
  have h2 := mul_le_mul_of_nonneg_right hL (polynomialEnergy_nonneg d n)
  linarith

#print axioms finite_polynomial_gap
end Legacy.BecknerOnofri.FiniteScalar
