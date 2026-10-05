module

public import Legacy.BecknerOnofri.LatticePolynomialSigned

@[expose] public section

/-! Exact equality of the full radial polynomial energy and the genuine
integer lattice sum. All dimensions and all indices, including zero, are
allowed. No bounded shell-array semantics is used. -/

open scoped BigOperators

namespace Legacy.BecknerOnofri.LatticePolynomial
open Polynomial Legacy.TorusEndpoint GaussianLattice

theorem central_eq_choose (n : ℕ) :
    Legacy.D10.FiniteScalar.central n = Nat.choose (2*n) n := by
  exact Legacy.D10.FiniteScalar.fastChoose_eq_choose (by omega)

theorem binomialZ_eq_rowCoefficient {n : ℕ} (j : ℤ) (hj : j.natAbs ≤ n) :
    binomialZ n j = (rowCoefficient n j : ℝ) / (Legacy.D10.FiniteScalar.central n : ℝ) := by
  rw [binomialZ, Legacy.D10.binomialCoeffReal_formula, central_eq_choose]
  have hs := Nat.choose_symm (show n + j.natAbs ≤ 2*n by omega)
  rw [show 2*n - (n+j.natAbs) = n-j.natAbs by omega] at hs
  rw [rowCoefficient, hs]

noncomputable def latticeBox (d n : ℕ) : Finset (Frequency d) := by
  classical
  exact Finset.univ.map ⟨signedVector, signedVector_injective d n⟩

theorem mem_latticeBox {d n : ℕ} (k : Frequency d) :
    k ∈ latticeBox d n ↔ ∀ i, (k i).natAbs ≤ n := by
  classical
  simp only [latticeBox, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨a, rfl⟩ i
    exact signed_natAbs_le (a i)
  · intro hk
    choose a ha using fun i => signed_surjective_on (k i) (hk i)
    exact ⟨a, funext ha⟩

theorem binomialTerm_eq_zero_outside {d n : ℕ} (k : Frequency d)
    (hk : k ∉ latticeBox d n) : binomialTerm n k = 0 := by
  classical
  rw [mem_latticeBox] at hk
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  have hz : binomialZ n (k i) = 0 := by
    simp only [binomialZ, Legacy.D10.binomialCoeffReal, Legacy.D10.binomialCoeff_eq_zero hi, Rat.cast_zero]
  have hp : binomialProduct n k = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz
  simp [binomialTerm, hp]

theorem summable_binomialTerm_all (d n : ℕ) :
    Summable (binomialTerm n : Frequency d → ℝ) :=
  summable_of_ne_finset_zero (binomialTerm_eq_zero_outside (d := d) (n := n))

theorem binomialEnergy_eq_signed_sum (d n : ℕ) :
    binomialEnergy d n = ∑ a : Fin d → SignedIndex n, binomialTerm n (signedVector a) := by
  classical
  rw [binomialEnergy, tsum_eq_sum (binomialTerm_eq_zero_outside (d := d) (n := n)),
    latticeBox, Finset.sum_map]
  rfl

theorem binomialProduct_signed (d n : ℕ) (a : Fin d → SignedIndex n) :
    binomialProduct n (signedVector a) =
      ((∏ i, rowCoefficient n (signed (a i)) : ℕ) : ℝ) /
        (Legacy.D10.FiniteScalar.central n : ℝ)^d := by
  unfold binomialProduct signedVector
  simp_rw [binomialZ_eq_rowCoefficient _ (signed_natAbs_le _)]
  rw [Finset.prod_div_distrib]
  simp

/-- The coefficient functional and the actual lattice energy coincide for
every natural dimension and index. -/
theorem polynomialEnergy_eq_binomialEnergy (d n : ℕ) :
    FiniteScalar.polynomialEnergy d n = binomialEnergy d n := by
  classical
  rw [polynomialEnergy_eq_weightedCoefficients, binomialPolynomial_tensor, map_sum,
    binomialEnergy_eq_signed_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [weightedCoefficients_monomial, radialWeight_radiusNat,
    binomialTerm, binomialProduct_signed]
  ring

#print axioms polynomialEnergy_eq_binomialEnergy
#print axioms summable_binomialTerm_all
end Legacy.BecknerOnofri.LatticePolynomial
