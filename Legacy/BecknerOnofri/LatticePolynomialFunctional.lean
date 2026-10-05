import Legacy.BecknerOnofri.FiniteScalarSemantics
import Legacy.BecknerOnofri.GaussianLattice
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! An additive coefficient functional with the zero frequency removed.
The radial weight is not multiplicative; tensor powers must be expanded
before this functional is applied. -/

open scoped BigOperators

namespace Legacy.BecknerOnofri.LatticePolynomial
open Polynomial Legacy.TorusEndpoint Legacy.TorusEndpoint.GreenMultiplierSummability

noncomputable def radialWeight (d q : ℕ) : ℝ :=
  if q = 0 then 0 else 1 / Real.sqrt ((q : ℝ) ^ d)

noncomputable def weightedCoefficients (d : ℕ) : Polynomial ℕ →+ ℝ where
  toFun P := P.sum (fun q c => (c : ℝ) * radialWeight d q)
  map_zero' := Polynomial.sum_zero_index _
  map_add' P Q := Polynomial.sum_add_index P Q _
    (by intro q; simp) (by intro q a b; simp [add_mul])

theorem weightedCoefficients_monomial (d q c : ℕ) :
    weightedCoefficients d (monomial q c) = (c : ℝ) * radialWeight d q := by
  change (monomial q c : Polynomial ℕ).sum (fun q c => (c : ℝ) * radialWeight d q) = _
  exact Polynomial.sum_monomial_index _ _ (by simp)

theorem polynomialEnergy_eq_weightedCoefficients (d n : ℕ) :
    FiniteScalar.polynomialEnergy d n =
      weightedCoefficients d (Legacy.D10.FiniteScalar.binomialPolynomial n ^ d) /
        (Legacy.D10.FiniteScalar.central n : ℝ) ^ d := by
  let P := Legacy.D10.FiniteScalar.binomialPolynomial n ^ d
  let N := max 64 (P.natDegree + 1)
  change (∑ j ∈ Finset.range N,
      (P.coeff (j + 1) : ℝ) / Real.sqrt (((j + 1 : ℕ) : ℝ) ^ d)) / _ =
      P.sum (fun q c => (c : ℝ) * radialWeight d q) / _
  congr 1
  rw [Polynomial.sum_over_range' P (by intro q; simp) (N + 1) (by dsimp [N]; omega),
    Finset.sum_range_succ']
  simp [radialWeight, div_eq_mul_inv]

def radiusNat {d : ℕ} (k : Frequency d) : ℕ := ∑ i, (k i).natAbs ^ 2

theorem radiusNat_cast {d : ℕ} (k : Frequency d) :
    (radiusNat k : ℝ) = radiusSq k := by
  unfold radiusNat radiusSq
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (k i))
  simp only [Int.cast_natCast, Int.cast_abs] at h
  rw [h, sq_abs]

theorem radiusNat_eq_zero_iff {d : ℕ} (k : Frequency d) :
    radiusNat k = 0 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hpos := radiusSq_one_le hk
    rw [← radiusNat_cast, h] at hpos
    norm_num at hpos
  · intro h
    subst k
    simp [radiusNat]

theorem radialWeight_radiusNat {d : ℕ} (k : Frequency d) :
    radialWeight d (radiusNat k) = GaussianLattice.spectralWeight k := by
  simp only [radialWeight, radiusNat_eq_zero_iff, GaussianLattice.spectralWeight,
    radiusNat_cast]

theorem prod_monomial {ι : Type*} (s : Finset ι) (q c : ι → ℕ) :
    (∏ i ∈ s, monomial (q i) (c i) : Polynomial ℕ) =
      monomial (∑ i ∈ s, q i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih,
      Polynomial.monomial_mul_monomial]

end Legacy.BecknerOnofri.LatticePolynomial
