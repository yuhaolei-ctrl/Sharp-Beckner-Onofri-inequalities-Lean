import Legacy.BecknerOnofri.LatticePolynomialFunctional

open scoped BigOperators

namespace Legacy.BecknerOnofri.LatticePolynomial
open Polynomial Legacy.TorusEndpoint

abbrev SignedIndex (n : ℕ) := Option (Fin n ⊕ Fin n)

def signed {n : ℕ} : SignedIndex n → ℤ
  | none => 0
  | some (Sum.inl j) => Int.ofNat (j.val + 1)
  | some (Sum.inr j) => -(Int.ofNat (j.val + 1))

@[simp] theorem signed_natAbs_none (n : ℕ) : (signed (none : SignedIndex n)).natAbs = 0 := rfl
@[simp] theorem signed_natAbs_inl {n : ℕ} (j : Fin n) :
    (signed (some (Sum.inl j))).natAbs = j.val + 1 := rfl
@[simp] theorem signed_natAbs_inr {n : ℕ} (j : Fin n) :
    (signed (some (Sum.inr j))).natAbs = j.val + 1 := by
  exact Int.natAbs_neg _

theorem signed_injective (n : ℕ) : Function.Injective (@signed n) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => cases b <;> simp [signed] at h <;> omega
  | some a =>
    cases b with
    | none => cases a <;> simp [signed] at h <;> omega
    | some b =>
      cases a <;> cases b <;> simp [signed] at h
      · congr 2
        exact Fin.ext (by omega)
      · omega
      · omega
      · congr 2
        exact Fin.ext (by omega)

theorem signed_natAbs_le {n : ℕ} (a : SignedIndex n) : (signed a).natAbs ≤ n := by
  cases a with
  | none => simp [signed]
  | some a => cases a with
    | inl a => simpa only [signed_natAbs_inl] using Nat.succ_le_iff.mpr a.isLt
    | inr a => simpa only [signed_natAbs_inr] using Nat.succ_le_iff.mpr a.isLt

theorem signed_surjective_on {n : ℕ} (j : ℤ) (hj : j.natAbs ≤ n) :
    ∃ a : SignedIndex n, signed a = j := by
  by_cases hzero : j = 0
  · exact ⟨none, hzero.symm⟩
  have habs : 0 < j.natAbs := Int.natAbs_pos.mpr hzero
  have hfin : j.natAbs - 1 < n := by omega
  by_cases hpos : 0 ≤ j
  · refine ⟨some (Sum.inl ⟨j.natAbs - 1, hfin⟩), ?_⟩
    dsimp [signed]
    have hcast := Int.natCast_natAbs j
    rw [abs_of_nonneg hpos] at hcast
    omega
  · refine ⟨some (Sum.inr ⟨j.natAbs - 1, hfin⟩), ?_⟩
    dsimp [signed]
    have hcast := Int.natCast_natAbs j
    rw [abs_of_nonpos (le_of_not_ge hpos)] at hcast
    omega

def signedVector {d n : ℕ} (a : Fin d → SignedIndex n) : Frequency d :=
  fun i => signed (a i)

theorem signedVector_injective (d n : ℕ) :
    Function.Injective (@signedVector d n) := by
  intro a b h
  funext i
  exact signed_injective n (congrFun h i)

def rowCoefficient (n : ℕ) (j : ℤ) : ℕ := Nat.choose (2*n) (n-j.natAbs)

theorem binomialPolynomial_signed (n : ℕ) :
    Legacy.D10.FiniteScalar.binomialPolynomial n =
      ∑ a : SignedIndex n, monomial ((signed a).natAbs ^ 2) (rowCoefficient n (signed a)) := by
  classical
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [rowCoefficient, signed_natAbs_none, signed_natAbs_inl, signed_natAbs_inr]
  rw [Legacy.D10.FiniteScalar.binomialPolynomial, Finset.sum_range_succ']
  simp only [Nat.sub_zero, zero_mul, ite_true, one_mul, zero_pow (by decide : 2 ≠ 0)]
  rw [add_comm]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (monomial ((k + 1) ^ 2) ((2*n).choose (n-(k+1))) : Polynomial ℕ)) n]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_neg (by omega : k + 1 ≠ 0), two_mul, map_add]
  simp only [pow_two]

theorem binomialPolynomial_tensor (d n : ℕ) :
    Legacy.D10.FiniteScalar.binomialPolynomial n ^ d =
      ∑ a : Fin d → SignedIndex n,
        monomial (radiusNat (signedVector a))
          (∏ i, rowCoefficient n (signed (a i))) := by
  classical
  rw [binomialPolynomial_signed, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro a ha
  exact prod_monomial Finset.univ _ _

end Legacy.BecknerOnofri.LatticePolynomial
