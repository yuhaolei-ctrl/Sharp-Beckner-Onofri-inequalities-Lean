module

public import Legacy.D10.FiniteScalarCore
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace Legacy.D10.FiniteScalar

set_option maxHeartbeats 0
set_option profiler true
set_option maxRecDepth 100000

open scoped BigOperators

theorem convolutionStep_size (a r : Array Nat) : (convolutionStep a r).size = 65 := by
  simp [convolutionStep]

theorem initialCoefficients_size : initialCoefficients.size = 65 := by
  simp [initialCoefficients]

theorem radialRow_size (n : Nat) : (radialRow n).size = 9 := by
  simp [radialRow]

theorem convolutionStep_get (a r : Array Nat) {q : Nat} (hq : q < 65) :
    (convolutionStep a r)[q]! =
      ∑ k ∈ Finset.range 9, if k*k ≤ q then r[k]! * a[q-k*k]! else 0 := by
  have hsz : q < (convolutionStep a r).size := by simpa [convolutionStep_size] using hq
  rw [getElem!_pos (convolutionStep a r) q hsz]
  simp only [convolutionStep, Array.getElem_map, List.getElem_toArray, List.getElem_range]
  have hr : (List.range 9).toFinset = Finset.range 9 := by
    ext k
    simp
  simpa only [hr] using (List.sum_toFinset _ (List.nodup_range (n := 9))).symm

theorem initialCoefficients_get {q : Nat} (hq : q < 65) :
    initialCoefficients[q]! = if q = 0 then 1 else 0 := by
  have hsz : q < initialCoefficients.size := by simpa [initialCoefficients_size] using hq
  rw [getElem!_pos initialCoefficients q hsz]
  simp [initialCoefficients]

/-- The polynomial containing exactly those one-dimensional terms which
can contribute to squared radii at most 64. -/
noncomputable def truncatedRadialPolynomial (n : Nat) : Polynomial Nat :=
  ∑ k ∈ Finset.range 9, Polynomial.monomial (k*k) (radialRow n)[k]!

theorem monomial_mul_coeff (p : Polynomial Nat) (j a q : Nat) :
    (Polynomial.monomial j a * p).coeff q =
      if j ≤ q then a * p.coeff (q-j) else 0 := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs <;> simp_all

theorem truncatedRadialPolynomial_mul_coeff (n : Nat) (p : Polynomial Nat) (q : Nat) :
    (truncatedRadialPolynomial n * p).coeff q =
      ∑ k ∈ Finset.range 9, if k*k ≤ q then (radialRow n)[k]! * p.coeff (q-k*k) else 0 := by
  simp only [truncatedRadialPolynomial, Finset.sum_mul, Polynomial.finsetSum_coeff,
    monomial_mul_coeff]

theorem shellArray_succ (n r : Nat) :
    shellArray n (r+1) = convolutionStep (shellArray n r) (radialRow n) := by
  exact Function.iterate_succ_apply' _ _ _

theorem shellArray_coeff (n r : Nat) {q : Nat} (hq : q < 65) :
    (shellArray n r)[q]! = (truncatedRadialPolynomial n ^ r).coeff q := by
  induction r generalizing q with
  | zero =>
      simp [shellArray, Nat.iterate, initialCoefficients_get hq, Polynomial.coeff_one]
  | succ r ih =>
      rw [shellArray_succ, convolutionStep_get _ _ hq, pow_succ',
        truncatedRadialPolynomial_mul_coeff]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k*k ≤ q
      · simp only [if_pos h]
        rw [ih (by omega)]
      · simp only [if_neg h]

def radialWeight (n k : Nat) : Nat :=
  if k ≤ n then (if k = 0 then 1 else 2) * fastChoose (2*n) (n-k) else 0

theorem radialRow_get (n : Nat) {k : Nat} (hk : k < 9) :
    (radialRow n)[k]! = radialWeight n k := by
  have hsz : k < (radialRow n).size := by simpa [radialRow_size] using hk
  rw [getElem!_pos (radialRow n) k hsz]
  simp [radialRow, radialWeight]

/-- All terms of the original one-variable polynomial for n<=21. -/
noncomputable def fullRadialPolynomial (n : Nat) : Polynomial Nat :=
  ∑ k ∈ Finset.range 22, Polynomial.monomial (k*k) (radialWeight n k)

noncomputable def binomialPolynomial (n : Nat) : Polynomial Nat :=
  ∑ k ∈ Finset.range (n+1),
    Polynomial.monomial (k*k) ((if k = 0 then 1 else 2) * Nat.choose (2*n) (n-k))

theorem fullRadialPolynomial_eq_binomial {n : Nat} (hn : n ≤ 21) :
    fullRadialPolynomial n = binomialPolynomial n := by
  symm
  unfold binomialPolynomial fullRadialPolynomial
  trans ∑ k ∈ Finset.range (n+1), Polynomial.monomial (k*k) (radialWeight n k)
  · apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by simpa using hk
    simp [radialWeight, hkn, fastChoose_eq_choose (by omega : n-k ≤ 2*n)]
  · apply Finset.sum_subset (Finset.range_mono (by omega : n+1 ≤ 22))
    intro k hk hkn
    have hnlt : n < k := by simpa using hkn
    simp [radialWeight, Nat.not_le.mpr hnlt]

theorem fullRadialPolynomial_mul_coeff (n : Nat) (p : Polynomial Nat) (q : Nat) :
    (fullRadialPolynomial n * p).coeff q =
      ∑ k ∈ Finset.range 22, if k*k ≤ q then radialWeight n k * p.coeff (q-k*k) else 0 := by
  simp only [fullRadialPolynomial, Finset.sum_mul, Polynomial.finsetSum_coeff,
    monomial_mul_coeff]

theorem fullRadialPolynomial_mul_coeff_low (n : Nat) (p : Polynomial Nat)
    {q : Nat} (hq : q < 65) :
    (fullRadialPolynomial n * p).coeff q = (truncatedRadialPolynomial n * p).coeff q := by
  rw [fullRadialPolynomial_mul_coeff, truncatedRadialPolynomial_mul_coeff]
  trans ∑ k ∈ Finset.range 9, if k*k ≤ q then radialWeight n k * p.coeff (q-k*k) else 0
  · symm
    apply Finset.sum_subset (Finset.range_mono (by decide : 9 ≤ 22))
    intro k hk hk9
    have hk' : 9 ≤ k := by simpa using hk9
    have hkq : ¬ k*k ≤ q := by nlinarith
    simp [hkq]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [radialRow_get n (by simpa using hk)]

theorem fullRadialPolynomial_pow_coeff_low (n r : Nat) {q : Nat} (hq : q < 65) :
    (fullRadialPolynomial n ^ r).coeff q = (truncatedRadialPolynomial n ^ r).coeff q := by
  induction r generalizing q with
  | zero => simp only [pow_zero]
  | succ r ih =>
      rw [pow_succ', fullRadialPolynomial_mul_coeff_low _ _ hq, pow_succ',
        truncatedRadialPolynomial_mul_coeff, truncatedRadialPolynomial_mul_coeff]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k*k ≤ q
      · simp only [if_pos h]
        rw [ih (by omega)]
      · simp only [if_neg h]

/-- The computed entries are coefficients of the full binomial polynomial,
not a free-standing numerical array. -/
theorem shellArray_binomial_coeff {n : Nat} (hn : n ≤ 21) (r : Nat)
    {q : Nat} (hq : q < 65) :
    (shellArray n r)[q]! = (binomialPolynomial n ^ r).coeff q := by
  rw [shellArray_coeff _ _ hq, ← fullRadialPolynomial_pow_coeff_low _ _ hq,
    fullRadialPolynomial_eq_binomial hn]

def fullRadialMass (n : Nat) : Nat :=
  ((List.range 22).map fun k => radialWeight n k).sum

theorem fullRadialMass_check01 : fullRadialMass 1 = 4^1 := by
  decide +kernel

theorem fullRadialMass_check02 : fullRadialMass 2 = 4^2 := by
  decide +kernel

theorem fullRadialMass_check03 : fullRadialMass 3 = 4^3 := by
  decide +kernel

theorem fullRadialMass_check04 : fullRadialMass 4 = 4^4 := by
  decide +kernel

theorem fullRadialMass_check05 : fullRadialMass 5 = 4^5 := by
  decide +kernel

theorem fullRadialMass_check06 : fullRadialMass 6 = 4^6 := by
  decide +kernel

theorem fullRadialMass_check07 : fullRadialMass 7 = 4^7 := by
  decide +kernel

theorem fullRadialMass_check08 : fullRadialMass 8 = 4^8 := by
  decide +kernel

theorem fullRadialMass_check09 : fullRadialMass 9 = 4^9 := by
  decide +kernel

theorem fullRadialMass_check10 : fullRadialMass 10 = 4^10 := by
  decide +kernel

theorem fullRadialMass_check11 : fullRadialMass 11 = 4^11 := by
  decide +kernel

theorem fullRadialMass_check12 : fullRadialMass 12 = 4^12 := by
  decide +kernel

theorem fullRadialMass_check13 : fullRadialMass 13 = 4^13 := by
  decide +kernel

theorem fullRadialMass_check14 : fullRadialMass 14 = 4^14 := by
  decide +kernel

theorem fullRadialMass_check15 : fullRadialMass 15 = 4^15 := by
  decide +kernel

theorem fullRadialMass_check16 : fullRadialMass 16 = 4^16 := by
  decide +kernel

theorem fullRadialMass_check17 : fullRadialMass 17 = 4^17 := by
  decide +kernel

theorem fullRadialMass_check18 : fullRadialMass 18 = 4^18 := by
  decide +kernel

theorem fullRadialMass_check19 : fullRadialMass 19 = 4^19 := by
  decide +kernel

theorem fullRadialMass_check20 : fullRadialMass 20 = 4^20 := by
  decide +kernel

theorem fullRadialMass_check21 : fullRadialMass 21 = 4^21 := by
  decide +kernel

theorem fullRadialMass_checks : ∀ i : Fin 21, fullRadialMass (i.val+1) = 4^(i.val+1) := by
  intro i
  fin_cases i
  · exact fullRadialMass_check01
  · exact fullRadialMass_check02
  · exact fullRadialMass_check03
  · exact fullRadialMass_check04
  · exact fullRadialMass_check05
  · exact fullRadialMass_check06
  · exact fullRadialMass_check07
  · exact fullRadialMass_check08
  · exact fullRadialMass_check09
  · exact fullRadialMass_check10
  · exact fullRadialMass_check11
  · exact fullRadialMass_check12
  · exact fullRadialMass_check13
  · exact fullRadialMass_check14
  · exact fullRadialMass_check15
  · exact fullRadialMass_check16
  · exact fullRadialMass_check17
  · exact fullRadialMass_check18
  · exact fullRadialMass_check19
  · exact fullRadialMass_check20
  · exact fullRadialMass_check21

theorem fullRadialMass_eq {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 21) :
    fullRadialMass n = 4^n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact fullRadialMass_checks ⟨j, by omega⟩

theorem fullRadialPolynomial_eval_one (n : Nat) :
    (fullRadialPolynomial n).eval 1 = fullRadialMass n := by
  simp only [fullRadialPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, one_pow, mul_one]
  unfold fullRadialMass
  have hr : (List.range 22).toFinset = Finset.range 22 := by
    ext k
    simp
  simpa only [hr] using List.sum_toFinset (radialWeight n) (List.nodup_range (n := 22))

theorem binomialPolynomial_power_mass {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 21) :
    (binomialPolynomial n ^ 10).eval 1 = 4^(10*n) := by
  rw [← fullRadialPolynomial_eq_binomial hn', Polynomial.eval_pow,
    fullRadialPolynomial_eval_one, fullRadialMass_eq hn hn', ← pow_mul]
  congr 1
  omega

#print axioms shellArray_binomial_coeff
#print axioms binomialPolynomial_power_mass

end Legacy.D10.FiniteScalar
