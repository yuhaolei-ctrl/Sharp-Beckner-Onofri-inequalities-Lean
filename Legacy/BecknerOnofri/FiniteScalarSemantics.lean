import Legacy.BecknerOnofri.FiniteScalarCore
import Legacy.BecknerOnofri.FiniteWeights
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Interval.Finset.Nat

/-!
The certified finite arrays bound the energy of the full radial polynomial.
The weight certificates remain an explicit integer premise in this module.
The identification with a lattice sum or actual Fourier integrals is a
separate theorem and is not asserted here.
-/

namespace Legacy.BecknerOnofri.FiniteScalar

open Legacy.D10.FiniteScalar
open scoped BigOperators

set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option profiler true

-- These are data-generating functions. Proof transformations should use their
-- public equations instead of reducing the large integer arithmetic.
attribute [local irreducible] reciprocalUnits Legacy.D10.FiniteScalar.central

noncomputable def polynomialEnergy (d n : Nat) : ℝ :=
  let P := binomialPolynomial n ^ d
  let N := max 64 (P.natDegree + 1)
  (∑ j ∈ Finset.range N,
    (P.coeff (j + 1) : ℝ) / Real.sqrt (((j + 1 : Nat) : ℝ) ^ d)) /
      (central n : ℝ) ^ d

theorem range_list_sum (f : Nat → Nat) (N : Nat) :
    ((List.range N).map f).sum = ∑ j ∈ Finset.range N, f j := by
  have hr : (List.range N).toFinset = Finset.range N := by
    ext k
    simp
  simpa only [hr] using (List.sum_toFinset f (List.nodup_range (n := N))).symm

theorem shellArray_size (n d : Nat) : (shellArray n d).size = 65 := by
  cases d with
  | zero => exact initialCoefficients_size
  | succ d => rw [shellArray_succ, convolutionStep_size]

theorem shellArray_toList (n d : Nat) :
    (shellArray n d).toList =
      (List.range 65).map (fun q => (shellArray n d)[q]!) := by
  apply List.ext_getElem
  · simp [shellArray_size]
  · intro i hi hj
    have hia : i < (shellArray n d).size := by simpa using hi
    simp [getElem!_pos, hia]

theorem retainedMass_eq_coeff_sum {n : Nat} (hn : n ≤ 21) (d : Nat) :
    retainedMass n d = ∑ q ∈ Finset.range 65, (binomialPolynomial n ^ d).coeff q := by
  rw [retainedMass, shellArray_toList, range_list_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact shellArray_binomial_coeff hn d (Finset.mem_range.mp hq)

theorem binomialPolynomial_power_mass {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 21)
    (d : Nat) : (binomialPolynomial n ^ d).eval 1 = 4 ^ (d * n) := by
  rw [← fullRadialPolynomial_eq_binomial hn', Polynomial.eval_pow,
    fullRadialPolynomial_eval_one, fullRadialMass_eq hn hn', ← pow_mul]
  rw [Nat.mul_comm]

theorem numeratorWith_eq_coeff_sum {n : Nat} (hn : n ≤ 21) (d : Nat) :
    numeratorWith d n (shellArray n d) =
      (∑ j ∈ Finset.range 64,
        (binomialPolynomial n ^ d).coeff (j + 1) * reciprocalUnits d (j + 1)) +
      (4 ^ (d * n) - retainedMass n d) * reciprocalUnits d 65 := by
  unfold numeratorWith
  rw [range_list_sum]
  apply congrArg (fun x : Nat =>
    x + (4 ^ (d * n) - retainedMass n d) * reciprocalUnits d 65)
  apply Finset.sum_congr rfl
  intro j hj
  rw [shellArray_binomial_coeff hn d (by have := Finset.mem_range.mp hj; omega)]

theorem weighted_reciprocal {d q : Nat}
    (hweights : ∀ q : Nat, 1 ≤ q → q ≤ 65 →
      scale ^ 2 ≤ reciprocalUnits d q ^ 2 * q ^ d)
    (hq : 1 ≤ q) (hq' : q ≤ 65) (c : Nat) :
    (c : ℝ) / Real.sqrt ((q : ℝ) ^ d) ≤
      ((c * reciprocalUnits d q : Nat) : ℝ) / (scale : ℝ) := by
  have h := mul_le_mul_of_nonneg_left
    (reciprocal_sqrt_le (by norm_num [scale]) (by omega) (hweights q hq hq'))
    (show (0 : ℝ) ≤ c by positivity)
  simpa only [Nat.cast_mul, mul_one_div, mul_div_assoc] using h

theorem tail_reciprocal {d q : Nat}
    (hweights : ∀ q : Nat, 1 ≤ q → q ≤ 65 →
      scale ^ 2 ≤ reciprocalUnits d q ^ 2 * q ^ d)
    (hq : 65 ≤ q) (c : Nat) :
    (c : ℝ) / Real.sqrt ((q : ℝ) ^ d) ≤
      ((c * reciprocalUnits d 65 : Nat) : ℝ) / (scale : ℝ) := by
  calc
    _ ≤ (c : ℝ) / Real.sqrt ((65 : ℝ) ^ d) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply Real.sqrt_le_sqrt
      gcongr
      exact_mod_cast hq
    _ ≤ _ := weighted_reciprocal hweights (by decide) (by decide) c

/-- Every positive-degree coefficient is included; the degree-dependent upper
limit only pads the polynomial by zero coefficients where necessary. -/
theorem polynomialEnergy_le_upper {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 21)
    (d : Nat)
    (hweights : ∀ q : Nat, 1 ≤ q → q ≤ 65 →
      scale ^ 2 ≤ reciprocalUnits d q ^ 2 * q ^ d) :
    polynomialEnergy d n ≤ (energyUpper d n : ℝ) := by
  let P := binomialPolynomial n ^ d
  let N := max 64 (P.natDegree + 1)
  have hN : 64 ≤ N := le_max_left _ _
  have hdeg : P.natDegree < N + 1 := by
    have := le_max_right 64 (P.natDegree + 1)
    omega
  have hmass : P.eval 1 = 4 ^ (d * n) := binomialPolynomial_power_mass hn hn' d
  have hsum : (∑ q ∈ Finset.range (N + 1), P.coeff q) = 4 ^ (d * n) := by
    rw [← hmass]
    symm
    simpa using Polynomial.eval_eq_sum_range' hdeg (1 : Nat)
  have hret : retainedMass n d = ∑ q ∈ Finset.range 65, P.coeff q :=
    retainedMass_eq_coeff_sum hn' d
  have hdecomp := Finset.sum_range_add_sum_Ico (fun j => P.coeff (j + 1)) hN
  have htail : (∑ j ∈ Finset.Ico 64 N, P.coeff (j + 1)) =
      4 ^ (d * n) - retainedMass n d := by
    rw [Finset.sum_range_succ'] at hsum
    rw [show (65 : Nat) = 64 + 1 from rfl, Finset.sum_range_succ'] at hret
    omega
  have hlo : (∑ j ∈ Finset.range 64,
      (P.coeff (j + 1) : ℝ) / Real.sqrt (((j + 1 : Nat) : ℝ) ^ d)) ≤
      ((∑ j ∈ Finset.range 64, P.coeff (j + 1) * reciprocalUnits d (j + 1) : Nat) : ℝ) /
        (scale : ℝ) := by
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    exact weighted_reciprocal hweights (by omega)
      (by have := Finset.mem_range.mp hj; omega) _
  have hhi : (∑ j ∈ Finset.Ico 64 N,
      (P.coeff (j + 1) : ℝ) / Real.sqrt (((j + 1 : Nat) : ℝ) ^ d)) ≤
      (((4 ^ (d * n) - retainedMass n d) * reciprocalUnits d 65 : Nat) : ℝ) /
        (scale : ℝ) := by
    rw [← htail, Finset.sum_mul, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    exact tail_reciprocal hweights (by have := (Finset.mem_Ico.mp hj).1; omega) _
  have hboth := add_le_add hlo hhi
  rw [Finset.sum_range_add_sum_Ico _ hN] at hboth
  have hdiv := div_le_div_of_nonneg_right hboth
    (pow_nonneg (Nat.cast_nonneg (central n)) d)
  unfold polynomialEnergy energyUpper energyUpperWith
  rw [numeratorWith_eq_coeff_sum hn' d]
  convert hdiv using 1 <;> first | rfl | (push_cast; ring)

/-- In dimensions three through ten the integer reciprocal-weight premises
are discharged by the independently kernel-checked finite certificates. -/
theorem polynomialEnergy_le_certified_upper {n d : Nat}
    (hn : 1 ≤ n) (hn' : n ≤ 21) (hd : 3 ≤ d) (hd' : d ≤ 10) :
    polynomialEnergy d n ≤ (energyUpper d n : ℝ) :=
  polynomialEnergy_le_upper hn hn' d (fun _ hq hq' => weight_check hd hd' hq hq')

end Legacy.BecknerOnofri.FiniteScalar
