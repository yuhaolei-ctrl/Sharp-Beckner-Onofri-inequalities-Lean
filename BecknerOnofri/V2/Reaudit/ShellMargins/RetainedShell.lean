module

public import Legacy.BecknerOnofri.FiniteScalar
public import Legacy.BecknerOnofri.GaussianScalarTwo
public import Legacy.D10.FiniteShellList
public import BecknerOnofri.LowScalarFull
public import BecknerOnofri.ElevenScalarFinite
public import BecknerOnofri.ElevenConstants
public import BecknerOnofri.V2.Reaudit.ShellMargins.Checks

@[expose] public section

/-! # Rows S020 and S030: the retained-shell certificate, literally

Replacement text: `ManuscriptPatch/manuscript_v2_proposed.tex`, the subsection
`subsec:finite-scalar-inequalities` (lines 2201-2236, marker `% REAUDIT S020`) and the finite part of
`d11:prop:scalar` (lines 2690-2703, marker `% REAUDIT S030`); original text in
`beckner_v2_proof_route_decisions_20261010T105832Z.md`, section 3.4.

Notation of the text, and its Lean counterpart in this file:

* `B = 2^40`                          `B`;
* `b = C(2n, n)`                      `b n`;
* `p_q`, the coefficient of `z^q` in `(b + 2 ∑_{j=1}^n C(2n,n+j) z^{j²})^d`     `p d n q`;
* `U_q`, the least nonnegative integer with `U_q² q^d ≥ B²`                     `leastUnit d q`;
* the right-hand side of `eq:finite-scalar-weight-bound`                         `retainedShellBound U d n`;
* `ℓ_d^+` of `eq:finite-scalar-couplings`                                        `couplingUpper d`.

The bound `retainedShellBound` retains the shells `q = |k|² ≤ 64` exactly and charges **all** omitted
mass `4^{dn} - ∑_{q=0}^{64} p_q` to the weight `U_65` (the cutoff `q ≤ 64` is a computational choice,
not an analytic threshold).  The kernel computations are those of the legacy `FiniteCheck`
(`Legacy.BecknerOnofri.FiniteScalar.energyUpper` evaluated with `decide +kernel`) with a larger margin.
-/

noncomputable section
open Finset Polynomial
open scoped BigOperators

namespace BecknerOnofri.V2.Reaudit.ShellMargins

open Legacy.BecknerOnofri
open Legacy.BecknerOnofri.FiniteScalar (reciprocalUnits lambdaUpper energyUpper energyUpperWith
  numeratorWith retainedMass polynomialEnergy)
open Legacy.D10.FiniteScalar (binomialPolynomial)

/-- `B = 2^40`. -/
def B : ℕ := 2 ^ 40

theorem B_eq_scale : B = FiniteScalar.scale := rfl

/-- `b = C(2n, n)` (`eq:finite-scalar-polynomial`, [TeX `manuscript_v2_proposed.tex` line 2205]). -/
def b (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- The polynomial `b + 2 ∑_{j=1}^n C(2n, n+j) z^{j²}` of `eq:finite-scalar-polynomial`. -/
def textPoly (n : ℕ) : ℕ[X] :=
  C (b n) + C 2 * ∑ j ∈ Icc 1 n, C (Nat.choose (2 * n) (n + j)) * X ^ (j ^ 2)

/-- `p_q` ([TeX `manuscript_v2_proposed.tex` lines 2205-2208]): the coefficient of `z^q` in `(b + 2 ∑_{j=1}^n C(2n,n+j) z^{j²})^d`. -/
def p (d n q : ℕ) : ℕ := ((textPoly n) ^ d).coeff q

/-- `ℓ_d^+` of `eq:finite-scalar-couplings` ([TeX `manuscript_v2_proposed.tex` lines 2224-2229]), with `π_* = 314159/100000`, `m = ⌊d/2⌋`:
`ℓ_{2m}^+ = 2 m!/π_*^m`, `ℓ_{2m+1}^+ = (2m+1)(2m)!/(4^m m! π_*^m)`. -/
def couplingUpper (d : ℕ) : ℚ :=
  if d % 2 = 0 then 2 * ((d / 2).factorial : ℚ) / ((314159 : ℚ) / 100000) ^ (d / 2)
  else (d : ℚ) * ((2 * (d / 2)).factorial : ℚ) /
    ((4 : ℚ) ^ (d / 2) * ((d / 2).factorial : ℚ) * ((314159 : ℚ) / 100000) ^ (d / 2))

/-- The right-hand side of `eq:finite-scalar-weight-bound` ([TeX `manuscript_v2_proposed.tex` lines 2217-2222]) for a weight `U`:
`(1/(B b^d)) [∑_{q=1}^{64} p_q U_q + U_65 (4^{dn} - ∑_{q=0}^{64} p_q)]`.  The subtraction is taken in
`ℚ` (it is nonnegative, `mass_le`); every omitted coefficient is in the second term. -/
def retainedShellBound (U : ℕ → ℕ) (d n : ℕ) : ℚ :=
  ((∑ q ∈ Icc 1 64, (p d n q : ℚ) * (U q : ℚ)) +
      (U 65 : ℚ) * ((4 : ℚ) ^ (d * n) - ∑ q ∈ range 65, (p d n q : ℚ))) /
    ((B : ℚ) * (b n : ℚ) ^ d)

/-- `U_q`: the least nonnegative integer with `B² ≤ U_q² q^d` ([TeX `manuscript_v2_proposed.tex` line 2214]). -/
def leastUnit (d q : ℕ) : ℕ := sInf {U : ℕ | B ^ 2 ≤ U ^ 2 * q ^ d}

theorem leastUnit_spec {d q : ℕ} (hq : 1 ≤ q) : B ^ 2 ≤ leastUnit d q ^ 2 * q ^ d := by
  have hne : ({U : ℕ | B ^ 2 ≤ U ^ 2 * q ^ d}).Nonempty :=
    ⟨B, by
      have : 1 ≤ q ^ d := Nat.one_le_pow _ _ hq
      calc B ^ 2 = B ^ 2 * 1 := by ring
        _ ≤ B ^ 2 * q ^ d := Nat.mul_le_mul_left _ this⟩
  exact Nat.sInf_mem hne

theorem leastUnit_le {d q U : ℕ} (h : B ^ 2 ≤ U ^ 2 * q ^ d) : leastUnit d q ≤ U :=
  Nat.sInf_le h

/-! ### The polynomial `textPoly` is the legacy `binomialPolynomial` -/

theorem sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ j ∈ Icc 1 n, f j = ∑ k ∈ range n, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

theorem textPoly_eq_binomialPolynomial (n : ℕ) :
    textPoly n = Legacy.D10.FiniteScalar.binomialPolynomial n := by
  unfold textPoly Legacy.D10.FiniteScalar.binomialPolynomial
  rw [Finset.sum_range_succ', sum_Icc_one_eq_range, Finset.mul_sum]
  have h0 : (C (b n) : ℕ[X]) =
      monomial (0 * 0) ((if (0 : ℕ) = 0 then 1 else 2) * Nat.choose (2 * n) (n - 0)) := by
    simp [b, monomial_zero_left]
  rw [add_comm, h0]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hkn : k < n := mem_range.mp hk
  have hsym : Nat.choose (2 * n) (n - (k + 1)) = Nat.choose (2 * n) (n + (k + 1)) := by
    rw [← Nat.choose_symm (show n + (k + 1) ≤ 2 * n by omega)]
    congr 1
    omega
  rw [hsym]
  simp only [Nat.succ_ne_zero, ite_false]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, pow_two (k + 1)]
  ring

theorem p_eq_coeff (d n q : ℕ) :
    p d n q = ((Legacy.D10.FiniteScalar.binomialPolynomial n) ^ d).coeff q := by
  unfold p
  rw [textPoly_eq_binomialPolynomial]

/-- `p_0 = b^d`. -/
theorem p_zero (d n : ℕ) : p d n 0 = b n ^ d := by
  unfold p
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow]
  congr 1
  unfold textPoly
  simp [Polynomial.eval_finsetSum]
  intro j hj
  omega

/-- "Repeated convolution truncated after degree 64 computes the coefficients exactly": the legacy
truncated convolution `shellArray n d` has entries `p d n q` for `q < 65` (`n ≤ 21`). -/
theorem shell_convolution_exact {n : ℕ} (hn : n ≤ 21) (d : ℕ) {q : ℕ} (hq : q < 65) :
    (Legacy.D10.FiniteScalar.shellArray n d)[q]! = p d n q := by
  rw [p_eq_coeff]
  exact Legacy.D10.FiniteScalar.shellArray_binomial_coeff hn d hq

/-- `∑_q p_q = 4^{dn}` (the polynomial evaluated at `z = 1`; `1 ≤ n ≤ 21`). -/
theorem p_total_mass {d n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 21) :
    ((textPoly n) ^ d).eval 1 = 4 ^ (d * n) := by
  rw [textPoly_eq_binomialPolynomial]
  exact Legacy.BecknerOnofri.FiniteScalar.binomialPolynomial_power_mass hn hn' d

/-- `G_{d,n} = b^{-d} ∑_{q ≥ 1} p_q q^{-d/2}`: the sum may be cut at any `N` at least the degree of
`(textPoly n)^d` (all later coefficients vanish).  Here `G_{d,n}` is `LowScalar.energy d n`. -/
theorem energy_eq_shell_sum (d n N : ℕ) (hN : ((textPoly n) ^ d).natDegree ≤ N) :
    HighDim.LowScalar.energy d n =
      (∑ q ∈ range N, (p d n (q + 1) : ℝ) / Real.sqrt (((q + 1 : ℕ) : ℝ) ^ d)) / (b n : ℝ) ^ d := by
  rw [HighDim.LowScalar.energy_eq_legacy, ← LatticePolynomial.polynomialEnergy_eq_binomialEnergy]
  unfold Legacy.BecknerOnofri.FiniteScalar.polynomialEnergy
  have hc : (Legacy.D10.FiniteScalar.central n : ℝ) = (b n : ℝ) := by
    rw [LatticePolynomial.central_eq_choose]; rfl
  simp only [hc]
  congr 1
  have hP : ((textPoly n) ^ d).natDegree = (binomialPolynomial n ^ d).natDegree := by
    rw [textPoly_eq_binomialPolynomial]
  have hcut : ∀ M, (binomialPolynomial n ^ d).natDegree ≤ M →
      ∑ q ∈ range M, ((binomialPolynomial n ^ d).coeff (q + 1) : ℝ) /
          Real.sqrt (((q + 1 : ℕ) : ℝ) ^ d) =
        ∑ q ∈ range (binomialPolynomial n ^ d).natDegree,
          ((binomialPolynomial n ^ d).coeff (q + 1) : ℝ) / Real.sqrt (((q + 1 : ℕ) : ℝ) ^ d) := by
    intro M hM
    symm
    apply sum_subset (range_mono hM)
    intro q _ hq
    have : (binomialPolynomial n ^ d).coeff (q + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simp only [mem_range, not_lt] at hq; omega)
    simp [this]
  simp only [p_eq_coeff]
  rw [hcut N (by rw [← hP]; exact hN),
    hcut _ (le_trans (Nat.le_succ _) (le_max_right _ _))]

/-! ### The retained-shell bound is an upper bound for `G_{d,n}` (`eq:finite-scalar-weight-bound`) -/


/-- The retained mass is at most the total mass: `∑_{q=0}^{64} p_q ≤ 4^{dn}` (`1 ≤ n ≤ 21`). -/
theorem mass_le {d n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 21) : ∑ q ∈ range 65, p d n q ≤ 4 ^ (d * n) := by
  have hmass : ((binomialPolynomial n) ^ d).eval 1 = 4 ^ (d * n) :=
    FiniteScalar.binomialPolynomial_power_mass hn hn' d
  set P := (binomialPolynomial n) ^ d with hP
  have hdeg : P.natDegree < max 65 (P.natDegree + 1) := by
    have := le_max_right 65 (P.natDegree + 1); omega
  have h := Polynomial.eval_eq_sum_range' hdeg (1 : ℕ)
  simp only [one_pow, mul_one] at h
  calc ∑ q ∈ range 65, p d n q = ∑ q ∈ range 65, P.coeff q := by
        refine sum_congr rfl fun q _ => ?_
        rw [p_eq_coeff]
    _ ≤ ∑ q ∈ range (max 65 (P.natDegree + 1)), P.coeff q :=
        sum_le_sum_of_subset (range_mono (le_max_left _ _))
    _ = P.eval 1 := h.symm
    _ = _ := hmass

/-- `retainedShellBound` as a quotient of natural numbers (the subtraction is exact). -/
theorem retainedShellBound_eq {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 21) (d : ℕ) (U : ℕ → ℕ) :
    retainedShellBound U d n =
      (((∑ j ∈ range 64, ((binomialPolynomial n) ^ d).coeff (j + 1) * U (j + 1)) +
        (4 ^ (d * n) - ∑ q ∈ range 65, ((binomialPolynomial n) ^ d).coeff q) * U 65 : ℕ) : ℚ) /
        ((B : ℚ) * (b n : ℚ) ^ d) := by
  have hle : ∑ q ∈ range 65, ((binomialPolynomial n) ^ d).coeff q ≤ 4 ^ (d * n) := by
    have := mass_le (d := d) hn hn'
    simpa only [p_eq_coeff] using this
  unfold retainedShellBound
  simp only [p_eq_coeff]
  rw [sum_Icc_one_eq_range 64 (fun q => (((binomialPolynomial n) ^ d).coeff q : ℚ) * (U q : ℚ))]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hle]
  push_cast
  ring

theorem weighted_reciprocal' {d q : ℕ} {U : ℕ → ℕ}
    (hU : ∀ q, 1 ≤ q → q ≤ 65 → B ^ 2 ≤ U q ^ 2 * q ^ d) (hq : 1 ≤ q) (hq' : q ≤ 65) (c : ℕ) :
    (c : ℝ) / Real.sqrt ((q : ℝ) ^ d) ≤ ((c * U q : ℕ) : ℝ) / (B : ℝ) := by
  have h := mul_le_mul_of_nonneg_left
    (FiniteScalar.reciprocal_sqrt_le (S := B) (by norm_num [B]) (by omega) (hU q hq hq'))
    (show (0 : ℝ) ≤ c by positivity)
  simpa only [Nat.cast_mul, mul_one_div, mul_div_assoc] using h

theorem tail_reciprocal' {d q : ℕ} {U : ℕ → ℕ}
    (hU : ∀ q, 1 ≤ q → q ≤ 65 → B ^ 2 ≤ U q ^ 2 * q ^ d) (hq : 65 ≤ q) (c : ℕ) :
    (c : ℝ) / Real.sqrt ((q : ℝ) ^ d) ≤ ((c * U 65 : ℕ) : ℝ) / (B : ℝ) := by
  calc
    _ ≤ (c : ℝ) / Real.sqrt ((65 : ℝ) ^ d) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply Real.sqrt_le_sqrt
      gcongr
      exact_mod_cast hq
    _ ≤ _ := weighted_reciprocal' hU (by decide) (by decide) c

/-- **`eq:finite-scalar-weight-bound`** for any weight `U` with `B² ≤ U_q² q^d` (`1 ≤ q ≤ 65`), in
the form of the legacy functional `polynomialEnergy d n = b^{-d} ∑_{q ≥ 1} p_q q^{-d/2}`. -/
theorem polynomialEnergy_le_bound {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 21) (d : ℕ) {U : ℕ → ℕ}
    (hU : ∀ q, 1 ≤ q → q ≤ 65 → B ^ 2 ≤ U q ^ 2 * q ^ d) :
    polynomialEnergy d n ≤ (retainedShellBound U d n : ℝ) := by
  let P := (binomialPolynomial n) ^ d
  let N := max 64 (P.natDegree + 1)
  have hN : 64 ≤ N := le_max_left _ _
  have hdeg : P.natDegree < N + 1 := by
    have := le_max_right 64 (P.natDegree + 1)
    omega
  have hmass : P.eval 1 = 4 ^ (d * n) := FiniteScalar.binomialPolynomial_power_mass hn hn' d
  have hsum : (∑ q ∈ range (N + 1), P.coeff q) = 4 ^ (d * n) := by
    rw [← hmass]
    symm
    simpa using Polynomial.eval_eq_sum_range' hdeg (1 : ℕ)
  have hdecomp := Finset.sum_range_add_sum_Ico (fun j => P.coeff (j + 1)) hN
  have htail : (∑ j ∈ Finset.Ico 64 N, P.coeff (j + 1)) =
      4 ^ (d * n) - ∑ q ∈ range 65, P.coeff q := by
    have h65 : ∑ q ∈ range 65, P.coeff q = P.coeff 0 + ∑ j ∈ range 64, P.coeff (j + 1) := by
      rw [show (65 : ℕ) = 64 + 1 from rfl, Finset.sum_range_succ']; ring
    rw [Finset.sum_range_succ'] at hsum
    omega
  have hlo : (∑ j ∈ range 64, (P.coeff (j + 1) : ℝ) / Real.sqrt (((j + 1 : ℕ) : ℝ) ^ d)) ≤
      ((∑ j ∈ range 64, P.coeff (j + 1) * U (j + 1) : ℕ) : ℝ) / (B : ℝ) := by
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    exact weighted_reciprocal' hU (by omega) (by have := Finset.mem_range.mp hj; omega) _
  have hhi : (∑ j ∈ Finset.Ico 64 N, (P.coeff (j + 1) : ℝ) / Real.sqrt (((j + 1 : ℕ) : ℝ) ^ d)) ≤
      (((4 ^ (d * n) - ∑ q ∈ range 65, P.coeff q) * U 65 : ℕ) : ℝ) / (B : ℝ) := by
    rw [← htail, Finset.sum_mul, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    exact tail_reciprocal' hU (by have := (Finset.mem_Ico.mp hj).1; omega) _
  have hboth := add_le_add hlo hhi
  rw [Finset.sum_range_add_sum_Ico _ hN] at hboth
  have hdiv := div_le_div_of_nonneg_right hboth
    (pow_nonneg (Nat.cast_nonneg (Legacy.D10.FiniteScalar.central n)) d)
  have hc : (Legacy.D10.FiniteScalar.central n : ℝ) = (b n : ℝ) := by
    rw [LatticePolynomial.central_eq_choose]; rfl
  unfold polynomialEnergy
  rw [retainedShellBound_eq hn hn' d U]
  rw [hc] at hdiv ⊢
  convert hdiv using 1
  push_cast
  ring

/-! ### The legacy integer weights dominate the least integer weights -/

/-- The legacy weights `reciprocalUnits` satisfy the defining inequality `B² ≤ U_q² q^d`
(`2 ≤ d ≤ 11`, `1 ≤ q ≤ 65`). -/
theorem RU_weights {d : ℕ} (hd : 2 ≤ d) (hd11 : d ≤ 11) :
    ∀ q, 1 ≤ q → q ≤ 65 → B ^ 2 ≤ reciprocalUnits d q ^ 2 * q ^ d := by
  intro q hq hq'
  by_cases h2 : d = 2
  · subst h2
    have := GaussianScalarTwoFinite.weight_checks_two ⟨q - 1, by omega⟩
    have h : FiniteScalar.scale ^ 2 ≤ reciprocalUnits 2 q ^ 2 * q ^ 2 := by
      simpa [Nat.sub_add_cancel hq] using this
    exact h
  by_cases h11 : d = 11
  · subst h11
    exact HighDim.Eleven.ScalarFinite.weight_check hq hq'
  · exact FiniteScalar.weight_check (by omega) (by omega) hq hq'

theorem leastUnit_le_RU {d : ℕ} (hd : 2 ≤ d) (hd11 : d ≤ 11) :
    ∀ q, 1 ≤ q → q ≤ 65 → leastUnit d q ≤ reciprocalUnits d q :=
  fun q hq hq' => leastUnit_le (RU_weights hd hd11 q hq hq')

/-- Legacy weights versus the least integer: for `2 ≤ d ≤ 11` and `1 ≤ q ≤ 65`, the weight
`reciprocalUnits d q` is the least integer `U` with `B² ≤ U² q^d` except at `(d, q) = (3, 2)`. -/
theorem RU_pred_fails :
    ∀ d : Fin 10, ∀ q : Fin 65, (d.val + 2, q.val + 1) ≠ (3, 2) →
      (reciprocalUnits (d.val + 2) (q.val + 1) - 1) ^ 2 * (q.val + 1) ^ (d.val + 2) < B ^ 2 := by
  decide +kernel

theorem leastUnit_eq_RU {d q : ℕ} (hd : 2 ≤ d) (hd11 : d ≤ 11) (hq : 1 ≤ q) (hq' : q ≤ 65)
    (hne : (d, q) ≠ (3, 2)) : leastUnit d q = reciprocalUnits d q := by
  refine le_antisymm (leastUnit_le_RU hd hd11 q hq hq') ?_
  by_contra hlt
  push Not at hlt
  have h1 := RU_pred_fails ⟨d - 2, by omega⟩ ⟨q - 1, by omega⟩
    (by intro h; apply hne; simpa [Nat.sub_add_cancel hd, Nat.sub_add_cancel hq] using h)
  simp only [Nat.sub_add_cancel hd, Nat.sub_add_cancel hq] at h1
  have h2 := leastUnit_spec (d := d) hq
  have h3 : leastUnit d q ≤ reciprocalUnits d q - 1 := by omega
  have h4 : leastUnit d q ^ 2 * q ^ d ≤ (reciprocalUnits d q - 1) ^ 2 * q ^ d :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h3 2)
  omega

/-- At `(d, q) = (3, 2)` the legacy weight is one more than the least integer. -/
theorem leastUnit_three_two : leastUnit 3 2 = 388736063997 ∧ reciprocalUnits 3 2 = 388736063998 := by
  have hRU : reciprocalUnits 3 2 = 388736063998 := by decide +kernel
  refine ⟨?_, hRU⟩
  have hle : leastUnit 3 2 ≤ 388736063997 := leastUnit_le (by norm_num [B])
  have h2 := leastUnit_spec (d := 3) (q := 2) (by norm_num)
  by_contra hne
  have hlt : leastUnit 3 2 ≤ 388736063996 := by omega
  have h4 : leastUnit 3 2 ^ 2 * 2 ^ 3 ≤ 388736063996 ^ 2 * 2 ^ 3 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlt 2)
  have : (388736063996 : ℕ) ^ 2 * 2 ^ 3 < B ^ 2 := by norm_num [B]
  omega

/-- The legacy `energyUpper` is `retainedShellBound` with the legacy weights. -/
theorem energyUpper_eq_bound {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 21) (d : ℕ) :
    (energyUpper d n : ℚ) = retainedShellBound (reciprocalUnits d) d n := by
  rw [retainedShellBound_eq hn hn']
  unfold energyUpper energyUpperWith
  rw [FiniteScalar.numeratorWith_eq_coeff_sum hn' d, FiniteScalar.retainedMass_eq_coeff_sum hn' d]
  have hc : Legacy.D10.FiniteScalar.central n = b n := LatticePolynomial.central_eq_choose n
  rw [hc]
  push_cast
  rfl

theorem retainedShellBound_mono {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 21) (d : ℕ) {U V : ℕ → ℕ}
    (h : ∀ q, 1 ≤ q → q ≤ 65 → U q ≤ V q) :
    retainedShellBound U d n ≤ retainedShellBound V d n := by
  rw [retainedShellBound_eq hn hn', retainedShellBound_eq hn hn']
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.add_le_add
    (sum_le_sum fun j hj => Nat.mul_le_mul_left _
      (h (j + 1) (by omega) (by have := mem_range.mp hj; omega)))
    (Nat.mul_le_mul_left _ (h 65 (by norm_num) le_rfl))

/-- **`eq:finite-scalar-weight-bound`** [TeX `manuscript_v2_proposed.tex` lines 2214-2222]: `G_{d,n} ≤ retainedShellBound U d n` for `1 ≤ n ≤ 21`
and every weight `U` with `B² ≤ U_q² q^d` (in particular `U_q = leastUnit d q`); `G_{d,n}` is
`LowScalar.energy d n = ∑_{k ≠ 0} |k|^{-d} ∏ a_n(k_i)`. -/
theorem energy_le_bound {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 21) (d : ℕ) {U : ℕ → ℕ}
    (hU : ∀ q, 1 ≤ q → q ≤ 65 → B ^ 2 ≤ U q ^ 2 * q ^ d) :
    HighDim.LowScalar.energy d n ≤ (retainedShellBound U d n : ℝ) := by
  rw [HighDim.LowScalar.energy_eq_legacy, ← LatticePolynomial.polynomialEnergy_eq_binomialEnergy]
  exact polynomialEnergy_le_bound hn hn' d hU

theorem energy_le_bound_least {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 21) (d : ℕ) :
    HighDim.LowScalar.energy d n ≤ (retainedShellBound (leastUnit d) d n : ℝ) :=
  energy_le_bound hn hn' d (fun _ hq _ => leastUnit_spec hq)

/-! ### The couplings `ℓ_d^+` -/

theorem couplingUpper_eq_lambdaUpper :
    ∀ i : Fin 10, couplingUpper (i.val + 2) = lambdaUpper (i.val + 2) := by decide +kernel

theorem couplingUpper_nonneg (d : ℕ) : 0 ≤ couplingUpper d := by
  unfold couplingUpper
  split_ifs <;> positivity

/-- Reading off an index from a `Fin`-quantified statement. -/
theorem of_fin {k : ℕ} {P : ℕ → Prop} (h : ∀ j : Fin k, P (j.val + 1)) {n : ℕ}
    (h1 : 1 ≤ n) (h2 : n ≤ k) : P n := by
  have := h ⟨n - 1, by omega⟩
  simpa [Nat.sub_add_cancel h1] using this

/-! ### The 171 pairs -/

/-- The 171 pairs of the text ([TeX `manuscript_v2_proposed.tex` line 2203]): `d = 2`, `1 ≤ n ≤ 3`, or `3 ≤ d ≤ 10`, `1 ≤ n ≤ 21`. -/
def Pair171 (d n : ℕ) : Prop := (d = 2 ∧ 1 ≤ n ∧ n ≤ 3) ∨ (3 ≤ d ∧ d ≤ 10 ∧ 1 ≤ n ∧ n ≤ 21)

instance (d n : ℕ) : Decidable (Pair171 d n) := by unfold Pair171; infer_instance

theorem pair171_card :
    (((Finset.range 11 ×ˢ Finset.range 22).filter fun x => Pair171 x.1 x.2).card = 171) := by
  decide +kernel

theorem Pair171.range {d n : ℕ} (h : Pair171 d n) : 2 ≤ d ∧ d ≤ 10 ∧ 1 ≤ n ∧ n ≤ 21 := by
  unfold Pair171 at h
  omega

theorem gap_gt_three_tenths {d n : ℕ} (h : Pair171 d n) (hne : ¬ (d = 10 ∧ n = 21)) :
    (3 : ℚ) / 10 < gapQ d n := by
  obtain ⟨hd2, hd10, hn1, hn21⟩ := h.range
  have h' := h
  unfold Pair171 at h'
  rcases h' with ⟨rfl, h1, h3⟩ | ⟨hd3, _, _, _⟩
  · exact of_fin (P := fun n => (3 : ℚ) / 10 < gapQ 2 n) gap_d2 h1 h3
  · interval_cases d
    · exact of_fin (P := fun n => (3 : ℚ) / 10 < gapQ 3 n) gap_d3 hn1 hn21
    · exact of_fin (P := fun n => (3 : ℚ) / 10 < gapQ 4 n) gap_d4 hn1 hn21
    · exact of_fin (P := fun n => (3 : ℚ) / 10 < gapQ 5 n) gap_d5 hn1 hn21
    · exact of_fin (P := fun n => (3 : ℚ) / 10 < gapQ 6 n) gap_d6 hn1 hn21
    · exact of_fin (P := fun n => (3 : ℚ) / 10 < gapQ 7 n) gap_d7 hn1 hn21
    · exact of_fin (P := fun n => (3 : ℚ) / 10 < gapQ 8 n) gap_d8 hn1 hn21
    · exact of_fin (P := fun n => (3 : ℚ) / 10 < gapQ 9 n) gap_d9 hn1 hn21
    · exact of_fin (P := fun n => (3 : ℚ) / 10 < gapQ 10 n) gap_d10 hn1 (by omega)

/-- Legacy-weight margin: `162894/10^6 < gapQ d n` for all 171 pairs. -/
theorem gap_gt_all {d n : ℕ} (h : Pair171 d n) : (162894 : ℚ) / 10 ^ 6 < gapQ d n := by
  by_cases hne : d = 10 ∧ n = 21
  · obtain ⟨rfl, rfl⟩ := hne
    exact gap_10_21.1
  · exact lt_trans (by norm_num) (gap_gt_three_tenths h hne)

/-- **`eq:finite-scalar-rational-gap`** [TeX `manuscript_v2_proposed.tex` lines 2230-2235] (the rational comparison), with the least integer weights:
for each of the 171 pairs, `d H_n - ℓ_d^+ · (1/(B b^d)) [∑_{q=1}^{64} p_q U_q + U_65 (4^{dn} - ∑_{q=0}^{64} p_q)] > 4/25`. -/
theorem rational_gap_least {d n : ℕ} (h : Pair171 d n) :
    (4 : ℚ) / 25 < (d : ℚ) * harmonic n -
      couplingUpper d * retainedShellBound (leastUnit d) d n := by
  obtain ⟨hd2, hd10, hn1, hn21⟩ := h.range
  have hg := gap_gt_all h
  have hmono := retainedShellBound_mono hn1 hn21 d (leastUnit_le_RU hd2 (by omega))
  have heq := energyUpper_eq_bound hn1 hn21 d
  rw [energyUpper_eq_list] at heq
  have hcl : couplingUpper d = lambdaUpper d := by
    have := couplingUpper_eq_lambdaUpper ⟨d - 2, by omega⟩
    simpa [Nat.sub_add_cancel hd2] using this
  have hH : Legacy.D10.FiniteScalar.harmonic n = harmonic n := HighDim.LowScalar.harmonic_eq n
  unfold gapQ at hg
  rw [hH] at hg
  rw [hcl]
  have hl : 0 ≤ lambdaUpper d := by rw [← hcl]; exact couplingUpper_nonneg d
  have := mul_le_mul_of_nonneg_left hmono hl
  rw [← heq] at this
  linarith

/-- The real-valued comparison: for each of the 171 pairs, with `U_q = leastUnit d q`,
`4/25 < d H_n - ℓ_d^+ · bound ≤ d H_n - (2d/β_s(d)) G_{d,n}`. -/
theorem scalar_gap_171 {d n : ℕ} (h : Pair171 d n) :
    (4 : ℝ) / 25 < (d : ℝ) * (harmonic n : ℝ) -
        (couplingUpper d : ℝ) * (retainedShellBound (leastUnit d) d n : ℝ) ∧
      (d : ℝ) * (harmonic n : ℝ) - (couplingUpper d : ℝ) * (retainedShellBound (leastUnit d) d n : ℝ)
        ≤ (d : ℝ) * (harmonic n : ℝ) -
          (2 * (d : ℝ) / HighDim.spectralThreshold d) * HighDim.LowScalar.energy d n := by
  obtain ⟨hd2, hd10, hn1, hn21⟩ := h.range
  constructor
  · have := (Rat.cast_lt (K := ℝ)).2 (rational_gap_least h)
    push_cast at this
    exact this
  · have hE := energy_le_bound_least hn1 hn21 d
    have hE0 : 0 ≤ HighDim.LowScalar.energy d n := by
      rw [HighDim.LowScalar.energy_eq_legacy, ← LatticePolynomial.polynomialEnergy_eq_binomialEnergy]
      exact FiniteScalar.polynomialEnergy_nonneg d n
    have hcl : couplingUpper d = lambdaUpper d := by
      have := couplingUpper_eq_lambdaUpper ⟨d - 2, by omega⟩
      simpa [Nat.sub_add_cancel hd2] using this
    have he : 2 * (d : ℝ) / HighDim.spectralThreshold d = 2 * endpointConstant d := by
      unfold endpointConstant HighDim.spectralThreshold Legacy.TorusEndpoint.endpointSigma
      ring
    have hle : 2 * (d : ℝ) / HighDim.spectralThreshold d ≤ (couplingUpper d : ℝ) := by
      rw [he, hcl]
      by_cases h2 : d = 2
      · subst h2
        exact GaussianScalarTwoFinite.lambda_two_le_upper
      · exact twice_endpointConstant_le_lambdaUpper d (by omega) hd10
    have hl : (0 : ℝ) ≤ (couplingUpper d : ℝ) := by exact_mod_cast couplingUpper_nonneg d
    have h1 := mul_le_mul_of_nonneg_right hle hE0
    have h2 := mul_le_mul_of_nonneg_left hE hl
    linarith

/-- Corollary in the form of `eq:scalar-result` restricted to the 171 pairs, with the margin `4/25`
(instead of the printed `3/1100`): `d H_n - (2d/β_s(d)) G_{d,n} > 4/25 > 3/1100`. -/
theorem scalar_gap_171_direct {d n : ℕ} (h : Pair171 d n) :
    (4 : ℝ) / 25 < (d : ℝ) * (harmonic n : ℝ) -
      (2 * (d : ℝ) / HighDim.spectralThreshold d) * HighDim.LowScalar.energy d n :=
  lt_of_lt_of_le (scalar_gap_171 h).1 (scalar_gap_171 h).2

/-! ### Row S030: dimension eleven -/

/-- The right-hand side of `d11:eq:finite-rational-gap` without the margin:
`(3543·945)/(200·64·B b^{11}) (100000/314159)^5 [∑_{q=1}^{64} p_q U_q + U_65 (4^{11n} - ∑_{q=0}^{64} p_q)]`. -/
def d11Bound (U : ℕ → ℕ) (n : ℕ) : ℚ :=
  (3543 * 945 : ℚ) / (200 * 64 * (B : ℚ) * (b n : ℚ) ^ 11) * (100000 / 314159 : ℚ) ^ 5 *
    ((∑ q ∈ Icc 1 64, (p 11 n q : ℚ) * (U q : ℚ)) +
      (U 65 : ℚ) * ((4 : ℚ) ^ (11 * n) - ∑ q ∈ range 65, (p 11 n q : ℚ)))

theorem d11Bound_eq (U : ℕ → ℕ) (n : ℕ) :
    d11Bound U n = HighDim.Eleven.ScalarFinite.betaLambda * retainedShellBound U 11 n := by
  have hb : (b n : ℚ) ≠ 0 := by
    have : 0 < b n := Nat.choose_pos (by omega)
    exact_mod_cast this.ne'
  have hB : (B : ℚ) ≠ 0 := by norm_num [B]
  unfold d11Bound retainedShellBound HighDim.Eleven.ScalarFinite.betaLambda
  field_simp

/-- The constant of `d11:eq:finite-rational-gap` is `(β₀/22) ℓ_11^+`, `β₀ = 3543/200`
(text, `d11:eq:coupling-upper` and the sentence after it): `(3543/4400) ℓ_11^+ = (3543/200)(945/64)(100000/314159)^5`. -/
theorem d11_coupling_factor :
    (3543 : ℚ) / 4400 * couplingUpper 11 = 3543 / 200 * (945 / 64) * (100000 / 314159 : ℚ) ^ 5 ∧
      HighDim.Eleven.ScalarFinite.betaLambda = 3543 / 4400 * couplingUpper 11 := by
  have h : (3543 : ℚ) / 4400 * couplingUpper 11 = 3543 / 200 * (945 / 64) * (100000 / 314159 : ℚ) ^ 5 := by
    norm_num [couplingUpper, Nat.factorial]
  refine ⟨h, ?_⟩
  rw [h]
  norm_num [HighDim.Eleven.ScalarFinite.betaLambda]

/-- **`d11:eq:coupling-upper`** [TeX `manuscript_v2_proposed.tex` line 2692]. `β₀/β_s(11) < (3543/200)(945/64)(100000/314159)^5`. -/
theorem d11_coupling_upper :
    (3543 : ℝ) / 200 / HighDim.spectralThreshold 11 <
      3543 / 200 * (945 / 64) * (100000 / 314159 : ℝ) ^ 5 := by
  rw [HighDim.Eleven.spectralThreshold_eleven]
  have hp : (314159 / 100000 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have h5 : ((314159 : ℝ) / 100000) ^ 5 < Real.pi ^ 5 :=
    pow_lt_pow_left₀ hp (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < ((314159 : ℝ) / 100000) ^ 5 := by positivity
  have hc : (0 : ℝ) < 3543 / 200 * (945 / 64) := by norm_num
  have key : 1 / Real.pi ^ 5 < (100000 / 314159 : ℝ) ^ 5 := by
    have e : (100000 / 314159 : ℝ) ^ 5 = 1 / ((314159 : ℝ) / 100000) ^ 5 := by
      rw [one_div, ← inv_pow]; norm_num
    rw [e]
    exact one_div_lt_one_div_of_lt hpos h5
  have hpi : (0 : ℝ) < Real.pi ^ 5 := by positivity
  calc (3543 : ℝ) / 200 / (64 * Real.pi ^ 5 / 945)
      = 3543 / 200 * (945 / 64) * (1 / Real.pi ^ 5) := by field_simp
    _ < _ := mul_lt_mul_of_pos_left key hc

/-- **`d11:eq:finite-rational-gap`** [TeX `manuscript_v2_proposed.tex` lines 2697-2700], with the least integer weights and the margin `111/200000`
(which exceeds the printed `1/2000`), for `1 ≤ n ≤ 21`. -/
theorem d11_rational_gap {n : ℕ} (hn1 : 1 ≤ n) (hn21 : n ≤ 21) :
    (111 : ℚ) / 200000 < 11 * harmonic n - d11Bound (leastUnit 11) n := by
  have hg : (111 : ℚ) / 200000 < gapQ11 n := by
    by_cases h1 : n = 1
    · subst h1
      exact lt_trans (by norm_num) gap11_one.1
    · have := gap11_rest ⟨n - 2, by omega⟩
      simp only [Nat.sub_add_cancel (show 2 ≤ n by omega)] at this
      exact lt_trans (by norm_num) this
  have hmono := retainedShellBound_mono hn1 hn21 11 (leastUnit_le_RU (by norm_num) le_rfl)
  have heq := energyUpper_eq_bound hn1 hn21 11
  rw [energyUpper_eq_list] at heq
  have hH : Legacy.D10.FiniteScalar.harmonic n = harmonic n := HighDim.LowScalar.harmonic_eq n
  unfold gapQ11 at hg
  rw [hH] at hg
  rw [d11Bound_eq]
  have hl : 0 ≤ HighDim.Eleven.ScalarFinite.betaLambda := by
    norm_num [HighDim.Eleven.ScalarFinite.betaLambda]
  have := mul_le_mul_of_nonneg_left hmono hl
  rw [← heq] at this
  linarith

/-- Real-valued form: `11 H_n - (β₀/β_s) G_{11,n} ≥ 11 H_n - d11Bound > 111/200000 > 1/2000`
(`1 ≤ n ≤ 21`), where `G_{11,n}` is `Eleven.scalarEnergy n`. -/
theorem d11_scalar_gap_finite {n : ℕ} (hn1 : 1 ≤ n) (hn21 : n ≤ 21) :
    (111 : ℝ) / 200000 < 11 * (harmonic n : ℝ) - (d11Bound (leastUnit 11) n : ℝ) ∧
      11 * (harmonic n : ℝ) - (d11Bound (leastUnit 11) n : ℝ) ≤
        11 * (harmonic n : ℝ) - (3543 : ℝ) / 200 / HighDim.spectralThreshold 11 *
          HighDim.Eleven.scalarEnergy n := by
  constructor
  · have := (Rat.cast_lt (K := ℝ)).2 (d11_rational_gap hn1 hn21)
    push_cast at this
    exact this
  · have hE : HighDim.Eleven.scalarEnergy n ≤ (retainedShellBound (leastUnit 11) 11 n : ℝ) := by
      rw [HighDim.Eleven.ScalarFinite.scalarEnergy_eq_legacy, ← HighDim.LowScalar.energy_eq_legacy]
      exact energy_le_bound_least hn1 hn21 11
    have hE0 : 0 ≤ HighDim.Eleven.scalarEnergy n := by
      rw [HighDim.Eleven.ScalarFinite.scalarEnergy_eq_legacy,
        ← LatticePolynomial.polynomialEnergy_eq_binomialEnergy]
      exact FiniteScalar.polynomialEnergy_nonneg 11 n
    have hcoef := HighDim.Eleven.ScalarFinite.coefficient_le
    have hl : (0 : ℝ) ≤ (HighDim.Eleven.ScalarFinite.betaLambda : ℝ) := by
      norm_num [HighDim.Eleven.ScalarFinite.betaLambda]
    have h1 := mul_le_mul_of_nonneg_right hcoef hE0
    have h2 := mul_le_mul_of_nonneg_left hE hl
    have e : (d11Bound (leastUnit 11) n : ℝ) =
        (HighDim.Eleven.ScalarFinite.betaLambda : ℝ) *
          (retainedShellBound (leastUnit 11) 11 n : ℝ) := by
      rw [d11Bound_eq]; push_cast; ring
    rw [e]
    linarith

/-- `d11:eq:gap` on `1 ≤ n ≤ 21` with the margin `111/200000 > 1/2000`:
`11 H_n - (β₀/β_s) G_{11,n} > 111/200000`. -/
theorem d11_scalar_gap_finite_direct {n : ℕ} (hn1 : 1 ≤ n) (hn21 : n ≤ 21) :
    (111 : ℝ) / 200000 < 11 * (harmonic n : ℝ) - (3543 : ℝ) / 200 / HighDim.spectralThreshold 11 *
      HighDim.Eleven.scalarEnergy n ∧
    (1 : ℝ) / 2000 < 11 * (harmonic n : ℝ) - (3543 : ℝ) / 200 / HighDim.spectralThreshold 11 *
      HighDim.Eleven.scalarEnergy n := by
  have h := d11_scalar_gap_finite hn1 hn21
  have h1 := lt_of_lt_of_le h.1 h.2
  exact ⟨h1, lt_trans (by norm_num) h1⟩

end BecknerOnofri.V2.Reaudit.ShellMargins

end
