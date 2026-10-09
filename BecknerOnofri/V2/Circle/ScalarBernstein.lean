module

public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

/-! # Scalar comparison of Lemma 5.16: the degree-seventeen unnormalized Bernstein identity
(`d12-circle-eq:baseexpand`, `d12-circle-eq:rationalcircle`, `d12-circle-eq:circleBern`,
Appendix B.2 table of `c_j`)

Everything here is a polynomial identity or an order statement about explicit polynomials.
`J` is the source's truncation (`k = 12`) of the series `d12-circle-eq:baseexpand`; its first three
coefficients are kept verbatim (they are NOT all nonnegative).  The Bernstein representation
`bernstein17` has NO binomial coefficients.

Contents.
* `D6`, `J`, `P17` (the polynomial `5140059724800 (5u-7) D6 [J + AB/(A+B) - 1/(14-10u)]` after
  clearing denominators with the printed closed form of `AB/(A+B)`);
* `P17_eq_bernstein17`: `P17 u = ∑ c_j u^j (1-u)^(17-j)` (exact, by `ring`);
* `D6_neg`, `bernstein17_pos`: sign statements on `[0,1]` (endpoint coefficient used explicitly).
The bridge from `A,B,C` to the printed closed form of `AB/(A+B)` is in `ScalarCircle.lean`. -/
noncomputable section
namespace BecknerOnofri.V2.Circle

variable {K : Type*} [Field K]

/-- `D_6` of Appendix A.2.3. -/
def D6 (u : K) : K :=
  30448 * u ^ 6 + 2910600 * u ^ 5 - 39002595 * u ^ 4 + 183644600 * u ^ 3
    - 398696760 * u ^ 2 + 404342400 * u - 154918400

/-- The coefficient `1/k * (247/1920 - 1/(2k-1))` times `u^m`, with `k` a numeral. -/
def tailTerm (k u : K) (m : ℕ) : K := 1 / k * (247 / 1920 - 1 / (2 * k - 1)) * u ^ m

/-- `J(u)`: the right side of `d12-circle-eq:baseexpand` truncated at `k = 12`.  The three initial
coefficients `-41/480`, `-31/1440`, `247/7680 - 1/28` are retained verbatim. -/
def J (u : K) : K :=
  -(41 / 480) - 31 / 1440 * u + (247 / 7680 - 1 / 28) * u ^ 2
    + tailTerm 5 u 3 + tailTerm 6 u 4 + tailTerm 7 u 5 + tailTerm 8 u 6
    + tailTerm 9 u 7 + tailTerm 10 u 8 + tailTerm 11 u 9 + tailTerm 12 u 10

/-- The constant `5140059724800` of `D(u) = 5140059724800 (5u-7) D_6(u)`. -/
def Kconst : K := 5140059724800

/-- Printed closed-form numerator factors in `AB/(A+B) = -9 N1 N3 / (16 D6)`. -/
def N1 (u : K) : K := 9 * u ^ 2 - 44 * u + 42
def N3 (u : K) : K := 3806 * u ^ 3 + 280995 * u ^ 2 - 1206240 * u + 1064000

/-- `P_17(u) = D(u) [J(u) + AB/(A+B) - 1/(14-10u)]`, with the printed value of `AB/(A+B)` and
`D(u)/(14-10u) = -K D6/2` inserted, i.e. all denominators cleared. -/
def P17 (u : K) : K :=
  Kconst * (5 * u - 7) * D6 u * J u - 9 * Kconst / 16 * ((5 * u - 7) * N1 u * N3 u)
    + Kconst / 2 * D6 u

/-- The unnormalized Bernstein form: eighteen positive integers, no binomial factors. -/
def bernstein17 (u : K) : K :=
  30179894941228032000 * u ^ 0 * (1 - u) ^ 17
    + 396106663529601024000 * u ^ 1 * (1 - u) ^ 16
    + 2390753510552475868800 * u ^ 2 * (1 - u) ^ 15
    + 8772257858545832851200 * u ^ 3 * (1 - u) ^ 14
    + 21777007448883210560400 * u ^ 4 * (1 - u) ^ 13
    + 38465600564557249421520 * u ^ 5 * (1 - u) ^ 12
    + 49389580532500238326950 * u ^ 6 * (1 - u) ^ 11
    + 46099205152060945922440 * u ^ 7 * (1 - u) ^ 10
    + 30562894382662930778330 * u ^ 8 * (1 - u) ^ 9
    + 13607965333758829372764 * u ^ 9 * (1 - u) ^ 8
    + 3765269021052516264167 * u ^ 10 * (1 - u) ^ 7
    + 977217579556228931452 * u ^ 11 * (1 - u) ^ 6
    + 832680376371621654129 * u ^ 12 * (1 - u) ^ 5
    + 653306534721186627290 * u ^ 13 * (1 - u) ^ 4
    + 283397678310840519901 * u ^ 14 * (1 - u) ^ 3
    + 68363981089534672488 * u ^ 15 * (1 - u) ^ 2
    + 8714996502104289223 * u ^ 16 * (1 - u) ^ 1
    + 459727754267332346 * u ^ 17 * (1 - u) ^ 0

variable [CharZero K]

/-- The exact polynomial identity `d12-circle-eq:circleBern`. -/
theorem P17_eq_bernstein17 (u : K) : P17 u = bernstein17 u := by
  unfold P17 bernstein17 Kconst D6 J tailTerm N1 N3
  ring


section Order

variable [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- `D_6(1-v) = -(…)` with all coefficients positive except the last, `-30448 v^6`. -/
theorem D6_eq_neg_poly_in_v (u : K) :
    D6 u = -(1689707 + 16607988 * (1 - u) + 52215810 * (1 - u) ^ 2 + 57349180 * (1 - u) ^ 3
      + 23992875 * (1 - u) ^ 4 + 3093288 * (1 - u) ^ 5 - 30448 * (1 - u) ^ 6) := by
  unfold D6
  ring

omit [CharZero K] in
/-- `D_6 < 0` on `[0,1]` (source: `v^6 ≤ v^5`, here `v^5 (3093288 - 30448 v) ≥ 0`). -/
theorem D6_neg {u : K} (h0 : 0 ≤ u) (h1 : u ≤ 1) : D6 u < 0 := by
  rw [D6_eq_neg_poly_in_v, neg_neg_iff_pos]
  have hv0 : 0 ≤ 1 - u := sub_nonneg.mpr h1
  have hv1 : 1 - u ≤ 1 := sub_le_self 1 h0
  have hlast : 0 ≤ (1 - u) ^ 5 * (3093288 - 30448 * (1 - u)) := by
    apply mul_nonneg (pow_nonneg hv0 5)
    have h2 : (30448 : K) * (1 - u) ≤ 30448 * 1 := mul_le_mul_of_nonneg_left hv1 (Nat.ofNat_nonneg _)
    have h3 : (30448 : K) * 1 ≤ 3093288 := by exact_mod_cast (by norm_num : (30448 : ℕ) * 1 ≤ 3093288)
    exact sub_nonneg.mpr (h2.trans h3)
  have e : (1689707 + 16607988 * (1 - u) + 52215810 * (1 - u) ^ 2 + 57349180 * (1 - u) ^ 3
      + 23992875 * (1 - u) ^ 4 + 3093288 * (1 - u) ^ 5 - 30448 * (1 - u) ^ 6 : K) =
      1689707 + (16607988 * (1 - u) + (52215810 * (1 - u) ^ 2 + (57349180 * (1 - u) ^ 3
      + (23992875 * (1 - u) ^ 4 + (1 - u) ^ 5 * (3093288 - 30448 * (1 - u)))))) := by ring
  rw [e]
  refine add_pos_of_pos_of_nonneg (Nat.ofNat_pos) ?_
  refine add_nonneg (mul_nonneg (Nat.ofNat_nonneg _) hv0) ?_
  refine add_nonneg (mul_nonneg (Nat.ofNat_nonneg _) (pow_nonneg hv0 2)) ?_
  refine add_nonneg (mul_nonneg (Nat.ofNat_nonneg _) (pow_nonneg hv0 3)) ?_
  exact add_nonneg (mul_nonneg (Nat.ofNat_nonneg _) (pow_nonneg hv0 4)) hlast

omit [CharZero K] in
/-- All eighteen Bernstein coefficients are positive; at each point of `[0,1]` either the term
`j = 0` (when `u < 1`) or the term `j = 17` (when `u = 1`) is strictly positive. -/
theorem bernstein17_pos {u : K} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 < bernstein17 u := by
  have hv0 : 0 ≤ 1 - u := sub_nonneg.mpr h1
  have key : ∀ (c : K) (j : ℕ), 0 ≤ c → 0 ≤ c * u ^ j * (1 - u) ^ (17 - j) := fun c j hc =>
    mul_nonneg (mul_nonneg hc (pow_nonneg h0 j)) (pow_nonneg hv0 _)
  have hends : 0 < (30179894941228032000 : K) * u ^ 0 * (1 - u) ^ 17
      + (459727754267332346 : K) * u ^ 17 * (1 - u) ^ 0 := by
    rcases lt_or_eq_of_le h1 with hlt | heq
    · have hp : 0 < (1 - u) ^ 17 := pow_pos (sub_pos.mpr hlt) 17
      have h17 := key (459727754267332346 : K) 17 (Nat.ofNat_nonneg _)
      have : 0 < (30179894941228032000 : K) * u ^ 0 * (1 - u) ^ 17 := by
        rw [pow_zero, mul_one]; exact mul_pos Nat.ofNat_pos hp
      exact add_pos_of_pos_of_nonneg this h17
    · have hu : u = 1 := heq
      have h0' := key (30179894941228032000 : K) 0 (Nat.ofNat_nonneg _)
      have : 0 < (459727754267332346 : K) * u ^ 17 * (1 - u) ^ 0 := by
        rw [hu]; simp
      exact add_pos_of_nonneg_of_pos h0' this
  have t1 := key (396106663529601024000 : K) 1 (Nat.ofNat_nonneg _)
  have t2 := key (2390753510552475868800 : K) 2 (Nat.ofNat_nonneg _)
  have t3 := key (8772257858545832851200 : K) 3 (Nat.ofNat_nonneg _)
  have t4 := key (21777007448883210560400 : K) 4 (Nat.ofNat_nonneg _)
  have t5 := key (38465600564557249421520 : K) 5 (Nat.ofNat_nonneg _)
  have t6 := key (49389580532500238326950 : K) 6 (Nat.ofNat_nonneg _)
  have t7 := key (46099205152060945922440 : K) 7 (Nat.ofNat_nonneg _)
  have t8 := key (30562894382662930778330 : K) 8 (Nat.ofNat_nonneg _)
  have t9 := key (13607965333758829372764 : K) 9 (Nat.ofNat_nonneg _)
  have t10 := key (3765269021052516264167 : K) 10 (Nat.ofNat_nonneg _)
  have t11 := key (977217579556228931452 : K) 11 (Nat.ofNat_nonneg _)
  have t12 := key (832680376371621654129 : K) 12 (Nat.ofNat_nonneg _)
  have t13 := key (653306534721186627290 : K) 13 (Nat.ofNat_nonneg _)
  have t14 := key (283397678310840519901 : K) 14 (Nat.ofNat_nonneg _)
  have t15 := key (68363981089534672488 : K) 15 (Nat.ofNat_nonneg _)
  have t16 := key (8714996502104289223 : K) 16 (Nat.ofNat_nonneg _)
  have s := add_nonneg t1 t2
  have s := add_nonneg s t3
  have s := add_nonneg s t4
  have s := add_nonneg s t5
  have s := add_nonneg s t6
  have s := add_nonneg s t7
  have s := add_nonneg s t8
  have s := add_nonneg s t9
  have s := add_nonneg s t10
  have s := add_nonneg s t11
  have s := add_nonneg s t12
  have s := add_nonneg s t13
  have s := add_nonneg s t14
  have s := add_nonneg s t15
  have s := add_nonneg s t16
  have e : bernstein17 u = ((30179894941228032000 : K) * u ^ 0 * (1 - u) ^ 17
      + (459727754267332346 : K) * u ^ 17 * (1 - u) ^ 0) + ((396106663529601024000 * u ^ 1 * (1 - u) ^ 16 : K) + (2390753510552475868800 * u ^ 2 * (1 - u) ^ 15 : K) + (8772257858545832851200 * u ^ 3 * (1 - u) ^ 14 : K) + (21777007448883210560400 * u ^ 4 * (1 - u) ^ 13 : K) + (38465600564557249421520 * u ^ 5 * (1 - u) ^ 12 : K) + (49389580532500238326950 * u ^ 6 * (1 - u) ^ 11 : K) + (46099205152060945922440 * u ^ 7 * (1 - u) ^ 10 : K) + (30562894382662930778330 * u ^ 8 * (1 - u) ^ 9 : K) + (13607965333758829372764 * u ^ 9 * (1 - u) ^ 8 : K) + (3765269021052516264167 * u ^ 10 * (1 - u) ^ 7 : K) + (977217579556228931452 * u ^ 11 * (1 - u) ^ 6 : K) + (832680376371621654129 * u ^ 12 * (1 - u) ^ 5 : K) + (653306534721186627290 * u ^ 13 * (1 - u) ^ 4 : K) + (283397678310840519901 * u ^ 14 * (1 - u) ^ 3 : K) + (68363981089534672488 * u ^ 15 * (1 - u) ^ 2 : K) + (8714996502104289223 * u ^ 16 * (1 - u) ^ 1 : K)) := by
    unfold bernstein17
    ring
  rw [e]
  exact add_pos_of_pos_of_nonneg hends s

end Order

end BecknerOnofri.V2.Circle
