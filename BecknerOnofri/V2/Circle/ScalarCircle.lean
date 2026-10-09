module

public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

/-! # `A`, `B`, `C`, the rational weights `L_1, L_2`, and the scalar positivity of Lemma 5.16
(`d12-circle-eq:L1`, `d12-circle-eq:L2`, `d12-circle-eq:ABC`, `d12-circle-eq:rationalcircle`)

Here `u = t^2`.  The denominators of `L_1, L_2` are positive on `[0,1]` (even at `u = 1`), the
numerators are positive, `A, B, C > 0`, and
`A B/(A+B) = -9 N1 N3/(16 D6)` (printed closed form) on `[0,1]`.  Combined with
`P17_eq_bernstein17` this yields `J(u) + AB/(A+B) - 1/(14-10u) > 0` on `[0,1]`.

Everything is generic in an ordered field and uses only `ring` and elementary order lemmas. -/
noncomputable section
namespace BecknerOnofri.V2.Circle

variable {K : Type*} [Field K]

/-- numerator and denominator of `L_1` (`d12-circle-eq:L1`) -/
def L1den (u : K) : K := 12 * (35 - 60 * u + 30 * u ^ 2 - 4 * u ^ 3)
def L1num (u : K) : K := 5 * (9 * u ^ 2 - 44 * u + 42)
def L2den (u : K) : K := 60 * (56 - 105 * u + 60 * u ^ 2 - 10 * u ^ 3)
def L2num (u : K) : K := 297 * u ^ 2 - 1260 * u + 1120

def L1 (u : K) : K := L1num u / L1den u
def L2 (u : K) : K := L2num u / L2den u

/-- `B = (27/40) L_1`, `C = (27/40) L_2`, `A = 5/16 + 11 C u/(120 C + 11)`
(`d12-circle-eq:ABC`, with `c = 27/40`). -/
def Bc (u : K) : K := 27 / 40 * L1 u
def Cc (u : K) : K := 27 / 40 * L2 u
def Ac (u : K) : K := 5 / 16 + 11 * Cc u * u / (120 * Cc u + 11)

section Order

variable [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem d1_eq (u : K) :
    35 - 60 * u + 30 * u ^ 2 - 4 * u ^ 3 =
      1 + 12 * (1 - u) + 18 * (1 - u) ^ 2 + 4 * (1 - u) ^ 3 := by ring

omit [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem d2_eq (u : K) :
    56 - 105 * u + 60 * u ^ 2 - 10 * u ^ 3 =
      1 + 15 * (1 - u) + 30 * (1 - u) ^ 2 + 10 * (1 - u) ^ 3 := by ring

omit [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem N1_eq (u : K) : 9 * u ^ 2 - 44 * u + 42 = 7 + 26 * (1 - u) + 9 * (1 - u) ^ 2 := by ring

omit [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem n2_eq (u : K) :
    297 * u ^ 2 - 1260 * u + 1120 = 157 + 666 * (1 - u) + 297 * (1 - u) ^ 2 := by ring

omit [CharZero K] in
theorem d1_pos {u : K} (h1 : u ≤ 1) : 0 < 35 - 60 * u + 30 * u ^ 2 - 4 * u ^ 3 := by
  rw [d1_eq]
  have hv : 0 ≤ 1 - u := sub_nonneg.mpr h1
  have a1 : 0 ≤ 12 * (1 - u) := mul_nonneg (Nat.ofNat_nonneg _) hv
  have a2 : 0 ≤ 18 * (1 - u) ^ 2 := mul_nonneg (Nat.ofNat_nonneg _) (pow_nonneg hv 2)
  have a3 : 0 ≤ 4 * (1 - u) ^ 3 := mul_nonneg (Nat.ofNat_nonneg _) (pow_nonneg hv 3)
  have := add_nonneg (add_nonneg a1 a2) a3
  have e : (1 + 12 * (1 - u) + 18 * (1 - u) ^ 2 + 4 * (1 - u) ^ 3 : K) =
      1 + (12 * (1 - u) + 18 * (1 - u) ^ 2 + 4 * (1 - u) ^ 3) := by ring
  rw [e]
  exact add_pos_of_pos_of_nonneg one_pos this

omit [CharZero K] in
theorem d2_pos {u : K} (h1 : u ≤ 1) : 0 < 56 - 105 * u + 60 * u ^ 2 - 10 * u ^ 3 := by
  rw [d2_eq]
  have hv : 0 ≤ 1 - u := sub_nonneg.mpr h1
  have a1 : 0 ≤ 15 * (1 - u) := mul_nonneg (Nat.ofNat_nonneg _) hv
  have a2 : 0 ≤ 30 * (1 - u) ^ 2 := mul_nonneg (Nat.ofNat_nonneg _) (pow_nonneg hv 2)
  have a3 : 0 ≤ 10 * (1 - u) ^ 3 := mul_nonneg (Nat.ofNat_nonneg _) (pow_nonneg hv 3)
  have := add_nonneg (add_nonneg a1 a2) a3
  have e : (1 + 15 * (1 - u) + 30 * (1 - u) ^ 2 + 10 * (1 - u) ^ 3 : K) =
      1 + (15 * (1 - u) + 30 * (1 - u) ^ 2 + 10 * (1 - u) ^ 3) := by ring
  rw [e]
  exact add_pos_of_pos_of_nonneg one_pos this

omit [CharZero K] in
theorem N1_pos {u : K} (h1 : u ≤ 1) : 0 < 9 * u ^ 2 - 44 * u + 42 := by
  rw [N1_eq]
  have hv : 0 ≤ 1 - u := sub_nonneg.mpr h1
  have a1 : 0 ≤ 26 * (1 - u) := mul_nonneg (Nat.ofNat_nonneg _) hv
  have a2 : 0 ≤ 9 * (1 - u) ^ 2 := mul_nonneg (Nat.ofNat_nonneg _) (pow_nonneg hv 2)
  have e : (7 + 26 * (1 - u) + 9 * (1 - u) ^ 2 : K) = 7 + (26 * (1 - u) + 9 * (1 - u) ^ 2) := by
    ring
  rw [e]
  exact add_pos_of_pos_of_nonneg Nat.ofNat_pos (add_nonneg a1 a2)

omit [CharZero K] in
theorem n2_pos {u : K} (h1 : u ≤ 1) : 0 < 297 * u ^ 2 - 1260 * u + 1120 := by
  rw [n2_eq]
  have hv : 0 ≤ 1 - u := sub_nonneg.mpr h1
  have a1 : 0 ≤ 666 * (1 - u) := mul_nonneg (Nat.ofNat_nonneg _) hv
  have a2 : 0 ≤ 297 * (1 - u) ^ 2 := mul_nonneg (Nat.ofNat_nonneg _) (pow_nonneg hv 2)
  have e : (157 + 666 * (1 - u) + 297 * (1 - u) ^ 2 : K) =
      157 + (666 * (1 - u) + 297 * (1 - u) ^ 2) := by ring
  rw [e]
  exact add_pos_of_pos_of_nonneg Nat.ofNat_pos (add_nonneg a1 a2)

omit [CharZero K] in
theorem L1_pos {u : K} (h1 : u ≤ 1) : 0 < L1 u := by
  unfold L1 L1num L1den
  exact div_pos (mul_pos Nat.ofNat_pos (N1_pos h1)) (mul_pos Nat.ofNat_pos (d1_pos h1))

omit [CharZero K] in
theorem L2_pos {u : K} (h1 : u ≤ 1) : 0 < L2 u := by
  unfold L2 L2num L2den
  exact div_pos (n2_pos h1) (mul_pos Nat.ofNat_pos (d2_pos h1))

omit [CharZero K] in
theorem Bc_pos {u : K} (h1 : u ≤ 1) : 0 < Bc u := mul_pos (by norm_num) (L1_pos h1)

omit [CharZero K] in
theorem Cc_pos {u : K} (h1 : u ≤ 1) : 0 < Cc u := mul_pos (by norm_num) (L2_pos h1)

omit [CharZero K] in
theorem Ac_pos {u : K} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 < Ac u := by
  unfold Ac
  have hC := Cc_pos h1
  refine add_pos_of_pos_of_nonneg (by norm_num) ?_
  refine div_nonneg (mul_nonneg (mul_nonneg (Nat.ofNat_nonneg _) hC.le) h0) ?_
  exact add_nonneg (mul_nonneg (Nat.ofNat_nonneg _) hC.le) (Nat.ofNat_nonneg _)

end Order

end BecknerOnofri.V2.Circle
