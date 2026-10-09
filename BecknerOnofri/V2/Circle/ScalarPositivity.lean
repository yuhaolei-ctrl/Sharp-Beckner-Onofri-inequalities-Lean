module

public import Mathlib.Tactic
public import BecknerOnofri.V2.Circle.ScalarBernstein
public import BecknerOnofri.V2.Circle.ScalarCircle

@[expose] public section

/-! # Scalar positivity of Lemma 5.16 (`d12-circle-eq:rationalcircle`)

With `A, B, C` the actual quantities of `d12-circle-eq:ABC` (`Ac, Bc, Cc` of `ScalarCircle`), the
printed closed form
`AB/(A+B) = -9 (9u²-44u+42)(3806u³+280995u²-1206240u+1064000) / (16 D_6(u))`
holds on `[0,1]`, and then
`J(u) + AB/(A+B) - 1/(14-10u) > 0` on `[0,1]`: multiplying by the positive
`D(u) = 5140059724800 (5u-7) D_6(u)` gives the unnormalized Bernstein polynomial `P_17`.
All statements are generic in an ordered field and used at `K = ℝ`. -/
noncomputable section
namespace BecknerOnofri.V2.Circle

variable {K : Type*} [Field K] [CharZero K]

/-- `E(u) = 27 n₂(u) + 220 d₂(u) = 42560 - 57120u + 21219u² - 2200u³`. -/
def Eden (u : K) : K :=
  27 * (297 * u ^ 2 - 1260 * u + 1120) + 220 * (56 - 105 * u + 60 * u ^ 2 - 10 * u ^ 3)

theorem Ac_abstract (n d E u : K) (hd : d ≠ 0) (hE : E ≠ 0) (hEd : E = 27 * n + 220 * d) :
    5 / 16 + 11 * (9 * n / (800 * d)) * u / (120 * (9 * n / (800 * d)) + 11) =
      (25 * E + 198 * n * u) / (80 * E) := by
  have h2 : (120 * (9 * n / (800 * d)) + 11 : K) = E / (20 * d) := by
    rw [hEd]; field_simp; ring
  rw [h2]
  field_simp
  rw [hEd]; ring

theorem AB_abstract (a b E d : K) (hE : E ≠ 0) (hd : d ≠ 0) :
    a / (80 * E) * (b / (32 * d)) / (a / (80 * E) + b / (32 * d)) =
      a * b / (32 * d * a + 80 * E * b) := by
  have hsum : a / (80 * E) + b / (32 * d) = (32 * d * a + 80 * E * b) / (80 * E * (32 * d)) := by
    field_simp
  rw [hsum, div_mul_div_comm]
  field_simp

section Order

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem Eden_pos {u : K} (h1 : u ≤ 1) : 0 < Eden u :=
  add_pos (mul_pos (by norm_num) (n2_pos h1)) (mul_pos (by norm_num) (d2_pos h1))

/-- `B = (27/40) L_1 = 9 N₁ / (32 d₁)`. -/
theorem Bc_eq {u : K} (h1 : u ≤ 1) :
    Bc u = 9 * (9 * u ^ 2 - 44 * u + 42) / (32 * (35 - 60 * u + 30 * u ^ 2 - 4 * u ^ 3)) := by
  have hd1 := (d1_pos h1).ne'
  unfold Bc L1 L1num L1den
  field_simp
  ring

/-- `C = (27/40) L_2 = 9 n₂ / (800 d₂)`. -/
theorem Cc_eq {u : K} (h1 : u ≤ 1) :
    Cc u = 9 * (297 * u ^ 2 - 1260 * u + 1120) / (800 * (56 - 105 * u + 60 * u ^ 2 - 10 * u ^ 3)) := by
  have hd2 := (d2_pos h1).ne'
  unfold Cc L2 L2num L2den
  field_simp
  ring

/-- `A = (25 E + 198 n₂ u)/(80 E)`. -/
theorem Ac_eq {u : K} (h1 : u ≤ 1) :
    Ac u = (25 * Eden u + 198 * (297 * u ^ 2 - 1260 * u + 1120) * u) / (80 * Eden u) := by
  have hd2 := (d2_pos h1).ne'
  have hE := (Eden_pos h1).ne'
  unfold Ac
  rw [Cc_eq h1]
  exact Ac_abstract _ _ _ _ hd2 hE rfl

/-- The printed closed form of `AB/(A+B)` (Appendix A.2.3). -/
theorem AB_closed {u : K} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Ac u * Bc u / (Ac u + Bc u) = -9 * N1 u * N3 u / (16 * D6 u) := by
  have hd1 := (d1_pos h1).ne'
  have hE := (Eden_pos h1).ne'
  have hD6 := (D6_neg h0 h1).ne
  have hN1 : 0 < N1 u := N1_pos h1
  have hA : 0 < Ac u := Ac_pos h0 h1
  have hB : 0 < Bc u := Bc_pos h1
  rw [Ac_eq h1, Bc_eq h1] at *
  rw [AB_abstract _ _ _ _ hE hd1]
  have hs : 32 * (35 - 60 * u + 30 * u ^ 2 - 4 * u ^ 3) *
        (25 * Eden u + 198 * (297 * u ^ 2 - 1260 * u + 1120) * u) +
      80 * Eden u * (9 * (9 * u ^ 2 - 44 * u + 42)) ≠ 0 := by
    have hn2 := n2_pos h1
    have hEp := Eden_pos h1
    have hd1p := d1_pos h1
    have : 0 < 32 * (35 - 60 * u + 30 * u ^ 2 - 4 * u ^ 3) *
        (25 * Eden u + 198 * (297 * u ^ 2 - 1260 * u + 1120) * u) +
      80 * Eden u * (9 * (9 * u ^ 2 - 44 * u + 42)) := by
      have h3 : 0 < 25 * Eden u + 198 * (297 * u ^ 2 - 1260 * u + 1120) * u :=
        add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hEp)
          (mul_nonneg (mul_nonneg (by norm_num) hn2.le) h0)
      exact add_pos (mul_pos (mul_pos (by norm_num) hd1p) h3)
        (mul_pos (mul_pos (by norm_num) hEp) (mul_pos (by norm_num) hN1))
    exact this.ne'
  rw [div_eq_div_iff hs (mul_ne_zero (by norm_num) hD6)]
  unfold N1 N3 D6 Eden
  ring

/-- The scalar comparison `d12-circle-eq:rationalcircle`, with the actual `A,B` of
`d12-circle-eq:ABC`: `J(u) + AB/(A+B) - 1/(14-10u) > 0` for `0 ≤ u ≤ 1`. -/
theorem scalar_positivity {u : K} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 < J u + Ac u * Bc u / (Ac u + Bc u) - 1 / (14 - 10 * u) := by
  rw [AB_closed h0 h1]
  have hD6 := D6_neg h0 h1
  have h5 : 5 * u - 7 < 0 := by linarith
  have h14 : (14 - 10 * u : K) = -2 * (5 * u - 7) := by ring
  have h14' : (14 - 10 * u : K) ≠ 0 := by rw [h14]; nlinarith
  have hK : (0 : K) < Kconst := by unfold Kconst; norm_num
  have hDpos : 0 < Kconst * (5 * u - 7) * D6 u :=
    mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hK h5) hD6
  have key : (Kconst * (5 * u - 7) * D6 u) *
      (J u + -9 * N1 u * N3 u / (16 * D6 u) - 1 / (14 - 10 * u)) = bernstein17 u := by
    rw [← P17_eq_bernstein17]
    unfold P17
    rw [h14]
    have h5' : (5 * u - 7 : K) ≠ 0 := h5.ne
    have hD6' : D6 u ≠ 0 := hD6.ne
    field_simp
    ring
  have hP := bernstein17_pos h0 h1
  rw [← key] at hP
  exact (mul_pos_iff_of_pos_left hDpos).mp hP

end Order

end BecknerOnofri.V2.Circle
