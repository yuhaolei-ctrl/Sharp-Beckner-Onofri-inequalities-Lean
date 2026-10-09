module

public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

/-! # The degree-seven Bernstein polynomial of Appendix A.1 (`d12-tail-eq:Qtail`, `d12-tail-eq:tailBern`)

Exact transcription.  `tailQ x y` is `Q(x,y)`; `tailP y` is
`[(2+x)(2+3x)(2+5x) Q(x,y)]_{x=2(1-y)/9}` written with the three denominators cleared.
The Bernstein representation **includes** the binomial coefficients `C(7,j)`. -/
noncomputable section
namespace BecknerOnofri.V2.ThetaTail

variable {K : Type*} [Field K]

/-- `L(y)` from `(d12-tail-eq:expL)`. -/
def tailL (y : K) : K :=
  309 / 25 + 287 / 50 * y + 52 / 25 * y ^ 2 + 7 / 10 * y ^ 3 + 11 / 50 * y ^ 4

/-- the rational functions `a_1(x), a_2(x), a_3(x)` of the source. -/
def aRat1 (x : K) : K := (2 - x) / (2 + x)
def aRat2 (x : K) : K := (2 - x) * (2 - 3 * x) / ((2 + x) * (2 + 3 * x))
def aRat3 (x : K) : K :=
  (2 - x) * (2 - 3 * x) * (2 - 5 * x) / ((2 + x) * (2 + 3 * x) * (2 + 5 * x))

/-- `Q(x,y)` of `(d12-tail-eq:Qtail)`. -/
def tailQ (x y : K) : K :=
  81 / 10 * (577 / 1000) - 77 / 1000 + 11 / 125 * (3 / 2 + y)
    - 81 / 5 * aRat1 x - 15 / 2 * aRat2 x - 11 / 5 * aRat3 x
    - 3111 / 800 * x + 27 / 100 * x ^ 2 - x ^ 4 / 216 + tailL y

/-- numerator after multiplying `Q` by `(2+x)(2+3x)(2+5x)` -/
def tailPxy (x y : K) : K :=
  (2 + x) * (2 + 3 * x) * (2 + 5 * x) *
      (81 / 10 * (577 / 1000) - 77 / 1000 + 11 / 125 * (3 / 2 + y)
        - 3111 / 800 * x + 27 / 100 * x ^ 2 - x ^ 4 / 216 + tailL y)
    - 81 / 5 * ((2 - x) * (2 + 3 * x) * (2 + 5 * x))
    - 15 / 2 * ((2 - x) * (2 - 3 * x) * (2 + 5 * x))
    - 11 / 5 * ((2 - x) * (2 - 3 * x) * (2 - 5 * x))

/-- `P(y)`. -/
def tailP (y : K) : K := tailPxy (2 * (1 - y) / 9) y

/-- The Bernstein sum `∑_{j=0}^7 β_j C(7,j) y^j (1-y)^(7-j)` with the printed `β_j`
(`β_0..β_7 = 2621600384/5380840125, 56482623256/62776468125, 2871236822/2325054375,
1147632568/775018125, 3433001/2126250, 93671/60750, 1383/1250, 167/1250`);
the binomial coefficients `1,7,21,35,35,21,7,1` are written out. -/
def tailBernsteinSum (y : K) : K :=
  (2621600384 / 5380840125) * (1 - y) ^ 7
    + (56482623256 / 62776468125) * 7 * y * (1 - y) ^ 6
    + (2871236822 / 2325054375) * 21 * y ^ 2 * (1 - y) ^ 5
    + (1147632568 / 775018125) * 35 * y ^ 3 * (1 - y) ^ 4
    + (3433001 / 2126250) * 35 * y ^ 4 * (1 - y) ^ 3
    + (93671 / 60750) * 21 * y ^ 5 * (1 - y) ^ 2
    + (1383 / 1250) * 7 * y ^ 6 * (1 - y) + (167 / 1250) * y ^ 7

/-- The exact identity `(d12-tail-eq:tailBern)`. -/
theorem tailP_eq_bernstein [CharZero K] (y : K) : tailP y = tailBernsteinSum y := by
  unfold tailP tailPxy tailBernsteinSum tailL
  ring

/-- Clearing denominators: `(2+x)(2+3x)(2+5x) Q(x,y) = tailPxy x y`. -/
theorem tailQ_mul_den [CharZero K] (x y : K) (h1 : (2 + x) ≠ 0) (h2 : (2 + 3 * x) ≠ 0)
    (h3 : (2 + 5 * x) ≠ 0) :
    (2 + x) * (2 + 3 * x) * (2 + 5 * x) * tailQ x y = tailPxy x y := by
  have f1 : aRat1 x * (2 + x) = 2 - x := div_mul_cancel₀ _ h1
  have f2 : aRat2 x * ((2 + x) * (2 + 3 * x)) = (2 - x) * (2 - 3 * x) :=
    div_mul_cancel₀ _ (mul_ne_zero h1 h2)
  have f3 : aRat3 x * ((2 + x) * (2 + 3 * x) * (2 + 5 * x)) = (2 - x) * (2 - 3 * x) * (2 - 5 * x) :=
    div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero h1 h2) h3)
  unfold tailQ tailPxy
  generalize aRat1 x = u1 at f1 ⊢
  generalize aRat2 x = u2 at f2 ⊢
  generalize aRat3 x = u3 at f3 ⊢
  have key : (2 + x) * (2 + 3 * x) * (2 + 5 * x) *
        (81 / 10 * (577 / 1000) - 77 / 1000 + 11 / 125 * (3 / 2 + y) - 81 / 5 * u1 - 15 / 2 * u2
          - 11 / 5 * u3 - 3111 / 800 * x + 27 / 100 * x ^ 2 - x ^ 4 / 216 + tailL y)
      - ((2 + x) * (2 + 3 * x) * (2 + 5 * x) *
          (81 / 10 * (577 / 1000) - 77 / 1000 + 11 / 125 * (3 / 2 + y)
            - 3111 / 800 * x + 27 / 100 * x ^ 2 - x ^ 4 / 216 + tailL y)
        - 81 / 5 * ((2 - x) * (2 + 3 * x) * (2 + 5 * x))
        - 15 / 2 * ((2 - x) * (2 - 3 * x) * (2 + 5 * x))
        - 11 / 5 * ((2 - x) * (2 - 3 * x) * (2 - 5 * x)))
      = -(81 / 5 : K) * ((2 + 3 * x) * (2 + 5 * x)) * (u1 * (2 + x) - (2 - x))
        - (15 / 2 : K) * (2 + 5 * x) * (u2 * ((2 + x) * (2 + 3 * x)) - (2 - x) * (2 - 3 * x))
        - (11 / 5 : K) * (u3 * ((2 + x) * (2 + 3 * x) * (2 + 5 * x))
            - (2 - x) * (2 - 3 * x) * (2 - 5 * x)) := by
    ring
  rw [f1, f2, f3] at key
  have key' := sub_eq_zero.mp (key.trans (by ring))
  exact key'

section Positivity

variable [LinearOrder K] [IsStrictOrderedRing K]

private lemma ofNat_div_nonneg (a b : ℕ) [a.AtLeastTwo] [b.AtLeastTwo] :
    (0 : K) ≤ (OfNat.ofNat a : K) / (OfNat.ofNat b : K) :=
  div_nonneg (Nat.ofNat_nonneg _) (Nat.ofNat_nonneg _)

private lemma ofNat_div_pos (a b : ℕ) [a.AtLeastTwo] [b.AtLeastTwo] :
    (0 : K) < (OfNat.ofNat a : K) / (OfNat.ofNat b : K) :=
  div_pos (Nat.ofNat_pos) (Nat.ofNat_pos)

private lemma bterm_nonneg (c y z : K) (i j : ℕ) (hc : 0 ≤ c) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ c * y ^ i * z ^ j :=
  mul_nonneg (mul_nonneg hc (pow_nonneg hy _)) (pow_nonneg hz _)

/-- `P > 0` on `[0,1]` once every Bernstein coefficient is positive
(`all eight β_j > 0` is exactly what the source prints). -/
theorem tailBernsteinSum_pos (y : K) (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 < tailBernsteinSum y := by
  have hz : 0 ≤ 1 - y := sub_nonneg.2 h1
  have n1 := bterm_nonneg (56482623256 / 62776468125 * 7 : K) y (1 - y) 1 6 (mul_nonneg (ofNat_div_nonneg _ _) (Nat.ofNat_nonneg _)) h0 hz
  have n2 := bterm_nonneg (2871236822 / 2325054375 * 21 : K) y (1 - y) 2 5 (mul_nonneg (ofNat_div_nonneg _ _) (Nat.ofNat_nonneg _)) h0 hz
  have n3 := bterm_nonneg (1147632568 / 775018125 * 35 : K) y (1 - y) 3 4 (mul_nonneg (ofNat_div_nonneg _ _) (Nat.ofNat_nonneg _)) h0 hz
  have n4 := bterm_nonneg (3433001 / 2126250 * 35 : K) y (1 - y) 4 3 (mul_nonneg (ofNat_div_nonneg _ _) (Nat.ofNat_nonneg _)) h0 hz
  have n5 := bterm_nonneg (93671 / 60750 * 21 : K) y (1 - y) 5 2 (mul_nonneg (ofNat_div_nonneg _ _) (Nat.ofNat_nonneg _)) h0 hz
  have n6 := bterm_nonneg (1383 / 1250 * 7 : K) y (1 - y) 6 1 (mul_nonneg (ofNat_div_nonneg _ _) (Nat.ofNat_nonneg _)) h0 hz
  have e0 : 0 ≤ (2621600384 / 5380840125 : K) * (1 - y) ^ 7 :=
    mul_nonneg (ofNat_div_nonneg _ _) (pow_nonneg hz _)
  have e7 : 0 ≤ (167 / 1250 : K) * y ^ 7 := mul_nonneg (ofNat_div_nonneg _ _) (pow_nonneg h0 _)
  have key : tailBernsteinSum y =
      (2621600384 / 5380840125 : K) * (1 - y) ^ 7 + (167 / 1250 : K) * y ^ 7
      + (56482623256 / 62776468125 * 7 * y ^ 1 * (1 - y) ^ 6
        + 2871236822 / 2325054375 * 21 * y ^ 2 * (1 - y) ^ 5
        + 1147632568 / 775018125 * 35 * y ^ 3 * (1 - y) ^ 4
        + 3433001 / 2126250 * 35 * y ^ 4 * (1 - y) ^ 3
        + 93671 / 60750 * 21 * y ^ 5 * (1 - y) ^ 2
        + 1383 / 1250 * 7 * y ^ 6 * (1 - y) ^ 1) := by
    unfold tailBernsteinSum; ring
  have hrest : 0 ≤ 56482623256 / 62776468125 * 7 * y ^ 1 * (1 - y) ^ 6
        + 2871236822 / 2325054375 * 21 * y ^ 2 * (1 - y) ^ 5
        + 1147632568 / 775018125 * 35 * y ^ 3 * (1 - y) ^ 4
        + 3433001 / 2126250 * 35 * y ^ 4 * (1 - y) ^ 3
        + 93671 / 60750 * 21 * y ^ 5 * (1 - y) ^ 2
        + 1383 / 1250 * 7 * y ^ 6 * (1 - y) ^ 1 :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg n1 n2) n3) n4) n5) n6
  rw [key]
  have hmain : 0 < (2621600384 / 5380840125 : K) * (1 - y) ^ 7 + (167 / 1250 : K) * y ^ 7 := by
    rcases le_or_gt y (1 / 2) with hy | hy
    · have hz2 : (1 / 2 : K) ≤ 1 - y := by
        have := sub_le_sub_left hy 1
        have h12 : (1 : K) - 1 / 2 = 1 / 2 := by norm_num
        rwa [h12] at this
      have hp : (1 / 2 : K) ^ 7 ≤ (1 - y) ^ 7 := pow_le_pow_left₀ (one_div_nonneg.2 (Nat.ofNat_nonneg 2)) hz2 7
      have hpos : 0 < (2621600384 / 5380840125 : K) * (1 - y) ^ 7 :=
        mul_pos (ofNat_div_pos _ _) (lt_of_lt_of_le (pow_pos (one_div_pos.2 Nat.ofNat_pos) 7) hp)
      exact add_pos_of_pos_of_nonneg hpos e7
    · have hp : (1 / 2 : K) ^ 7 ≤ y ^ 7 := pow_le_pow_left₀ (one_div_nonneg.2 (Nat.ofNat_nonneg 2)) hy.le 7
      have hpos : 0 < (167 / 1250 : K) * y ^ 7 :=
        mul_pos (ofNat_div_pos _ _) (lt_of_lt_of_le (pow_pos (one_div_pos.2 Nat.ofNat_pos) 7) hp)
      exact add_pos_of_nonneg_of_pos e0 hpos
  exact add_pos_of_pos_of_nonneg hmain hrest

/-- `Q(x,y) > 0` for `y ∈ [0,1]` and `x = 2(1-y)/9`: the end of `(d12-tail-eq:Qtail)`–`(d12-tail-eq:tailBern)`. -/
theorem tailQ_pos (y : K) (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 < tailQ (2 * (1 - y) / 9) y := by
  have hz : 0 ≤ 1 - y := sub_nonneg.2 h1
  have hx : 0 ≤ 2 * (1 - y) / 9 := div_nonneg (mul_nonneg (Nat.ofNat_nonneg 2) hz) (Nat.ofNat_nonneg 9)
  have p1 : 0 < 2 + 2 * (1 - y) / 9 := add_pos_of_pos_of_nonneg Nat.ofNat_pos hx
  have p2 : 0 < 2 + 3 * (2 * (1 - y) / 9) :=
    add_pos_of_pos_of_nonneg Nat.ofNat_pos (mul_nonneg (Nat.ofNat_nonneg 3) hx)
  have p3 : 0 < 2 + 5 * (2 * (1 - y) / 9) :=
    add_pos_of_pos_of_nonneg Nat.ofNat_pos (mul_nonneg (Nat.ofNat_nonneg 5) hx)
  have hden := mul_pos (mul_pos p1 p2) p3
  have hmul := tailQ_mul_den (2 * (1 - y) / 9) y p1.ne' p2.ne' p3.ne'
  have hP : 0 < (2 + 2 * (1 - y) / 9) * (2 + 3 * (2 * (1 - y) / 9)) * (2 + 5 * (2 * (1 - y) / 9)) *
      tailQ (2 * (1 - y) / 9) y := by
    rw [hmul]
    have := tailBernsteinSum_pos y h0 h1
    rw [← tailP_eq_bernstein y] at this
    exact this
  exact (mul_pos_iff_of_pos_left hden).1 hP

end Positivity

end BecknerOnofri.V2.ThetaTail
