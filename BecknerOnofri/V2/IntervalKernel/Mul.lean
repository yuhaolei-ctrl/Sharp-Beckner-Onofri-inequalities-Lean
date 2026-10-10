module

public import BecknerOnofri.V2.IntervalKernel.Pack

@[expose] public section

/-!
# Scalar kernel arithmetic: biased interval multiplication

`fmul` multiplies two intervals whose endpoints are biased naturals (`v + B`), exactly as
`Iv.mul` does (all four products, minimum/maximum, rounding down/up by `2^110`), but using only
`Nat` primitives.  The result endpoints are biased by `C0 = B^2 / 2^110` (a *product bias*, so that
no natural subtraction can truncate).
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

/-- The integer denoted by a biased natural. -/
def dec (n : Nat) : Int := (n : Int) - (B : Int)

@[inline] def nmin (a b : Nat) : Nat := bif Nat.ble a b then a else b
@[inline] def nmax (a b : Nat) : Nat := bif Nat.ble a b then b else a

theorem ble_iff {a b : Nat} : Nat.ble a b = true ↔ a ≤ b := Iff.of_eq Nat.ble_eq

theorem nmin_cast (a b : Nat) : ((nmin a b : Nat) : Int) = min (a : Int) b := by
  unfold nmin
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hh => by have := ble_iff.2 hh; simp_all
    simp only [Bool.cond_false]; omega
  · have : a ≤ b := ble_iff.1 h
    simp only [Bool.cond_true]; omega

theorem nmax_cast (a b : Nat) : ((nmax a b : Nat) : Int) = max (a : Int) b := by
  unfold nmax
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hh => by have := ble_iff.2 hh; simp_all
    simp only [Bool.cond_false]; omega
  · have : a ≤ b := ble_iff.1 h
    simp only [Bool.cond_true]; omega

/-- `(a - B) (b - B) + B^2`, computed without truncation. -/
def pp (a b : Nat) : Nat := Nat.sub (Nat.add (Nat.mul a b) K2) (Nat.mul B (Nat.add a b))

theorem pp_cast {a b : Nat} (ha : a ≤ TWOB) (hb : b ≤ TWOB) :
    ((pp a b : Nat) : Int) = dec a * dec b + (B : Int) * B := by
  have ha' : (a : Int) ≤ 2 * B := by rw [TWOB_eq] at ha; exact_mod_cast ha
  have hb' : (b : Int) ≤ 2 * B := by rw [TWOB_eq] at hb; exact_mod_cast hb
  have hB : (0 : Int) ≤ B := by positivity
  have hle : B * (a + b) ≤ a * b + K2 := by
    have : ((B * (a + b) : Nat) : Int) ≤ ((a * b + K2 : Nat) : Int) := by
      push_cast
      rw [K2_eq]; push_cast
      nlinarith [mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hb'), Nat.cast_nonneg (α := Int) a,
        Nat.cast_nonneg (α := Int) b, mul_nonneg (Nat.cast_nonneg (α := Int) a) (Nat.cast_nonneg (α := Int) b)]
    exact_mod_cast this
  unfold pp dec
  simp only [Nat.sub_eq, Nat.add_eq, Nat.mul_eq]
  rw [Nat.cast_sub hle]
  push_cast
  rw [K2_eq]; push_cast
  ring

/-- Product of two biased intervals: `(lo, hi)` biased by `C0`. -/
def fmul (al ah bl bh : Nat) : Nat × Nat :=
  let p1 := pp al bl
  let p2 := pp al bh
  let p3 := pp ah bl
  let p4 := pp ah bh
  (Nat.shiftRight (nmin (nmin p1 p2) (nmin p3 p4)) 110,
   Nat.shiftRight (Nat.add (nmax (nmax p1 p2) (nmax p3 p4)) S110m1) 110)

theorem scale_eq : scale = (S110 : Int) := by
  unfold scale S110; norm_num

theorem fmul_spec {al ah bl bh : Nat} (h1 : al ≤ TWOB) (h2 : ah ≤ TWOB) (h3 : bl ≤ TWOB)
    (h4 : bh ≤ TWOB) :
    (((fmul al ah bl bh).1 : Nat) : Int) = (Iv.mul ⟨dec al, dec ah⟩ ⟨dec bl, dec bh⟩).lo + C0 ∧
    (((fmul al ah bl bh).2 : Nat) : Int) = (Iv.mul ⟨dec al, dec ah⟩ ⟨dec bl, dec bh⟩).hi + C0 := by
  have e1 := pp_cast h1 h3
  have e2 := pp_cast h1 h4
  have e3 := pp_cast h2 h3
  have e4 := pp_cast h2 h4
  have hC : (B : Int) * B = (C0 : Int) * S110 := by
    have := C0_eq; exact_mod_cast this.symm
  have hS : (0 : Int) < S110 := by unfold S110; norm_num
  unfold fmul Iv.mul
  simp only [fdiv, cdiv, scale_eq]
  have hsh : ∀ n : Nat, Nat.shiftRight n 110 = n / S110 := by
    intro n
    have : n >>> 110 = n / 2 ^ 110 := Nat.shiftRight_eq_div_pow n 110
    rw [S110_eq]
    exact this
  generalize pp al bl = P1 at *
  generalize pp al bh = P2 at *
  generalize pp ah bl = P3 at *
  generalize pp ah bh = P4 at *
  generalize dec al * dec bl = p1 at *
  generalize dec al * dec bh = p2 at *
  generalize dec ah * dec bl = p3 at *
  generalize dec ah * dec bh = p4 at *
  have key : ∀ m : Int, (m + (S110m1 : Int)) / S110 = -((-m) / S110) := by
    intro m; unfold S110 S110m1; push_cast; omega
  generalize hK : (C0 : Int) * S110 = K at hC
  constructor
  · rw [hsh, Int.natCast_div, nmin_cast, nmin_cast, nmin_cast]
    have hm : min (min (P1 : Int) P2) (min (P3 : Int) P4)
        = min (min p1 p2) (min p3 p4) + (C0 : Int) * S110 := by
      rw [hK, ← hC, e1, e2, e3, e4]; omega
    rw [hm, Int.add_mul_ediv_right _ _ (ne_of_gt hS)]
  · rw [hsh, Int.natCast_div]
    simp only [Nat.add_eq]
    push_cast
    rw [nmax_cast, nmax_cast, nmax_cast]
    have hm : max (max (P1 : Int) P2) (max (P3 : Int) P4)
        = max (max p1 p2) (max p3 p4) + (C0 : Int) * S110 := by
      rw [hK, ← hC, e1, e2, e3, e4]; omega
    rw [hm, add_right_comm, Int.add_mul_ediv_right _ _ (ne_of_gt hS), key]

end BecknerOnofri.V2.IntervalKernel
