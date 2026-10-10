module

public import Mathlib.Tactic
public import BecknerOnofri.V2.Interval.Check

@[expose] public section

/-!
# Kernel-friendly packed registers (IntervalKernel)

A register of the interval interpreter is a centred jet (`mid`, `box`), i.e. `28` integers.  Here it
is stored as ONE natural number: field `i` (`i < 28`) occupies bits `[256 i, 256 (i+1))` and holds the
*biased* value `v + B`, `B = 2^240`, of the integer `v` (admissible range `0 ≤ v + B ≤ 2 B`).  Natural
number literals are the only data on which the Lean kernel computes quickly (GMP), so every hot
loop of the checker is expressed with `Nat.add/sub/mul/shiftRight/ble` on such literals.

Field order: `mid` entries `0..6` (`lo`, `hi` each), then `box` entries `0..6`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

/-- `2^110` (the scale of the interval arithmetic). -/
def S110 : Nat := 1298074214633706907132624082305024
/-- `2^110 - 1`. -/
def S110m1 : Nat := 1298074214633706907132624082305023
/-- The bias `2^240`. -/
def B : Nat := 1766847064778384329583297500742918515827483896875618958121606201292619776
/-- `2 B = 2^241`: the largest admissible biased field. -/
def TWOB : Nat := 3533694129556768659166595001485837031654967793751237916243212402585239552
/-- `2 B^2 = 2^481`. -/
def K2 : Nat := 6243497100631984462763194459586332611497196285329942301718313919250743477639531240240612206126983942319653862242813245790895951358576570612580352
/-- `B^2 / 2^110 = 2^370`: the bias of a rounded product. -/
def C0 : Nat := 2404907604760405225358828131112281116032698930082119547604265954848982041717359046106827774346003151904701415424
/-- `2^256`: the field width. -/
def TWO256 : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936

theorem S110_eq : S110 = 2 ^ 110 := by norm_num [S110]
theorem S110m1_eq : S110m1 = 2 ^ 110 - 1 := by norm_num [S110m1]
theorem B_eq : B = 2 ^ 240 := by norm_num [B]
theorem TWOB_eq : TWOB = 2 * B := by norm_num [TWOB, B]
theorem K2_eq : K2 = 2 * B * B := by norm_num [K2, B]
theorem C0_eq : C0 * S110 = B * B := by norm_num [C0, S110, B]
theorem TWO256_eq : TWO256 = 2 ^ 256 := by norm_num [TWO256]

/-! ### Fields -/

/-- Field `i` of a packed register. -/
def fld (r i : Nat) : Nat := Nat.mod (Nat.shiftRight r (Nat.mul 256 i)) TWO256

/-- Horner packing of a list of fields. -/
def packList : List Nat → Nat
  | [] => 0
  | x :: l => Nat.add x (Nat.shiftLeft (packList l) 256)

theorem pow256 : (2 : Nat) ^ 256 = TWO256 := TWO256_eq.symm

theorem TWO256_pos : 0 < TWO256 := by rw [TWO256_eq]; positivity

theorem pow_256_succ (i : Nat) : 2 ^ (256 * (i + 1)) = TWO256 * 2 ^ (256 * i) := by
  rw [← pow256, ← pow_add]; congr 1; ring

theorem fld_def (r i : Nat) : fld r i = r / 2 ^ (256 * i) % TWO256 := by
  show (r >>> (256 * i)) % TWO256 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem packList_cons (x : Nat) (l : List Nat) :
    packList (x :: l) = x + TWO256 * packList l := by
  show x + (packList l <<< 256) = _
  rw [Nat.shiftLeft_eq, pow256, mul_comm]

theorem fld_zero_left (i : Nat) : fld 0 i = 0 := by
  rw [fld_def]; simp

theorem fld_packList : ∀ (l : List Nat) (i : Nat), (∀ x ∈ l, x < TWO256) →
    fld (packList l) i = l.getD i 0
  | [], i, _ => by
    show fld 0 i = _
    rw [fld_zero_left]; rfl
  | x :: l, 0, h => by
    have hx : x < TWO256 := h x (by simp)
    rw [packList_cons, fld_def]
    simp only [mul_zero, pow_zero, Nat.div_one]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    rfl
  | x :: l, i + 1, h => by
    have hx : x < TWO256 := h x (by simp)
    have ih := fld_packList l i (fun y hy => h y (by simp [hy]))
    rw [packList_cons, fld_def, pow_256_succ, ← Nat.div_div_eq_div_mul]
    have h2 : (x + TWO256 * packList l) / TWO256 = packList l := by
      rw [Nat.add_mul_div_left _ _ TWO256_pos, Nat.div_eq_of_lt hx]; simp
    rw [h2, ← fld_def, ih]
    rfl

theorem packList_append (l1 l2 : List Nat) :
    packList (l1 ++ l2) = packList l1 + 2 ^ (256 * l1.length) * packList l2 := by
  induction l1 with
  | nil =>
    rw [List.nil_append, List.length_nil, Nat.mul_zero, pow_zero, one_mul]
    show _ = 0 + _
    rw [zero_add]
  | cons x l ih =>
    rw [List.cons_append, packList_cons, packList_cons, ih]
    rw [List.length_cons, pow_256_succ]
    generalize 2 ^ (256 * l.length) = P
    generalize packList l = a
    generalize packList l2 = b
    generalize TWO256 = W
    ring

end BecknerOnofri.V2.IntervalKernel
