import Legacy.BecknerOnofri.UniformTail
import Mathlib.Logic.Function.Iterate
/-! Exact arithmetic for an alternative theta certificate using a rational
Laplace-integral majorant instead of 4096 quadrature panels. The connection
between this finite formula and the actual J_10 remains a separate proof. -/
namespace Legacy.BecknerOnofri.ThetaCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def a : ℚ := 6283185 / 2000000
def r : ℚ := 4321393 / 100000000
def step (p : Array Nat) : Array Nat := (List.range 25).toArray.map fun q =>
  ((List.range 5).map fun k => if k*k ≤ q then (if k=0 then 1 else 2)*p[q-k*k]! else 0).sum
def stage : Nat → Array Nat
  | 0 => #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => #[1, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => #[1, 4, 4, 0, 4, 8, 0, 0, 4, 4, 8, 0, 0, 8, 0, 0, 4, 8, 4, 0, 8, 0, 0, 0, 0]
  | 3 => #[1, 6, 12, 8, 6, 24, 24, 0, 12, 30, 24, 24, 8, 24, 48, 0, 6, 48, 36, 24, 24, 48, 24, 0, 24]
  | 4 => #[1, 8, 24, 32, 24, 48, 96, 64, 24, 104, 144, 96, 96, 112, 192, 192, 24, 144, 312, 160, 144, 256, 288, 192, 96]
  | 5 => #[1, 10, 40, 80, 90, 112, 240, 320, 200, 250, 560, 560, 400, 560, 800, 960, 730, 480, 1240, 1520, 752, 1120, 1840, 1600, 1200]
  | 6 => #[1, 12, 60, 160, 252, 312, 544, 960, 1020, 876, 1560, 2400, 2080, 2040, 3264, 4160, 4092, 3480, 4380, 7200, 6552, 4608, 8160, 10560, 8224]
  | 7 => #[1, 14, 84, 280, 574, 840, 1288, 2368, 3444, 3542, 4424, 7560, 9240, 8456, 11088, 16576, 18494, 17808, 19740, 27720, 34440, 29456, 31304, 49728, 52808]
  | 8 => #[1, 16, 112, 448, 1136, 2016, 3136, 5504, 9328, 12112, 14112, 21312, 31808, 35168, 38528, 56448, 74864, 78624, 84784, 109760, 143136, 154112, 149184, 194688, 261184]
  | 9 => #[1, 18, 144, 672, 2034, 4320, 7392, 12672, 22608, 34802, 44640, 60768, 93984, 125280, 141120, 182400, 262386, 317376, 343536, 421344, 557280, 665280, 703584, 800640, 1068384]
  | 10 => #[1, 20, 180, 960, 3380, 8424, 16320, 28800, 52020, 88660, 129064, 175680, 262080, 386920, 489600, 600960, 840500, 1137960, 1330420, 1563840, 2050344, 2611200, 2986560, 3358080, 4194240]
  | _ => #[]
theorem steps_checked : ∀ i : Fin 10, step (stage i.val) = stage (i.val+1) := by decide +kernel
def counts (n : Nat) : Array Nat := Nat.iterate step n (stage 0)
theorem counts_correct (n : Nat) (hn : n ≤ 10) : counts n = stage n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [counts, Function.iterate_succ_apply']
      rw [show Nat.iterate step n (stage 0) = stage n from ih (by omega)]
      exact steps_checked ⟨n, by omega⟩
def laplaceUpper (A : ℚ) : ℚ := (A^2+5*A+2)/(A*(A^2+6*A+6))
def term (q : Nat) : ℚ :=
  let A := a*q
  (counts 10)[q]! * r^q * (1/A+4/A^2+12/A^3+24/A^4+24/A^5+laplaceUpper A)
def tailCoefficient (p : Nat) : ℚ := #[24,24,12,4,2][p]!
def tail : ℚ := 3^10*r^25*((List.range 5).map fun p =>
  tailCoefficient p*25^p/(a^(5-p)*(1-r*(26/25)^p))).sum
def rounded : Array Nat := #[1459125207561, 156702351207, 20570797669, 2193163652, 182092587, 12413605, 798766, 53939, 3502, 197, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def roundedTail : Nat := 1
def upper : ℚ := (∑ i : Fin 24, term (i.val+1)) + tail
theorem ratios_lt_one : ∀ i : Fin 5, r*(26/25)^i.val < 1 := by decide +kernel
theorem term_checks : ∀ i : Fin 24, term (i.val+1) ≤ (rounded[i.val]! : ℚ)/1000000000000 := by
  unfold term
  rw [counts_correct 10 (by decide)]
  decide +kernel
theorem tail_check : tail ≤ (roundedTail : ℚ)/1000000000000 := by decide +kernel
theorem rounded_check : (∑ i : Fin 24, (rounded[i.val]! : ℚ)/1000000000000) +
    (roundedTail : ℚ)/1000000000000 < 41/25 := by decide +kernel
theorem rational_upper_lt : upper < (41/25 : ℚ) := by
  exact lt_of_le_of_lt (add_le_add (Finset.sum_le_sum (fun i _ => term_checks i)) tail_check) rounded_check
#print axioms rational_upper_lt
end Legacy.BecknerOnofri.ThetaCertificate
