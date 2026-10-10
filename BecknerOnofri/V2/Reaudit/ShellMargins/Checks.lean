module

public import Legacy.BecknerOnofri.FiniteScalar
public import Legacy.D10.FiniteShellList
public import BecknerOnofri.ElevenScalarFinite.Core

@[expose] public section

/-! # Kernel evaluation of the retained-shell certificate with the margins of the replacement text

The legacy `FiniteCheck d n` (`Legacy.BecknerOnofri.FiniteScalar`) states
`lambdaUpper d * energyUpper d n + 3/1100 < d * harmonic n`.  Here the same finite computation
(`energyUpper` = retained shells `q ≤ 64` exactly plus all omitted mass at the weight `U_65`, with the
integer weights `reciprocalUnits`) is evaluated with the larger margins claimed in the replacement
text, by `decide +kernel` (kernel evaluation only).

* `gapQ d n = d H_n - ℓ_d^+ · (retained-shell bound)` for `d = 2` (`n ≤ 3`) and `3 ≤ d ≤ 10`
  (`n ≤ 21`): every one of the 171 pairs exceeds `3/10`, except `(d, n) = (10, 21)` whose gap lies in
  `(0.162894, 0.162895)`; hence all 171 gaps exceed `4/25` and the smallest is at `(10, 21)`.
* `gapQ11 n = 11 H_n - (β₀ ℓ_11^+/22) · (retained-shell bound)` for `1 ≤ n ≤ 21`: the gap at `n = 1` lies in
  `(0.00055649, 0.0005565)` and the others exceed `3/10`; hence all exceed `111/200000`. -/

namespace BecknerOnofri.V2.Reaudit.ShellMargins

open Legacy.BecknerOnofri.FiniteScalar (lambdaUpper energyUpper energyUpperWith)
open Legacy.D10.FiniteScalar (shellList shellArray_eq_shellList)

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- `energyUpper` with the shell array replaced by the (kernel-fast) shell list. -/
def energyUpperList (d n : ℕ) : ℚ := energyUpperWith d n (shellList n d).toArray

theorem energyUpper_eq_list (d n : ℕ) : energyUpper d n = energyUpperList d n := by
  unfold energyUpper energyUpperList
  rw [shellArray_eq_shellList]

/-- `d H_n - ℓ_d^+ · (retained-shell bound)`, with the legacy integer weights. -/
def gapQ (d n : ℕ) : ℚ :=
  (d : ℚ) * Legacy.D10.FiniteScalar.harmonic n - lambdaUpper d * energyUpperList d n

/-- `11 H_n - (3543·945/(200·64)) (100000/314159)^5 · (retained-shell bound)`. -/
def gapQ11 (n : ℕ) : ℚ :=
  (11 : ℚ) * Legacy.D10.FiniteScalar.harmonic n -
    BecknerOnofri.HighDim.Eleven.ScalarFinite.betaLambda * energyUpperList 11 n

theorem gap_d2 : ∀ j : Fin 3, (3 : ℚ) / 10 < gapQ 2 (j.val + 1) := by decide +kernel
theorem gap_d3 : ∀ j : Fin 21, (3 : ℚ) / 10 < gapQ 3 (j.val + 1) := by decide +kernel
theorem gap_d4 : ∀ j : Fin 21, (3 : ℚ) / 10 < gapQ 4 (j.val + 1) := by decide +kernel
theorem gap_d5 : ∀ j : Fin 21, (3 : ℚ) / 10 < gapQ 5 (j.val + 1) := by decide +kernel
theorem gap_d6 : ∀ j : Fin 21, (3 : ℚ) / 10 < gapQ 6 (j.val + 1) := by decide +kernel
theorem gap_d7 : ∀ j : Fin 21, (3 : ℚ) / 10 < gapQ 7 (j.val + 1) := by decide +kernel
theorem gap_d8 : ∀ j : Fin 21, (3 : ℚ) / 10 < gapQ 8 (j.val + 1) := by decide +kernel
theorem gap_d9 : ∀ j : Fin 21, (3 : ℚ) / 10 < gapQ 9 (j.val + 1) := by decide +kernel
theorem gap_d10 : ∀ j : Fin 20, (3 : ℚ) / 10 < gapQ 10 (j.val + 1) := by decide +kernel

/-- The smallest of the 171 gaps: `d = 10`, `n = 21`, about `0.1628949`. -/
theorem gap_10_21 : (162894 : ℚ) / 10 ^ 6 < gapQ 10 21 ∧ gapQ 10 21 < (162895 : ℚ) / 10 ^ 6 := by
  decide +kernel

theorem gap11_one :
    (55649 : ℚ) / 10 ^ 8 < gapQ11 1 ∧ gapQ11 1 < (55650 : ℚ) / 10 ^ 8 := by decide +kernel

theorem gap11_rest : ∀ j : Fin 20, (3 : ℚ) / 10 < gapQ11 (j.val + 2) := by decide +kernel

end BecknerOnofri.V2.Reaudit.ShellMargins

end
