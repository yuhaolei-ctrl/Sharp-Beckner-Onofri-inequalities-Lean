module

public import BecknerOnofri.V2.Vocab.Section2Bridge
public import BecknerOnofri.V2.Vocab.ExternalInputs
public import BecknerOnofri.V2.Final.Unconditional
public import BecknerOnofri.V2.Final.Low
public import BecknerOnofri.V2.Final.Eleven

@[expose] public section

/-! # `PositiveThresholdInput d` as a consequence of the v2 final theorems

The manuscript takes `eq:section2-positive-threshold-input` (`Ent ρ ≥ (β₀ c_d / 2) ‖ρ‖²_{Ḣ^{-d/2}}`,
some `β₀ > 0`) from [CdCRS2025, Thm 3] (tensorization) for `d ≥ 2` and from Lebedev-Milin for `d = 1`.
The repository does **not** reprove CdCRS Thm 3.  What it has is

* `positiveThreshold_of_globalTransition_pos`: the Prop is *equivalent* to `0 < β_gm(d)` (take
  `β₀ = β_gm(d)`; `P_d(β_gm) = 0` is the competitor inequality), and
* the v2 final theorems, which determine `β_gm(d)` exactly or bound it from below:
  `β_gm(d) = 2d` for `1 ≤ d ≤ 10`, `3543/200 < β_gm(11)`, `β_gm(d) = β_s(d)` for `d ≥ 12`.

Consequently `positiveThreshold d` below is a theorem for every `d ≥ 1` -- **as a corollary of the main
theorems**, not as an input to them.  This is the reverse of the manuscript's logical order (the printed
proof uses the input to define the threshold before the main theorems are proved); in Lean the main
theorems do not use `PositiveThresholdInput` at all (nothing else in the repository mentions it). -/

noncomputable section

namespace BecknerOnofri.V2.Reaudit.ExternalInputs
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- Converse of `V2.Vocab.globalTransition_pos_of_input`. -/
theorem positiveThreshold_of_globalTransition_pos {d : ℕ} (hd : 0 < d)
    (h : 0 < VariationalCurves.globalTransition d) : PositiveThresholdInput d := by
  refine ⟨VariationalCurves.globalTransition d, h, fun ρ hρ => ?_⟩
  have hz : pressure d (VariationalCurves.globalTransition d) = 0 :=
    (VariationalCurves.pressure_zero_iff hd _).2 le_rfl
  have hc := (VariationalCurves.pressure_zero_iff_competitors hd _).1 hz ρ hρ
  rw [interaction_eq_kernelConstant_mul hd ρ hρ, entropy_eq_toReal_torusEntropy ρ hρ] at hc
  linarith

theorem positiveThreshold_iff {d : ℕ} (hd : 0 < d) :
    PositiveThresholdInput d ↔ 0 < VariationalCurves.globalTransition d :=
  ⟨globalTransition_pos_of_input hd, positiveThreshold_of_globalTransition_pos hd⟩

/-- `0 < β_gm(d)` for every `d ≥ 1`, from the v2 final theorems (`d ≤ 10`, `d = 11`, `d ≥ 12`). -/
theorem globalTransition_pos_final {d : ℕ} (hd : 0 < d) : 0 < VariationalCurves.globalTransition d := by
  by_cases h10 : d ≤ 10
  · rw [BecknerOnofri.V2.Final.low_dim_globalTransition d hd h10]
    exact mul_pos two_pos (Nat.cast_pos.mpr hd)
  by_cases h11 : d = 11
  · subst h11
    have := (BecknerOnofri.V2.Final.eleven_globalTransition_bounds).1
    exact lt_trans (by norm_num) this
  · have h12 : 12 ≤ d := by omega
    rw [(BecknerOnofri.V2.Final.Unconditional.high_dim_thresholds d h12).2.2.1]
    exact spectralThreshold_pos' hd

/-- **`eq:section2-positive-threshold-input`** for every `d ≥ 1`, as a corollary of the final theorems. -/
theorem positiveThreshold {d : ℕ} (hd : 0 < d) : PositiveThresholdInput d :=
  positiveThreshold_of_globalTransition_pos hd (globalTransition_pos_final hd)

end BecknerOnofri.V2.Reaudit.ExternalInputs
