module

public import BecknerOnofri.V2.Interval.CheckSound
public import BecknerOnofri.V2.IntervalKernel.Cells1
public import BecknerOnofri.V2.IntervalKernel.Cells2
public import BecknerOnofri.V2.IntervalKernel.Cells3

@[expose] public section

/-!
# Negative tests of the kernel certificate checker, and the finite statements about the table

The 160 cell checks `fastCheck row_i k FP OUTS = true` (files `Cells{1,2,3}_*.lean`) are positive
statements.  Here the same checker (`fastCheck`, the compiled programs `FP1`, `FP2`, `OUTS1`, `OUTS2`)
is shown to REJECT wrong data.  Every theorem below is a kernel evaluation (`decide +kernel`, no native
code) of `fastCheck` on a deliberately perturbed row, program or output list, or of the reference
`Row.checkCell`; it states that the verdict is `false`.  Four families:

* **Sharp margins** (`*_tight_ok` / `*_tight_reject`): on a cell (the last cell of row 1, the last cell
  of row 2, the first cell of row 3) the strict margin is replaced by a rational just below / just
  above the lower end of the enclosure that the checker computes (the numbers quoted in the
  docstrings were read off with `#eval` on the unperturbed data and are not used in any proof).  The
  pair shows that the verdict flips exactly at the computed enclosure, i.e. that the final comparison
  is not vacuous.  Also a margin with denominator `0`, and the margin `1/4` for `e_j + 1/4` on the
  first cell of row 1, where `e_j(0) = 0` makes the strict inequality `e_j + 1/4 > 1/4` false.
* **Perturbed cell data**: cells that are too coarse (`count` replaced by a smaller number), cells moved
  to a place where the program is not certified or is not defined, cells outside the table.
* **Perturbed programs / outputs**: wrong output register, out-of-range output register, truncated or
  edited program, the program of the other kind of row.
* **Statements about the table**: the cell numbers `32 + 64 + 64 = 160`, validity of the rows
  (`Row.Valid`), the rows are glued end to end, and the cells cover `[0, 99/100]` (by
  `Row.cover`); `fastCheck` on a row with `count = 0` is NOT rejected, which is why `Row.Valid` is
  an explicit hypothesis of `Row.cover` and of the soundness theorems.

Why `false` is the correct verdict: by `fastCheck_sound`, `fastCheck r k FP OUTS = true` for the
reference programs would give `r.checkCell k = true`, and by `checkCell_big` / `checkCell_small` that
is the claim `m < register value` for every point of the cell.  The unperturbed rows are certified
only with margins strictly below the computed enclosure; the perturbed data ask for more (or for
something else) than the enclosure supports.  A `false` verdict does not mean that the real inequality
is false (the check is only sufficient); where the real inequality is false it is said explicitly.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

/-! ### 1. Sharp margins

For the cells below the checked quantities are (row 1) `f⁗/4! - 1/10`, `1/50 - 𝒱⁗/4!`, and the
minimum over `j` of `e_j + 1/4` (box entry `0`), and (rows 2, 3) the lower ends of the Taylor-and-box
enclosures of `f/t⁴ - 1/10`, `1/50 - 𝒱/t⁴` and `e_j + 1/4`. -/

/-- Row 1, last cell `k = 31` (`[31/256, 1/8]`), margin `m0` of `f⁗/4! - 1/10` replaced by `408/1000`.
The checker's lower end is about `0.40907`, so the margin `0.408` is still strictly below it. -/
theorem row1_c31_m0_tight_ok :
    fastCheck { row1 with m0 := (408, 1000) } 31 FP1 OUTS1 = true := by decide +kernel

/-- Same cell, `m0 := 410/1000`: above the computed lower end `0.40907`, hence `false`. -/
theorem row1_c31_m0_tight_reject :
    fastCheck { row1 with m0 := (410, 1000) } 31 FP1 OUTS1 = false := by decide +kernel

/-- Row 1, cell 31, margin `m1` of `1/50 - 𝒱⁗/4!` replaced by `78/10000`; the computed value is
about `0.007866`, so this is still accepted. -/
theorem row1_c31_m1_tight_ok :
    fastCheck { row1 with m1 := (78, 10000) } 31 FP1 OUTS1 = true := by decide +kernel

/-- Same cell, `m1 := 79/10000 > 0.007866`: rejected. -/
theorem row1_c31_m1_tight_reject :
    fastCheck { row1 with m1 := (79, 10000) } 31 FP1 OUTS1 = false := by decide +kernel

/-- Row 1, cell 31, margin `m2` for the minimum of `e_j + 1/4` replaced by `245/1000`; the computed
minimum is about `0.24581` (register `e_12`), so this is accepted. -/
theorem row1_c31_m2_tight_ok :
    fastCheck { row1 with m2 := (245, 1000) } 31 FP1 OUTS1 = true := by decide +kernel

/-- Same cell, `m2 := 246/1000 > 0.24581`: rejected. -/
theorem row1_c31_m2_tight_reject :
    fastCheck { row1 with m2 := (246, 1000) } 31 FP1 OUTS1 = false := by decide +kernel

/-- Row 2, last cell `k = 63`, margin `m0` of `f/t⁴ - 1/10` replaced by `19/1000`; the lower end of
the Taylor-and-box enclosure is about `0.019503`, so `0.019` is accepted. -/
theorem row2_c63_m0_tight_ok :
    fastCheck { row2 with m0 := (19, 1000) } 63 FP2 OUTS2 = true := by decide +kernel

/-- Same cell, `m0 := 20/1000 > 0.019503`: rejected. -/
theorem row2_c63_m0_tight_reject :
    fastCheck { row2 with m0 := (20, 1000) } 63 FP2 OUTS2 = false := by decide +kernel

/-- Row 2, cell 63, margin `m1` of `1/50 - 𝒱/t⁴` replaced by `11/1000`; lower end about `0.011091`. -/
theorem row2_c63_m1_tight_ok :
    fastCheck { row2 with m1 := (11, 1000) } 63 FP2 OUTS2 = true := by decide +kernel

/-- Same cell, `m1 := 12/1000 > 0.011091`: rejected. -/
theorem row2_c63_m1_tight_reject :
    fastCheck { row2 with m1 := (12, 1000) } 63 FP2 OUTS2 = false := by decide +kernel

/-- Row 2, cell 63, margin `m2` for all thirteen `e_j + 1/4` replaced by `96/1000`; the smallest of the
thirteen lower ends is about `0.096358` (`e_8`), so this is accepted. -/
theorem row2_c63_m2_tight_ok :
    fastCheck { row2 with m2 := (96, 1000) } 63 FP2 OUTS2 = true := by decide +kernel

/-- Same cell, `m2 := 97/1000 > 0.096358`: rejected because of the register `e_8`. -/
theorem row2_c63_m2_tight_reject :
    fastCheck { row2 with m2 := (97, 1000) } 63 FP2 OUTS2 = false := by decide +kernel

/-- Row 3, first cell `k = 0` (`[7/8, 7/8 + 23/12800]`), margin `m0` of `f/t⁴ - 1/10` replaced by
`22/1000`; the computed lower end is about `0.022935` (the genuine margin is `1/50`), so `0.022`
is accepted. -/
theorem row3_c0_m0_tight_ok :
    fastCheck { row3 with m0 := (22, 1000) } 0 FP2 OUTS2 = true := by decide +kernel

/-- Same cell, `m0 := 23/1000 > 0.022935`: rejected. -/
theorem row3_c0_m0_tight_reject :
    fastCheck { row3 with m0 := (23, 1000) } 0 FP2 OUTS2 = false := by decide +kernel

/-- Row 3, cell 0, margin `m1` of `1/50 - 𝒱/t⁴` replaced by `11/1000`; lower end about `0.011825`. -/
theorem row3_c0_m1_tight_ok :
    fastCheck { row3 with m1 := (11, 1000) } 0 FP2 OUTS2 = true := by decide +kernel

/-- Same cell, `m1 := 12/1000 > 0.011825`: rejected. -/
theorem row3_c0_m1_tight_reject :
    fastCheck { row3 with m1 := (12, 1000) } 0 FP2 OUTS2 = false := by decide +kernel

/-- Row 3, cell 0, margin `m2` for all `e_j + 1/4` replaced by `96/1000`; smallest lower end about
`0.096080` (`e_8`), accepted. -/
theorem row3_c0_m2_tight_ok :
    fastCheck { row3 with m2 := (96, 1000) } 0 FP2 OUTS2 = true := by decide +kernel

/-- Same cell, `m2 := 97/1000 > 0.096080`: rejected. -/
theorem row3_c0_m2_tight_reject :
    fastCheck { row3 with m2 := (97, 1000) } 0 FP2 OUTS2 = false := by decide +kernel

/-- Row 1, first cell (it contains `t = 0`), margin `m2` replaced by `1/4`: the check would assert
`e_j + 1/4 > 1/4` on `[0, 1/256]`, which is FALSE at `t = 0` because `e_j(0) = 0` (the vanishing at
the origin of the manuscript's appendix).  The checker must therefore return `false`. -/
theorem row1_c0_m2_quarter_reject :
    fastCheck { row1 with m2 := (1, 4) } 0 FP1 OUTS1 = false := by decide +kernel

/-- A margin `1/0` is not a rational number: the integer cross-multiplication `c * b < a * 0` of
`gtQ` can never hold for `c = 1`, so the verdict is `false` (row 1). -/
theorem row1_margin_den_zero_reject :
    fastCheck { row1 with m0 := (1, 0) } 0 FP1 OUTS1 = false := by decide +kernel

/-- Margin denominator `0` for the first margin of row 2 (first cell of row 2). -/
theorem row2_margin_den_zero_reject :
    fastCheck { row2 with m0 := (1, 0) } 0 FP2 OUTS2 = false := by decide +kernel

/-- Margin denominator `0` for the first margin of row 3 (first cell of row 3). -/
theorem row3_margin_den_zero_reject :
    fastCheck { row3 with m0 := (1, 0) } 0 FP2 OUTS2 = false := by decide +kernel

/-! ### 2. Perturbed cell data -/

/-- Row 1 with two cells instead of 32: the first cell is `[0, 1/16]`, sixteen times as wide as a
genuine cell.  The fourth-derivative boxes over such a wide cell are too coarse to reach the margins
`2/5`, `3/400`, `6/25`; the checker rejects (the true inequalities need not fail; the enclosure is
simply not good enough). -/
theorem row1_coarse_reject : fastCheck { row1 with count := 2 } 0 FP1 OUTS1 = false := by
  decide +kernel

/-- Row 2 as a single cell `[1/8, 7/8]`: the Taylor-and-box enclosure over a cell of width `3/4` does
not reach the margins `1/100`, `7/1000`, `9/100`; rejected. -/
theorem row2_coarse_reject : fastCheck { row2 with count := 1 } 0 FP2 OUTS2 = false := by
  decide +kernel

/-- Row 3 with four cells instead of 64 (first cell of width `23/800`, sixteen times a genuine cell):
rejected, because the margins of row 3 (tight: `f/t⁴ - 1/10 > 1/50` with computed value `0.0229` on the
genuine first cell) cannot be certified from a wider cell. -/
theorem row3_coarse_reject : fastCheck { row3 with count := 4 } 0 FP2 OUTS2 = false := by
  decide +kernel

/-- Row 1 moved to `[1/4, 3/8]` (still `32` cells; first cell tested): the first-row test (box entry
`4` of `f` above `1/10 + 2/5`) is not satisfied there; rejected.  (Row 1 is only certified on
`[0, 1/8]`; beyond `1/8` rows 2 and 3 take over.) -/
theorem row1_shifted_reject :
    fastCheck { row1 with aN := 1, aD := 4, bN := 3, bD := 8 } 0 FP1 OUTS1 = false := by
  decide +kernel

/-- Cell `k = 32` of row 1 is the cell `[1/8, 1/8 + 1/256]` just outside the table range of row 1:
the first-row test fails there (index out of range of the table, not covered by `hc1`). -/
theorem row1_out_of_range_reject : fastCheck row1 32 FP1 OUTS1 = false := by decide +kernel

/-- Cell `k = 64` of row 3 is `[99/100, 99/100 + 23/12800]`, outside the range `[7/8, 99/100]` of the
table: rejected. -/
theorem row3_out_of_range_reject : fastCheck row3 64 FP2 OUTS2 = false := by decide +kernel

/-- Row 2 started at `0` instead of `1/8` (so its first cell contains `t = 0`): the normalized program
divides by `t⁴` (reciprocal of an interval containing `0`), the interpreter fails, and the verdict is
`false`.  The quantity `f/t⁴ - 1/10` is not even defined at `t = 0`. -/
theorem row2_from_zero_reject :
    fastCheck { row2 with aN := 0, aD := 1 } 0 FP2 OUTS2 = false := by decide +kernel

/-- Row 3 extended to the right end point `1` (instead of `99/100`): the last cell contains
`t = 1`, where the program is not defined (`λ`, `ω`, the entropies degenerate at the end point);
rejected. -/
theorem row3_to_one_reject :
    fastCheck { row3 with bN := 1, bD := 1 } 63 FP2 OUTS2 = false := by decide +kernel

/-! ### 3. Perturbed programs and output registers -/

/-- Row 3, cell 0: the output register `f` is replaced by the register of `v` (`1/50 - 𝒱/t⁴`, lower
end `0.0118`).  The first margin `1/50` is then tested against the lower end `0.0118` of the `v` register; rejected. -/
theorem row3_wrong_f_register_reject :
    fastCheck row3 0 FP2 { OUTS2 with f := OUTS2.v } = false := by decide +kernel

/-- Row 1, cell 0: the register of `f` is replaced by that of `𝒱`; the test `f⁗/4! - 1/10 > 2/5`
is applied to the register of `𝒱`; rejected. -/
theorem row1_wrong_f_register_reject :
    fastCheck row1 0 FP1 { OUTS1 with f := OUTS1.v } = false := by decide +kernel

/-- Row 1, cell 0: the register of `𝒱` is replaced by that of `f`; the test
`1/50 - 𝒱⁗/4! > 3/400` is applied to the register of `f`; rejected. -/
theorem row1_wrong_v_register_reject :
    fastCheck row1 0 FP1 { OUTS1 with v := OUTS1.f } = false := by decide +kernel

/-- Row 2, cell 0: the list of `e`-registers gets an extra register `5000`, which is beyond the
register file (capacity `2048`).  The register is missing, `tget` returns `none`, the check is
`false` (an out-of-range output register can never be accepted). -/
theorem row2_missing_e_register_reject :
    fastCheck row2 0 FP2 { OUTS2 with e := OUTS2.e ++ [5000] } = false := by decide +kernel

/-- Row 1, cell 0: the extra `e`-register is `2048`, the first index excluded by the capacity check
of `tget`; rejected. -/
theorem row1_capacity_e_register_reject :
    fastCheck row1 0 FP1 { OUTS1 with e := OUTS1.e ++ [2048] } = false := by decide +kernel

/-- Row 1, cell 0: the last operation of the compiled program is removed; the output registers of
`OUTS1` then refer to a register that was never written; rejected. -/
theorem row1_truncated_program_reject : fastCheck row1 0 FP1.dropLast OUTS1 = false := by
  decide +kernel

/-- Row 3, cell 0: the last operation of `FP2` is removed (the register `1298`, which `OUTS2.v`
reads, is never written); rejected. -/
theorem row3_truncated_program_reject : fastCheck row3 0 FP2.dropLast OUTS2 = false := by
  decide +kernel

/-- Row 3, cell 0: the first operation of `FP2` (the variable `t`) is removed, which shifts every
register index by one; the references of the remaining program are now wrong; rejected. -/
theorem row3_shifted_program_reject : fastCheck row3 0 FP2.tail OUTS2 = false := by
  decide +kernel

/-- Row 3, cell 0: the last operation `FOp.add 1294 1297` (which forms `1/50 - 𝒱/t⁴` as the sum
of the constant `1/50` and the negated `𝒱/t⁴`) is replaced by the product `FOp.mul 1294 1297`; the register `1298` then holds a wrong
quantity; rejected. -/
theorem row3_edited_op_reject :
    fastCheck row3 0 (FP2.dropLast ++ [FOp.mul 1294 1297]) OUTS2 = false := by decide +kernel

/-- The first-row program `FP1` / `OUTS1` run on a cell of row 2 (so the register `f` is `f`, not
`f/t⁴ - 1/10`): the `Taylor` tests of the non-small row against the margins `1/100`, `7/1000`,
`9/100` fail; rejected. -/
theorem row2_with_row1_program_reject : fastCheck row2 0 FP1 OUTS1 = false := by decide +kernel

/-- The normalized program `FP2` / `OUTS2` run on row 1 (first cell, which contains `t = 0`): the
division by `t⁴` fails; rejected. -/
theorem row1_with_row2_program_reject : fastCheck row1 0 FP2 OUTS2 = false := by decide +kernel

/-! ### 4. The reference checker `Row.checkCell` also rejects -/

set_option maxHeartbeats 0 in
/-- The reference checker (the slow, readable interpreter `runRS`, not the packed one) on row 3 cell 7
with the margin `m1` of `1/50 - 𝒱/t⁴` replaced by `1/10`: the lower end of the enclosure of `1/50 - 𝒱/t⁴`
is of order `10^-2` on row 3 (`0.0118` on cell 0), far below `1/10`; rejected.  `fastCheck_sound`
is the refinement from the packed checker to this one. -/
theorem row3_checkCell_margin_reject :
    ({ row3 with m1 := (1, 10) } : Row).checkCell 7 = false := by decide +kernel

/-! ### 5. The degenerate row with no cells

`fastCheck` does not reject the row with `count = 0` (its single "cell" has `den = 0` and is a point
interval `[0, 0]`).  This is harmless, because every soundness statement assumes `Row.Valid`, which
contains `0 < count`, and because `hc1 hc2 hc3` quantify over `k < count` for the genuine rows. -/

/-- `fastCheck` accepts the degenerate cell of the row with `count = 0` (observed, kernel-checked). -/
theorem degenerate_count_zero_accepted :
    fastCheck { row1 with count := 0 } 0 FP1 OUTS1 = true := by decide +kernel

/-- The degenerate row is not `Row.Valid`, so none of the soundness theorems applies to it. -/
theorem degenerate_count_zero_not_valid : ¬ Row.Valid { row1 with count := 0 } := by
  intro h
  exact absurd h.count (by decide)

/-! ### 6. Statements about the table: cell numbers, validity, gluing, cover -/

/-- The row data are exactly the table of the manuscript (ranges, cell numbers, margins). -/
theorem rows_table :
    row1 = ⟨true, 0, 1, 1, 8, 32, (2, 5), (3, 400), (6, 25)⟩ ∧
    row2 = ⟨false, 1, 8, 7, 8, 64, (1, 100), (7, 1000), (9, 100)⟩ ∧
    row3 = ⟨false, 7, 8, 99, 100, 64, (1, 50), (1, 100), (7, 250)⟩ := ⟨rfl, rfl, rfl⟩

/-- The numbers of cells are `32`, `64`, `64` (so `160` in all). -/
theorem cell_counts : row1.count = 32 ∧ row2.count = 64 ∧ row3.count = 64 := by decide

theorem cell_total : row1.count + row2.count + row3.count = 160 := by decide

theorem row1_valid : row1.Valid := ⟨by decide, by decide, by decide⟩
theorem row2_valid : row2.Valid := ⟨by decide, by decide, by decide⟩
theorem row3_valid : row3.Valid := ⟨by decide, by decide, by decide⟩

/-- Row 1 starts at `0` and consists of consecutive cells (the right end of cell `k` is the left end of
cell `k + 1`, with the common denominator) which end at `1/8`. -/
theorem row1_glued :
    (row1.cell 0).lo = 0 ∧ (∀ k < 31, (row1.cell k).hi = (row1.cell (k + 1)).lo) ∧
      (row1.cell 31).hi * 8 = ((row1.cell 31).den : Int) := by
  refine ⟨by decide, ?_, by decide⟩
  decide

/-- Row 2 starts at `1/8` and its cells end at `7/8`. -/
theorem row2_glued :
    (row2.cell 0).lo * 8 = ((row2.cell 0).den : Int) ∧
      (∀ k < 63, (row2.cell k).hi = (row2.cell (k + 1)).lo) ∧
      (row2.cell 63).hi * 8 = 7 * ((row2.cell 63).den : Int) := by
  refine ⟨by decide, ?_, by decide⟩
  decide

/-- Row 3 starts at `7/8` and its cells end at `99/100`. -/
theorem row3_glued :
    (row3.cell 0).lo * 8 = 7 * ((row3.cell 0).den : Int) ∧
      (∀ k < 63, (row3.cell k).hi = (row3.cell (k + 1)).lo) ∧
      (row3.cell 63).hi * 100 = 99 * ((row3.cell 63).den : Int) := by
  refine ⟨by decide, ?_, by decide⟩
  decide

/-- The end points of the three rows, as real numbers: `[0, 1/8]`, `[1/8, 7/8]`, `[7/8, 99/100]`. -/
theorem row_endpoints :
    ((row1.aN : ℝ) / row1.aD = 0 ∧ (row1.bN : ℝ) / row1.bD = 1 / 8) ∧
    ((row2.aN : ℝ) / row2.aD = 1 / 8 ∧ (row2.bN : ℝ) / row2.bD = 7 / 8) ∧
    ((row3.aN : ℝ) / row3.aD = 7 / 8 ∧ (row3.bN : ℝ) / row3.bD = 99 / 100) := by
  norm_num [row1, row2, row3]

/-- The 160 cells cover `[0, 99/100]`: every point of that interval lies in a closed cell
`[lo/den, hi/den]` of one of the three rows (by `Row.cover` for each row). -/
theorem cells_cover :
    ∀ t : ℝ, 0 ≤ t → t ≤ 99 / 100 →
      ∃ r ∈ [row1, row2, row3], ∃ k, k < r.count ∧ r.lo' k ≤ t ∧ t ≤ r.hi' k := by
  intro t h0 h99
  obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := row_endpoints
  rcases le_total t (1 / 8) with h | h
  · obtain ⟨k, hk, hl, hu⟩ := Row.cover row1 row1_valid (t := t) ⟨by rw [a1]; exact h0, by rw [b1]; exact h⟩
    exact ⟨row1, by simp, k, hk, hl, hu⟩
  · rcases le_total t (7 / 8) with h' | h'
    · obtain ⟨k, hk, hl, hu⟩ :=
        Row.cover row2 row2_valid (t := t) ⟨by rw [a2]; exact h, by rw [b2]; exact h'⟩
      exact ⟨row2, by simp, k, hk, hl, hu⟩
    · obtain ⟨k, hk, hl, hu⟩ :=
        Row.cover row3 row3_valid (t := t) ⟨by rw [a3]; exact h', by rw [b3]; exact h99⟩
      exact ⟨row3, by simp, k, hk, hl, hu⟩

/-- The positive statement that all `160 = 32 + 64 + 64` cells pass (these are the proved
`hc1 hc2 hc3` of `Cells{1,2,3}.lean`, restated next to the negative tests). -/
theorem all_cells_checked :
    (∀ k < row1.count, row1.checkCell k = true) ∧
    (∀ k < row2.count, row2.checkCell k = true) ∧
    (∀ k < row3.count, row3.checkCell k = true) := ⟨hc1, hc2, hc3⟩

end BecknerOnofri.V2.IntervalKernel
