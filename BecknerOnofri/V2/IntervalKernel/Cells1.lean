module

public import BecknerOnofri.V2.IntervalKernel.Cells1_0
public import BecknerOnofri.V2.IntervalKernel.Cells1_1
public import BecknerOnofri.V2.IntervalKernel.Cells1_2
public import BecknerOnofri.V2.IntervalKernel.Cells1_3

@[expose] public section

/-!
# Row 1: `hc1`

`hc1` is the hypothesis `∀ k < row1.count, row1.checkCell k = true` of `scalar_certificate`,
obtained from the 32 kernel-checked cells through `fastCheck_sound`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cells1 : ∀ k < 32, fastCheck row1 k FP1 OUTS1 = true := by
  intro k hk
  interval_cases k
  · exact cell1_0
  · exact cell1_1
  · exact cell1_2
  · exact cell1_3
  · exact cell1_4
  · exact cell1_5
  · exact cell1_6
  · exact cell1_7
  · exact cell1_8
  · exact cell1_9
  · exact cell1_10
  · exact cell1_11
  · exact cell1_12
  · exact cell1_13
  · exact cell1_14
  · exact cell1_15
  · exact cell1_16
  · exact cell1_17
  · exact cell1_18
  · exact cell1_19
  · exact cell1_20
  · exact cell1_21
  · exact cell1_22
  · exact cell1_23
  · exact cell1_24
  · exact cell1_25
  · exact cell1_26
  · exact cell1_27
  · exact cell1_28
  · exact cell1_29
  · exact cell1_30
  · exact cell1_31

theorem hc1 : ∀ k < row1.count, row1.checkCell k = true := by
  intro k hk
  have hn : row1.count = 32 := by decide
  rw [hn] at hk
  exact fastCheck_sound row1 k FP1 OUTS1 FP1_eq OUTS1_eq (cells1 k hk)

end BecknerOnofri.V2.IntervalKernel
