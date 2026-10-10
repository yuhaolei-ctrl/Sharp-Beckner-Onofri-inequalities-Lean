module

public import BecknerOnofri.V2.IntervalKernel.Cells2_0
public import BecknerOnofri.V2.IntervalKernel.Cells2_1
public import BecknerOnofri.V2.IntervalKernel.Cells2_2
public import BecknerOnofri.V2.IntervalKernel.Cells2_3
public import BecknerOnofri.V2.IntervalKernel.Cells2_4
public import BecknerOnofri.V2.IntervalKernel.Cells2_5
public import BecknerOnofri.V2.IntervalKernel.Cells2_6
public import BecknerOnofri.V2.IntervalKernel.Cells2_7

@[expose] public section

/-!
# Row 2: `hc2`

`hc2` is the hypothesis `∀ k < row2.count, row2.checkCell k = true` of `scalar_certificate`,
obtained from the 64 kernel-checked cells through `fastCheck_sound`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cells2 : ∀ k < 64, fastCheck row2 k FP2 OUTS2 = true := by
  intro k hk
  interval_cases k
  · exact cell2_0
  · exact cell2_1
  · exact cell2_2
  · exact cell2_3
  · exact cell2_4
  · exact cell2_5
  · exact cell2_6
  · exact cell2_7
  · exact cell2_8
  · exact cell2_9
  · exact cell2_10
  · exact cell2_11
  · exact cell2_12
  · exact cell2_13
  · exact cell2_14
  · exact cell2_15
  · exact cell2_16
  · exact cell2_17
  · exact cell2_18
  · exact cell2_19
  · exact cell2_20
  · exact cell2_21
  · exact cell2_22
  · exact cell2_23
  · exact cell2_24
  · exact cell2_25
  · exact cell2_26
  · exact cell2_27
  · exact cell2_28
  · exact cell2_29
  · exact cell2_30
  · exact cell2_31
  · exact cell2_32
  · exact cell2_33
  · exact cell2_34
  · exact cell2_35
  · exact cell2_36
  · exact cell2_37
  · exact cell2_38
  · exact cell2_39
  · exact cell2_40
  · exact cell2_41
  · exact cell2_42
  · exact cell2_43
  · exact cell2_44
  · exact cell2_45
  · exact cell2_46
  · exact cell2_47
  · exact cell2_48
  · exact cell2_49
  · exact cell2_50
  · exact cell2_51
  · exact cell2_52
  · exact cell2_53
  · exact cell2_54
  · exact cell2_55
  · exact cell2_56
  · exact cell2_57
  · exact cell2_58
  · exact cell2_59
  · exact cell2_60
  · exact cell2_61
  · exact cell2_62
  · exact cell2_63

theorem hc2 : ∀ k < row2.count, row2.checkCell k = true := by
  intro k hk
  have hn : row2.count = 64 := by decide
  rw [hn] at hk
  exact fastCheck_sound row2 k FP2 OUTS2 FP2_eq OUTS2_eq (cells2 k hk)

end BecknerOnofri.V2.IntervalKernel
