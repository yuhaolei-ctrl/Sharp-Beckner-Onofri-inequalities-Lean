module

public import BecknerOnofri.V2.IntervalKernel.Cells3_0
public import BecknerOnofri.V2.IntervalKernel.Cells3_1
public import BecknerOnofri.V2.IntervalKernel.Cells3_2
public import BecknerOnofri.V2.IntervalKernel.Cells3_3
public import BecknerOnofri.V2.IntervalKernel.Cells3_4
public import BecknerOnofri.V2.IntervalKernel.Cells3_5
public import BecknerOnofri.V2.IntervalKernel.Cells3_6
public import BecknerOnofri.V2.IntervalKernel.Cells3_7

@[expose] public section

/-!
# Row 3: `hc3`

`hc3` is the hypothesis `∀ k < row3.count, row3.checkCell k = true` of `scalar_certificate`,
obtained from the 64 kernel-checked cells through `fastCheck_sound`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cells3 : ∀ k < 64, fastCheck row3 k FP2 OUTS2 = true := by
  intro k hk
  interval_cases k
  · exact cell3_0
  · exact cell3_1
  · exact cell3_2
  · exact cell3_3
  · exact cell3_4
  · exact cell3_5
  · exact cell3_6
  · exact cell3_7
  · exact cell3_8
  · exact cell3_9
  · exact cell3_10
  · exact cell3_11
  · exact cell3_12
  · exact cell3_13
  · exact cell3_14
  · exact cell3_15
  · exact cell3_16
  · exact cell3_17
  · exact cell3_18
  · exact cell3_19
  · exact cell3_20
  · exact cell3_21
  · exact cell3_22
  · exact cell3_23
  · exact cell3_24
  · exact cell3_25
  · exact cell3_26
  · exact cell3_27
  · exact cell3_28
  · exact cell3_29
  · exact cell3_30
  · exact cell3_31
  · exact cell3_32
  · exact cell3_33
  · exact cell3_34
  · exact cell3_35
  · exact cell3_36
  · exact cell3_37
  · exact cell3_38
  · exact cell3_39
  · exact cell3_40
  · exact cell3_41
  · exact cell3_42
  · exact cell3_43
  · exact cell3_44
  · exact cell3_45
  · exact cell3_46
  · exact cell3_47
  · exact cell3_48
  · exact cell3_49
  · exact cell3_50
  · exact cell3_51
  · exact cell3_52
  · exact cell3_53
  · exact cell3_54
  · exact cell3_55
  · exact cell3_56
  · exact cell3_57
  · exact cell3_58
  · exact cell3_59
  · exact cell3_60
  · exact cell3_61
  · exact cell3_62
  · exact cell3_63

theorem hc3 : ∀ k < row3.count, row3.checkCell k = true := by
  intro k hk
  have hn : row3.count = 64 := by decide
  rw [hn] at hk
  exact fastCheck_sound row3 k FP2 OUTS2 FP2_eq OUTS2_eq (cells3 k hk)

end BecknerOnofri.V2.IntervalKernel
