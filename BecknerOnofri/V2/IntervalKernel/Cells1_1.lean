module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 8..15 of row 1

Each `cell1_k` is `decide +kernel` of the fast checker `fastCheck row1 k FP1 OUTS1`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell1_8 : fastCheck row1 8 FP1 OUTS1 = true := by decide +kernel
theorem cell1_9 : fastCheck row1 9 FP1 OUTS1 = true := by decide +kernel
theorem cell1_10 : fastCheck row1 10 FP1 OUTS1 = true := by decide +kernel
theorem cell1_11 : fastCheck row1 11 FP1 OUTS1 = true := by decide +kernel
theorem cell1_12 : fastCheck row1 12 FP1 OUTS1 = true := by decide +kernel
theorem cell1_13 : fastCheck row1 13 FP1 OUTS1 = true := by decide +kernel
theorem cell1_14 : fastCheck row1 14 FP1 OUTS1 = true := by decide +kernel
theorem cell1_15 : fastCheck row1 15 FP1 OUTS1 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
