module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 8..15 of row 2

Each `cell2_k` is `decide +kernel` of the fast checker `fastCheck row2 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell2_8 : fastCheck row2 8 FP2 OUTS2 = true := by decide +kernel
theorem cell2_9 : fastCheck row2 9 FP2 OUTS2 = true := by decide +kernel
theorem cell2_10 : fastCheck row2 10 FP2 OUTS2 = true := by decide +kernel
theorem cell2_11 : fastCheck row2 11 FP2 OUTS2 = true := by decide +kernel
theorem cell2_12 : fastCheck row2 12 FP2 OUTS2 = true := by decide +kernel
theorem cell2_13 : fastCheck row2 13 FP2 OUTS2 = true := by decide +kernel
theorem cell2_14 : fastCheck row2 14 FP2 OUTS2 = true := by decide +kernel
theorem cell2_15 : fastCheck row2 15 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
