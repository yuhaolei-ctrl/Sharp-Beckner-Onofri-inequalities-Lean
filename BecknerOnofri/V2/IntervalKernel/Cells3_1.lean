module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 8..15 of row 3

Each `cell3_k` is `decide +kernel` of the fast checker `fastCheck row3 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell3_8 : fastCheck row3 8 FP2 OUTS2 = true := by decide +kernel
theorem cell3_9 : fastCheck row3 9 FP2 OUTS2 = true := by decide +kernel
theorem cell3_10 : fastCheck row3 10 FP2 OUTS2 = true := by decide +kernel
theorem cell3_11 : fastCheck row3 11 FP2 OUTS2 = true := by decide +kernel
theorem cell3_12 : fastCheck row3 12 FP2 OUTS2 = true := by decide +kernel
theorem cell3_13 : fastCheck row3 13 FP2 OUTS2 = true := by decide +kernel
theorem cell3_14 : fastCheck row3 14 FP2 OUTS2 = true := by decide +kernel
theorem cell3_15 : fastCheck row3 15 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
