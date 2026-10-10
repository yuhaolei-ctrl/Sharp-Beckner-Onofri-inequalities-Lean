module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 16..23 of row 3

Each `cell3_k` is `decide +kernel` of the fast checker `fastCheck row3 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell3_16 : fastCheck row3 16 FP2 OUTS2 = true := by decide +kernel
theorem cell3_17 : fastCheck row3 17 FP2 OUTS2 = true := by decide +kernel
theorem cell3_18 : fastCheck row3 18 FP2 OUTS2 = true := by decide +kernel
theorem cell3_19 : fastCheck row3 19 FP2 OUTS2 = true := by decide +kernel
theorem cell3_20 : fastCheck row3 20 FP2 OUTS2 = true := by decide +kernel
theorem cell3_21 : fastCheck row3 21 FP2 OUTS2 = true := by decide +kernel
theorem cell3_22 : fastCheck row3 22 FP2 OUTS2 = true := by decide +kernel
theorem cell3_23 : fastCheck row3 23 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
