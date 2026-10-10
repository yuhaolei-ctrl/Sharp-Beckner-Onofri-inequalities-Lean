module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 0..7 of row 3

Each `cell3_k` is `decide +kernel` of the fast checker `fastCheck row3 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell3_0 : fastCheck row3 0 FP2 OUTS2 = true := by decide +kernel
theorem cell3_1 : fastCheck row3 1 FP2 OUTS2 = true := by decide +kernel
theorem cell3_2 : fastCheck row3 2 FP2 OUTS2 = true := by decide +kernel
theorem cell3_3 : fastCheck row3 3 FP2 OUTS2 = true := by decide +kernel
theorem cell3_4 : fastCheck row3 4 FP2 OUTS2 = true := by decide +kernel
theorem cell3_5 : fastCheck row3 5 FP2 OUTS2 = true := by decide +kernel
theorem cell3_6 : fastCheck row3 6 FP2 OUTS2 = true := by decide +kernel
theorem cell3_7 : fastCheck row3 7 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
