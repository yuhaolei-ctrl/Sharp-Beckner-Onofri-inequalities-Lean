module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 56..63 of row 3

Each `cell3_k` is `decide +kernel` of the fast checker `fastCheck row3 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell3_56 : fastCheck row3 56 FP2 OUTS2 = true := by decide +kernel
theorem cell3_57 : fastCheck row3 57 FP2 OUTS2 = true := by decide +kernel
theorem cell3_58 : fastCheck row3 58 FP2 OUTS2 = true := by decide +kernel
theorem cell3_59 : fastCheck row3 59 FP2 OUTS2 = true := by decide +kernel
theorem cell3_60 : fastCheck row3 60 FP2 OUTS2 = true := by decide +kernel
theorem cell3_61 : fastCheck row3 61 FP2 OUTS2 = true := by decide +kernel
theorem cell3_62 : fastCheck row3 62 FP2 OUTS2 = true := by decide +kernel
theorem cell3_63 : fastCheck row3 63 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
