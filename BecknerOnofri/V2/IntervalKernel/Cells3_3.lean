module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 24..31 of row 3

Each `cell3_k` is `decide +kernel` of the fast checker `fastCheck row3 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell3_24 : fastCheck row3 24 FP2 OUTS2 = true := by decide +kernel
theorem cell3_25 : fastCheck row3 25 FP2 OUTS2 = true := by decide +kernel
theorem cell3_26 : fastCheck row3 26 FP2 OUTS2 = true := by decide +kernel
theorem cell3_27 : fastCheck row3 27 FP2 OUTS2 = true := by decide +kernel
theorem cell3_28 : fastCheck row3 28 FP2 OUTS2 = true := by decide +kernel
theorem cell3_29 : fastCheck row3 29 FP2 OUTS2 = true := by decide +kernel
theorem cell3_30 : fastCheck row3 30 FP2 OUTS2 = true := by decide +kernel
theorem cell3_31 : fastCheck row3 31 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
