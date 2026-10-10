module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 32..39 of row 3

Each `cell3_k` is `decide +kernel` of the fast checker `fastCheck row3 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell3_32 : fastCheck row3 32 FP2 OUTS2 = true := by decide +kernel
theorem cell3_33 : fastCheck row3 33 FP2 OUTS2 = true := by decide +kernel
theorem cell3_34 : fastCheck row3 34 FP2 OUTS2 = true := by decide +kernel
theorem cell3_35 : fastCheck row3 35 FP2 OUTS2 = true := by decide +kernel
theorem cell3_36 : fastCheck row3 36 FP2 OUTS2 = true := by decide +kernel
theorem cell3_37 : fastCheck row3 37 FP2 OUTS2 = true := by decide +kernel
theorem cell3_38 : fastCheck row3 38 FP2 OUTS2 = true := by decide +kernel
theorem cell3_39 : fastCheck row3 39 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
