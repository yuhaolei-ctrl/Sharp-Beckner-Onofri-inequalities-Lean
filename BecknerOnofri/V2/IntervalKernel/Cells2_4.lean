module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 32..39 of row 2

Each `cell2_k` is `decide +kernel` of the fast checker `fastCheck row2 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell2_32 : fastCheck row2 32 FP2 OUTS2 = true := by decide +kernel
theorem cell2_33 : fastCheck row2 33 FP2 OUTS2 = true := by decide +kernel
theorem cell2_34 : fastCheck row2 34 FP2 OUTS2 = true := by decide +kernel
theorem cell2_35 : fastCheck row2 35 FP2 OUTS2 = true := by decide +kernel
theorem cell2_36 : fastCheck row2 36 FP2 OUTS2 = true := by decide +kernel
theorem cell2_37 : fastCheck row2 37 FP2 OUTS2 = true := by decide +kernel
theorem cell2_38 : fastCheck row2 38 FP2 OUTS2 = true := by decide +kernel
theorem cell2_39 : fastCheck row2 39 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
