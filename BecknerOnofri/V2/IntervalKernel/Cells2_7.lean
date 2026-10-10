module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 56..63 of row 2

Each `cell2_k` is `decide +kernel` of the fast checker `fastCheck row2 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell2_56 : fastCheck row2 56 FP2 OUTS2 = true := by decide +kernel
theorem cell2_57 : fastCheck row2 57 FP2 OUTS2 = true := by decide +kernel
theorem cell2_58 : fastCheck row2 58 FP2 OUTS2 = true := by decide +kernel
theorem cell2_59 : fastCheck row2 59 FP2 OUTS2 = true := by decide +kernel
theorem cell2_60 : fastCheck row2 60 FP2 OUTS2 = true := by decide +kernel
theorem cell2_61 : fastCheck row2 61 FP2 OUTS2 = true := by decide +kernel
theorem cell2_62 : fastCheck row2 62 FP2 OUTS2 = true := by decide +kernel
theorem cell2_63 : fastCheck row2 63 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
