module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 16..23 of row 2

Each `cell2_k` is `decide +kernel` of the fast checker `fastCheck row2 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell2_16 : fastCheck row2 16 FP2 OUTS2 = true := by decide +kernel
theorem cell2_17 : fastCheck row2 17 FP2 OUTS2 = true := by decide +kernel
theorem cell2_18 : fastCheck row2 18 FP2 OUTS2 = true := by decide +kernel
theorem cell2_19 : fastCheck row2 19 FP2 OUTS2 = true := by decide +kernel
theorem cell2_20 : fastCheck row2 20 FP2 OUTS2 = true := by decide +kernel
theorem cell2_21 : fastCheck row2 21 FP2 OUTS2 = true := by decide +kernel
theorem cell2_22 : fastCheck row2 22 FP2 OUTS2 = true := by decide +kernel
theorem cell2_23 : fastCheck row2 23 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
