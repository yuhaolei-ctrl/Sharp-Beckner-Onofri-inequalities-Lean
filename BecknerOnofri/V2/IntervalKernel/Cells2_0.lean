module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 0..7 of row 2

Each `cell2_k` is `decide +kernel` of the fast checker `fastCheck row2 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell2_0 : fastCheck row2 0 FP2 OUTS2 = true := by decide +kernel
theorem cell2_1 : fastCheck row2 1 FP2 OUTS2 = true := by decide +kernel
theorem cell2_2 : fastCheck row2 2 FP2 OUTS2 = true := by decide +kernel
theorem cell2_3 : fastCheck row2 3 FP2 OUTS2 = true := by decide +kernel
theorem cell2_4 : fastCheck row2 4 FP2 OUTS2 = true := by decide +kernel
theorem cell2_5 : fastCheck row2 5 FP2 OUTS2 = true := by decide +kernel
theorem cell2_6 : fastCheck row2 6 FP2 OUTS2 = true := by decide +kernel
theorem cell2_7 : fastCheck row2 7 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
