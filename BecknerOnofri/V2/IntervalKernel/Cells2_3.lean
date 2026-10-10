module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 24..31 of row 2

Each `cell2_k` is `decide +kernel` of the fast checker `fastCheck row2 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell2_24 : fastCheck row2 24 FP2 OUTS2 = true := by decide +kernel
theorem cell2_25 : fastCheck row2 25 FP2 OUTS2 = true := by decide +kernel
theorem cell2_26 : fastCheck row2 26 FP2 OUTS2 = true := by decide +kernel
theorem cell2_27 : fastCheck row2 27 FP2 OUTS2 = true := by decide +kernel
theorem cell2_28 : fastCheck row2 28 FP2 OUTS2 = true := by decide +kernel
theorem cell2_29 : fastCheck row2 29 FP2 OUTS2 = true := by decide +kernel
theorem cell2_30 : fastCheck row2 30 FP2 OUTS2 = true := by decide +kernel
theorem cell2_31 : fastCheck row2 31 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
