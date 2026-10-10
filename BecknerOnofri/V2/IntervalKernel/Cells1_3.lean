module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 24..31 of row 1

Each `cell1_k` is `decide +kernel` of the fast checker `fastCheck row1 k FP1 OUTS1`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell1_24 : fastCheck row1 24 FP1 OUTS1 = true := by decide +kernel
theorem cell1_25 : fastCheck row1 25 FP1 OUTS1 = true := by decide +kernel
theorem cell1_26 : fastCheck row1 26 FP1 OUTS1 = true := by decide +kernel
theorem cell1_27 : fastCheck row1 27 FP1 OUTS1 = true := by decide +kernel
theorem cell1_28 : fastCheck row1 28 FP1 OUTS1 = true := by decide +kernel
theorem cell1_29 : fastCheck row1 29 FP1 OUTS1 = true := by decide +kernel
theorem cell1_30 : fastCheck row1 30 FP1 OUTS1 = true := by decide +kernel
theorem cell1_31 : fastCheck row1 31 FP1 OUTS1 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
