module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 16..23 of row 1

Each `cell1_k` is `decide +kernel` of the fast checker `fastCheck row1 k FP1 OUTS1`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell1_16 : fastCheck row1 16 FP1 OUTS1 = true := by decide +kernel
theorem cell1_17 : fastCheck row1 17 FP1 OUTS1 = true := by decide +kernel
theorem cell1_18 : fastCheck row1 18 FP1 OUTS1 = true := by decide +kernel
theorem cell1_19 : fastCheck row1 19 FP1 OUTS1 = true := by decide +kernel
theorem cell1_20 : fastCheck row1 20 FP1 OUTS1 = true := by decide +kernel
theorem cell1_21 : fastCheck row1 21 FP1 OUTS1 = true := by decide +kernel
theorem cell1_22 : fastCheck row1 22 FP1 OUTS1 = true := by decide +kernel
theorem cell1_23 : fastCheck row1 23 FP1 OUTS1 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
