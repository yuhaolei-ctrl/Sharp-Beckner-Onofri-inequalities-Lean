module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 0..7 of row 1

Each `cell1_k` is `decide +kernel` of the fast checker `fastCheck row1 k FP1 OUTS1`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell1_0 : fastCheck row1 0 FP1 OUTS1 = true := by decide +kernel
theorem cell1_1 : fastCheck row1 1 FP1 OUTS1 = true := by decide +kernel
theorem cell1_2 : fastCheck row1 2 FP1 OUTS1 = true := by decide +kernel
theorem cell1_3 : fastCheck row1 3 FP1 OUTS1 = true := by decide +kernel
theorem cell1_4 : fastCheck row1 4 FP1 OUTS1 = true := by decide +kernel
theorem cell1_5 : fastCheck row1 5 FP1 OUTS1 = true := by decide +kernel
theorem cell1_6 : fastCheck row1 6 FP1 OUTS1 = true := by decide +kernel
theorem cell1_7 : fastCheck row1 7 FP1 OUTS1 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
