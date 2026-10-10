module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 40..47 of row 2

Each `cell2_k` is `decide +kernel` of the fast checker `fastCheck row2 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell2_40 : fastCheck row2 40 FP2 OUTS2 = true := by decide +kernel
theorem cell2_41 : fastCheck row2 41 FP2 OUTS2 = true := by decide +kernel
theorem cell2_42 : fastCheck row2 42 FP2 OUTS2 = true := by decide +kernel
theorem cell2_43 : fastCheck row2 43 FP2 OUTS2 = true := by decide +kernel
theorem cell2_44 : fastCheck row2 44 FP2 OUTS2 = true := by decide +kernel
theorem cell2_45 : fastCheck row2 45 FP2 OUTS2 = true := by decide +kernel
theorem cell2_46 : fastCheck row2 46 FP2 OUTS2 = true := by decide +kernel
theorem cell2_47 : fastCheck row2 47 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
