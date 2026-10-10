module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 40..47 of row 3

Each `cell3_k` is `decide +kernel` of the fast checker `fastCheck row3 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell3_40 : fastCheck row3 40 FP2 OUTS2 = true := by decide +kernel
theorem cell3_41 : fastCheck row3 41 FP2 OUTS2 = true := by decide +kernel
theorem cell3_42 : fastCheck row3 42 FP2 OUTS2 = true := by decide +kernel
theorem cell3_43 : fastCheck row3 43 FP2 OUTS2 = true := by decide +kernel
theorem cell3_44 : fastCheck row3 44 FP2 OUTS2 = true := by decide +kernel
theorem cell3_45 : fastCheck row3 45 FP2 OUTS2 = true := by decide +kernel
theorem cell3_46 : fastCheck row3 46 FP2 OUTS2 = true := by decide +kernel
theorem cell3_47 : fastCheck row3 47 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
