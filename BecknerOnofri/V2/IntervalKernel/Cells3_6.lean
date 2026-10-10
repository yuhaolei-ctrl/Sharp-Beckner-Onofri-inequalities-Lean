module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 48..55 of row 3

Each `cell3_k` is `decide +kernel` of the fast checker `fastCheck row3 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell3_48 : fastCheck row3 48 FP2 OUTS2 = true := by decide +kernel
theorem cell3_49 : fastCheck row3 49 FP2 OUTS2 = true := by decide +kernel
theorem cell3_50 : fastCheck row3 50 FP2 OUTS2 = true := by decide +kernel
theorem cell3_51 : fastCheck row3 51 FP2 OUTS2 = true := by decide +kernel
theorem cell3_52 : fastCheck row3 52 FP2 OUTS2 = true := by decide +kernel
theorem cell3_53 : fastCheck row3 53 FP2 OUTS2 = true := by decide +kernel
theorem cell3_54 : fastCheck row3 54 FP2 OUTS2 = true := by decide +kernel
theorem cell3_55 : fastCheck row3 55 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
