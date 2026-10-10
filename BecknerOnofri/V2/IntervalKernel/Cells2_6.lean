module

public import BecknerOnofri.V2.IntervalKernel.FProg

@[expose] public section

/-!
# Kernel proofs of cells 48..55 of row 2

Each `cell2_k` is `decide +kernel` of the fast checker `fastCheck row2 k FP2 OUTS2`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem cell2_48 : fastCheck row2 48 FP2 OUTS2 = true := by decide +kernel
theorem cell2_49 : fastCheck row2 49 FP2 OUTS2 = true := by decide +kernel
theorem cell2_50 : fastCheck row2 50 FP2 OUTS2 = true := by decide +kernel
theorem cell2_51 : fastCheck row2 51 FP2 OUTS2 = true := by decide +kernel
theorem cell2_52 : fastCheck row2 52 FP2 OUTS2 = true := by decide +kernel
theorem cell2_53 : fastCheck row2 53 FP2 OUTS2 = true := by decide +kernel
theorem cell2_54 : fastCheck row2 54 FP2 OUTS2 = true := by decide +kernel
theorem cell2_55 : fastCheck row2 55 FP2 OUTS2 = true := by decide +kernel

end BecknerOnofri.V2.IntervalKernel
