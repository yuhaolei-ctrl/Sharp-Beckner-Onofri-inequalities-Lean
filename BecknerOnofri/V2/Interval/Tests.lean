module

public import BecknerOnofri.V2.Interval.Check

@[expose] public section

/-!
# Negative and positive sanity tests of the interval layer

Every failure mode of the interpreter that `checkCell` relies on is exercised on tiny inputs and
proved by `decide`/`rfl` (kernel evaluation, no native code): reciprocal of an interval containing
zero, logarithm of a non-positive interval, empty meet, bad register reference, bad denominator.
-/

namespace BecknerOnofri.V2.Interval

/-- Reciprocal of an interval containing zero is rejected (both closed-end cases and the interior). -/
theorem recip_zero_mid : (Iv.recip ⟨-1, 1⟩) = none := by decide
theorem recip_zero_lo : (Iv.recip ⟨0, 5⟩) = none := by decide
theorem recip_zero_hi : (Iv.recip ⟨-5, 0⟩) = none := by decide
/-- Reciprocal of a strictly negative interval is accepted. -/
theorem recip_neg_ok : (Iv.recip ⟨-5, -1⟩).isSome = true := by decide
/-- Logarithm of an interval with a non-positive left end point is rejected. -/
theorem log_nonpos_lo : (Iv.log ⟨0, 5⟩) = none := by decide
theorem log_neg : (Iv.log ⟨-5, -1⟩) = none := by decide
/-- Empty meet is a failure. -/
theorem meet_empty : (Iv.meet? ⟨0, 1⟩ ⟨2, 3⟩) = none := by decide
theorem meet_ok : (Iv.meet? ⟨0, 2⟩ ⟨1, 3⟩) = some ⟨1, 2⟩ := by decide
/-- Jets: reciprocal and logarithm of a jet whose zeroth entry contains zero fail. -/
theorem jet_recip_zero : Jet.recip (Jet.const ⟨-1, 1⟩) = none := by decide
theorem jet_log_zero : Jet.log (Jet.const ⟨0, 1⟩) = none := by decide
/-- Constants with zero denominator are rejected. -/
theorem const_zero_den : (Const.q 1 0).toIv = none := by decide
theorem const_inv_zero : (Const.inv 0 3).toIv = none := by decide

/-- A cell context used for the program-level tests: the first cell of the first row. -/
def testCtx : Ctx := (row1.cell 0).ctx

/-- A reference to a register that does not exist fails the run. -/
theorem run_bad_reference : runRS testCtx [Op.add 0 0] = none := by decide +kernel
theorem run_bad_reference' : runRS testCtx [Op.var, Op.mul 0 1] = none := by decide +kernel
/-- The variable ranges over a cell containing `0`, so its reciprocal and logarithm fail. -/
theorem run_inv_zero : runRS testCtx [Op.var, Op.inv 0] = none := by decide +kernel
theorem run_log_zero : runRS testCtx [Op.var, Op.log 0] = none := by decide +kernel
/-- A malformed constant fails the run. -/
theorem run_bad_const : runRS testCtx [Op.const (Const.q 1 0)] = none := by decide +kernel
/-- A well-formed short program succeeds. -/
theorem run_ok : (runRS testCtx [Op.var, Op.const (Const.q 1 1), Op.add 0 1]).isSome = true := by
  decide +kernel

end BecknerOnofri.V2.Interval
