import Legacy.BecknerOnofri.FiniteData01
import BecknerOnofri.ElevenScalarFinite.Core
/-! Generated rational candidate data. Every equality and inequality below
is checked by Lean's kernel; generation supplies no trusted premise.
Squared radii ≥ 65 retain their full polynomial mass with the upper weight
65^(-11/2), as in the proved generic polynomialEnergy_le_upper lemma. -/
namespace BecknerOnofri.HighDim.Eleven.ScalarFinite.Case01
open Legacy.D10.FiniteScalar Legacy.BecknerOnofri.FiniteScalar
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lastStage : Array Nat := #[2048, 22528, 112640, 337920, 675840, 946176, 946176, 675840, 337920, 112640, 22528, 2048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem lastStage_correct : shellArray 1 11 = lastStage := by
  rw [show 11 = 10+1 by rfl, shellArray_succ,
    Legacy.BecknerOnofri.FiniteScalar.Case01.stage_correct 10 (by decide),
    ← Legacy.BecknerOnofri.FiniteScalar.Case01.row_correct]
  decide +kernel
theorem checked : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 1 + 1/2000 <
    11 * harmonic 1 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [lastStage_correct]
  decide +kernel
#print axioms checked
end BecknerOnofri.HighDim.Eleven.ScalarFinite.Case01
