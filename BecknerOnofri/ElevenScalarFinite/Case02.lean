module

public import Legacy.BecknerOnofri.FiniteData02
public import BecknerOnofri.ElevenScalarFinite.Core

@[expose] public section
/-! Generated rational candidate data. Every equality and inequality below
is checked by Lean's kernel; generation supplies no trusted premise.
Squared radii ≥ 65 retain their full polynomial mass with the upper weight
65^(-11/2), as in the proved generic polynomialEnergy_le_upper lemma. -/
namespace BecknerOnofri.HighDim.Eleven.ScalarFinite.Case02
open Legacy.D10.FiniteScalar Legacy.BecknerOnofri.FiniteScalar
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lastStage : Array Nat := #[362797056, 5321023488, 35473489920, 141893959680, 379714148352, 724053344256, 1048175935488, 1275293859840, 1483052820480, 1704989417472, 1782353362944, 1645917765632, 1483052820480, 1378010726400, 1180379250688, 892238561280, 691289026560, 566520627200, 403979304960, 255499960320, 186334900224, 136317468672, 76526714880, 43772805120, 32929763328, 18972721152, 7963017216, 5449973760, 3688058880, 1260847104, 583925760, 519045120, 182138880, 36495360, 48660480, 21626880, 1013760, 2703360, 1802240, 0, 67584, 90112, 0, 0, 2048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem lastStage_correct : shellArray 2 11 = lastStage := by
  rw [show 11 = 10+1 by rfl, shellArray_succ,
    Legacy.BecknerOnofri.FiniteScalar.Case02.stage_correct 10 (by decide),
    ← Legacy.BecknerOnofri.FiniteScalar.Case02.row_correct]
  decide +kernel
theorem checked : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 2 + 1/2000 <
    11 * harmonic 2 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [lastStage_correct]
  decide +kernel
#print axioms checked
end BecknerOnofri.HighDim.Eleven.ScalarFinite.Case02
