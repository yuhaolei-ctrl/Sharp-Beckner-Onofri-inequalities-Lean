import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0475
import BecknerOnofri.EntropyScalarCertificate.Bessel0476
import BecknerOnofri.EntropyScalarCertificate.Bessel0477
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0190
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo3040b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨0,by decide⟩
def lo3040b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨1,by decide⟩
def lo3040 : CheckedMoment :=
  CheckedMoment.ofBessel lo3040b1 lo3040b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3040b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨5,by decide⟩
def hi3040b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨6,by decide⟩
def hi3040 : CheckedMoment :=
  CheckedMoment.ofBessel hi3040b1 hi3040b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3040 : meanBracketCheck (6241/6250) lo3040 hi3040=true := by decide +kernel
def bracket3040 : MeanBracket := meanBracketOfMoments (6241/6250) lo3040 hi3040 accepted3040
def lo3041b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨10,by decide⟩
def lo3041b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨11,by decide⟩
def lo3041 : CheckedMoment :=
  CheckedMoment.ofBessel lo3041b1 lo3041b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3041b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨15,by decide⟩
def hi3041b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨16,by decide⟩
def hi3041 : CheckedMoment :=
  CheckedMoment.ofBessel hi3041b1 hi3041b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3041 : meanBracketCheck (199713/200000) lo3041 hi3041=true := by decide +kernel
def bracket3041 : MeanBracket := meanBracketOfMoments (199713/200000) lo3041 hi3041 accepted3041
def lo3042b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨20,by decide⟩
def lo3042b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨21,by decide⟩
def lo3042 : CheckedMoment :=
  CheckedMoment.ofBessel lo3042b1 lo3042b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3042b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨25,by decide⟩
def hi3042b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨26,by decide⟩
def hi3042 : CheckedMoment :=
  CheckedMoment.ofBessel hi3042b1 hi3042b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3042 : meanBracketCheck (99857/100000) lo3042 hi3042=true := by decide +kernel
def bracket3042 : MeanBracket := meanBracketOfMoments (99857/100000) lo3042 hi3042 accepted3042
def lo3043b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨30,by decide⟩
def lo3043b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨31,by decide⟩
def lo3043 : CheckedMoment :=
  CheckedMoment.ofBessel lo3043b1 lo3043b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3043b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨35,by decide⟩
def hi3043b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨36,by decide⟩
def hi3043 : CheckedMoment :=
  CheckedMoment.ofBessel hi3043b1 hi3043b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3043 : meanBracketCheck (39943/40000) lo3043 hi3043=true := by decide +kernel
def bracket3043 : MeanBracket := meanBracketOfMoments (39943/40000) lo3043 hi3043 accepted3043
def lo3044b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨40,by decide⟩
def lo3044b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨41,by decide⟩
def lo3044 : CheckedMoment :=
  CheckedMoment.ofBessel lo3044b1 lo3044b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3044b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨45,by decide⟩
def hi3044b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨46,by decide⟩
def hi3044 : CheckedMoment :=
  CheckedMoment.ofBessel hi3044b1 hi3044b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3044 : meanBracketCheck (49929/50000) lo3044 hi3044=true := by decide +kernel
def bracket3044 : MeanBracket := meanBracketOfMoments (49929/50000) lo3044 hi3044 accepted3044
def lo3045b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨50,by decide⟩
def lo3045b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨51,by decide⟩
def lo3045 : CheckedMoment :=
  CheckedMoment.ofBessel lo3045b1 lo3045b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3045b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨55,by decide⟩
def hi3045b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨56,by decide⟩
def hi3045 : CheckedMoment :=
  CheckedMoment.ofBessel hi3045b1 hi3045b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3045 : meanBracketCheck (199717/200000) lo3045 hi3045=true := by decide +kernel
def bracket3045 : MeanBracket := meanBracketOfMoments (199717/200000) lo3045 hi3045 accepted3045
def lo3046b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨60,by decide⟩
def lo3046b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨61,by decide⟩
def lo3046 : CheckedMoment :=
  CheckedMoment.ofBessel lo3046b1 lo3046b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3046b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨1,by decide⟩
def hi3046b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨2,by decide⟩
def hi3046 : CheckedMoment :=
  CheckedMoment.ofBessel hi3046b1 hi3046b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3046 : meanBracketCheck (99859/100000) lo3046 hi3046=true := by decide +kernel
def bracket3046 : MeanBracket := meanBracketOfMoments (99859/100000) lo3046 hi3046 accepted3046
def lo3047b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨6,by decide⟩
def lo3047b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨7,by decide⟩
def lo3047 : CheckedMoment :=
  CheckedMoment.ofBessel lo3047b1 lo3047b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3047b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨11,by decide⟩
def hi3047b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨12,by decide⟩
def hi3047 : CheckedMoment :=
  CheckedMoment.ofBessel hi3047b1 hi3047b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3047 : meanBracketCheck (199719/200000) lo3047 hi3047=true := by decide +kernel
def bracket3047 : MeanBracket := meanBracketOfMoments (199719/200000) lo3047 hi3047 accepted3047
def lo3048b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨16,by decide⟩
def lo3048b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨17,by decide⟩
def lo3048 : CheckedMoment :=
  CheckedMoment.ofBessel lo3048b1 lo3048b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3048b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨21,by decide⟩
def hi3048b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨22,by decide⟩
def hi3048 : CheckedMoment :=
  CheckedMoment.ofBessel hi3048b1 hi3048b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3048 : meanBracketCheck (4993/5000) lo3048 hi3048=true := by decide +kernel
def bracket3048 : MeanBracket := meanBracketOfMoments (4993/5000) lo3048 hi3048 accepted3048
def lo3049b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨26,by decide⟩
def lo3049b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨27,by decide⟩
def lo3049 : CheckedMoment :=
  CheckedMoment.ofBessel lo3049b1 lo3049b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3049b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨31,by decide⟩
def hi3049b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨32,by decide⟩
def hi3049 : CheckedMoment :=
  CheckedMoment.ofBessel hi3049b1 hi3049b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3049 : meanBracketCheck (199721/200000) lo3049 hi3049=true := by decide +kernel
def bracket3049 : MeanBracket := meanBracketOfMoments (199721/200000) lo3049 hi3049 accepted3049
def lo3050b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨36,by decide⟩
def lo3050b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨37,by decide⟩
def lo3050 : CheckedMoment :=
  CheckedMoment.ofBessel lo3050b1 lo3050b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3050b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨41,by decide⟩
def hi3050b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨42,by decide⟩
def hi3050 : CheckedMoment :=
  CheckedMoment.ofBessel hi3050b1 hi3050b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3050 : meanBracketCheck (99861/100000) lo3050 hi3050=true := by decide +kernel
def bracket3050 : MeanBracket := meanBracketOfMoments (99861/100000) lo3050 hi3050 accepted3050
def lo3051b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨46,by decide⟩
def lo3051b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨47,by decide⟩
def lo3051 : CheckedMoment :=
  CheckedMoment.ofBessel lo3051b1 lo3051b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3051b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨51,by decide⟩
def hi3051b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨52,by decide⟩
def hi3051 : CheckedMoment :=
  CheckedMoment.ofBessel hi3051b1 hi3051b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3051 : meanBracketCheck (199723/200000) lo3051 hi3051=true := by decide +kernel
def bracket3051 : MeanBracket := meanBracketOfMoments (199723/200000) lo3051 hi3051 accepted3051
def lo3052b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨56,by decide⟩
def lo3052b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨57,by decide⟩
def lo3052 : CheckedMoment :=
  CheckedMoment.ofBessel lo3052b1 lo3052b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3052b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨61,by decide⟩
def hi3052b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨62,by decide⟩
def hi3052 : CheckedMoment :=
  CheckedMoment.ofBessel hi3052b1 hi3052b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3052 : meanBracketCheck (49931/50000) lo3052 hi3052=true := by decide +kernel
def bracket3052 : MeanBracket := meanBracketOfMoments (49931/50000) lo3052 hi3052 accepted3052
def lo3053b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨2,by decide⟩
def lo3053b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨3,by decide⟩
def lo3053 : CheckedMoment :=
  CheckedMoment.ofBessel lo3053b1 lo3053b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3053b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨7,by decide⟩
def hi3053b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨8,by decide⟩
def hi3053 : CheckedMoment :=
  CheckedMoment.ofBessel hi3053b1 hi3053b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3053 : meanBracketCheck (7989/8000) lo3053 hi3053=true := by decide +kernel
def bracket3053 : MeanBracket := meanBracketOfMoments (7989/8000) lo3053 hi3053 accepted3053
def lo3054b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨12,by decide⟩
def lo3054b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨13,by decide⟩
def lo3054 : CheckedMoment :=
  CheckedMoment.ofBessel lo3054b1 lo3054b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3054b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨17,by decide⟩
def hi3054b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨18,by decide⟩
def hi3054 : CheckedMoment :=
  CheckedMoment.ofBessel hi3054b1 hi3054b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3054 : meanBracketCheck (99863/100000) lo3054 hi3054=true := by decide +kernel
def bracket3054 : MeanBracket := meanBracketOfMoments (99863/100000) lo3054 hi3054 accepted3054
def lo3055b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨22,by decide⟩
def lo3055b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨23,by decide⟩
def lo3055 : CheckedMoment :=
  CheckedMoment.ofBessel lo3055b1 lo3055b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3055b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨27,by decide⟩
def hi3055b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨28,by decide⟩
def hi3055 : CheckedMoment :=
  CheckedMoment.ofBessel hi3055b1 hi3055b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3055 : meanBracketCheck (199727/200000) lo3055 hi3055=true := by decide +kernel
def bracket3055 : MeanBracket := meanBracketOfMoments (199727/200000) lo3055 hi3055 accepted3055
#print axioms bracket3040
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0190
