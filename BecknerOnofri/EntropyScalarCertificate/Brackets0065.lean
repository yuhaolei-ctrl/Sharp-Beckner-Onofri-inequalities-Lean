import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0162
import BecknerOnofri.EntropyScalarCertificate.Bessel0163
import BecknerOnofri.EntropyScalarCertificate.Bessel0164
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0065
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1040b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨32,by decide⟩
def lo1040b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨33,by decide⟩
def lo1040 : CheckedMoment :=
  CheckedMoment.ofBessel lo1040b1 lo1040b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1040b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨37,by decide⟩
def hi1040b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨38,by decide⟩
def hi1040 : CheckedMoment :=
  CheckedMoment.ofBessel hi1040b1 hi1040b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1040 : meanBracketCheck (261/500) lo1040 hi1040=true := by decide +kernel
def bracket1040 : MeanBracket := meanBracketOfMoments (261/500) lo1040 hi1040 accepted1040
def lo1041b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨42,by decide⟩
def lo1041b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨43,by decide⟩
def lo1041 : CheckedMoment :=
  CheckedMoment.ofBessel lo1041b1 lo1041b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1041b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨47,by decide⟩
def hi1041b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨48,by decide⟩
def hi1041 : CheckedMoment :=
  CheckedMoment.ofBessel hi1041b1 hi1041b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1041 : meanBracketCheck (523/1000) lo1041 hi1041=true := by decide +kernel
def bracket1041 : MeanBracket := meanBracketOfMoments (523/1000) lo1041 hi1041 accepted1041
def lo1042b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨52,by decide⟩
def lo1042b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨53,by decide⟩
def lo1042 : CheckedMoment :=
  CheckedMoment.ofBessel lo1042b1 lo1042b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1042b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨57,by decide⟩
def hi1042b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨58,by decide⟩
def hi1042 : CheckedMoment :=
  CheckedMoment.ofBessel hi1042b1 hi1042b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1042 : meanBracketCheck (131/250) lo1042 hi1042=true := by decide +kernel
def bracket1042 : MeanBracket := meanBracketOfMoments (131/250) lo1042 hi1042 accepted1042
def lo1043b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨62,by decide⟩
def lo1043b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨63,by decide⟩
def lo1043 : CheckedMoment :=
  CheckedMoment.ofBessel lo1043b1 lo1043b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1043b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨3,by decide⟩
def hi1043b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨4,by decide⟩
def hi1043 : CheckedMoment :=
  CheckedMoment.ofBessel hi1043b1 hi1043b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1043 : meanBracketCheck (21/40) lo1043 hi1043=true := by decide +kernel
def bracket1043 : MeanBracket := meanBracketOfMoments (21/40) lo1043 hi1043 accepted1043
def lo1044b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨8,by decide⟩
def lo1044b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨9,by decide⟩
def lo1044 : CheckedMoment :=
  CheckedMoment.ofBessel lo1044b1 lo1044b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1044b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨13,by decide⟩
def hi1044b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨14,by decide⟩
def hi1044 : CheckedMoment :=
  CheckedMoment.ofBessel hi1044b1 hi1044b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1044 : meanBracketCheck (263/500) lo1044 hi1044=true := by decide +kernel
def bracket1044 : MeanBracket := meanBracketOfMoments (263/500) lo1044 hi1044 accepted1044
def lo1045b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨18,by decide⟩
def lo1045b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨19,by decide⟩
def lo1045 : CheckedMoment :=
  CheckedMoment.ofBessel lo1045b1 lo1045b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1045b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨23,by decide⟩
def hi1045b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨24,by decide⟩
def hi1045 : CheckedMoment :=
  CheckedMoment.ofBessel hi1045b1 hi1045b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1045 : meanBracketCheck (527/1000) lo1045 hi1045=true := by decide +kernel
def bracket1045 : MeanBracket := meanBracketOfMoments (527/1000) lo1045 hi1045 accepted1045
def lo1046b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨28,by decide⟩
def lo1046b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨29,by decide⟩
def lo1046 : CheckedMoment :=
  CheckedMoment.ofBessel lo1046b1 lo1046b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1046b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨33,by decide⟩
def hi1046b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨34,by decide⟩
def hi1046 : CheckedMoment :=
  CheckedMoment.ofBessel hi1046b1 hi1046b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1046 : meanBracketCheck (66/125) lo1046 hi1046=true := by decide +kernel
def bracket1046 : MeanBracket := meanBracketOfMoments (66/125) lo1046 hi1046 accepted1046
def lo1047b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨38,by decide⟩
def lo1047b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨39,by decide⟩
def lo1047 : CheckedMoment :=
  CheckedMoment.ofBessel lo1047b1 lo1047b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1047b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨43,by decide⟩
def hi1047b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨44,by decide⟩
def hi1047 : CheckedMoment :=
  CheckedMoment.ofBessel hi1047b1 hi1047b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1047 : meanBracketCheck (529/1000) lo1047 hi1047=true := by decide +kernel
def bracket1047 : MeanBracket := meanBracketOfMoments (529/1000) lo1047 hi1047 accepted1047
def lo1048b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨48,by decide⟩
def lo1048b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨49,by decide⟩
def lo1048 : CheckedMoment :=
  CheckedMoment.ofBessel lo1048b1 lo1048b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1048b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨53,by decide⟩
def hi1048b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨54,by decide⟩
def hi1048 : CheckedMoment :=
  CheckedMoment.ofBessel hi1048b1 hi1048b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1048 : meanBracketCheck (53/100) lo1048 hi1048=true := by decide +kernel
def bracket1048 : MeanBracket := meanBracketOfMoments (53/100) lo1048 hi1048 accepted1048
def lo1049b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨58,by decide⟩
def lo1049b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨59,by decide⟩
def lo1049 : CheckedMoment :=
  CheckedMoment.ofBessel lo1049b1 lo1049b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1049b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨63,by decide⟩
def hi1049b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨0,by decide⟩
def hi1049 : CheckedMoment :=
  CheckedMoment.ofBessel hi1049b1 hi1049b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1049 : meanBracketCheck (531/1000) lo1049 hi1049=true := by decide +kernel
def bracket1049 : MeanBracket := meanBracketOfMoments (531/1000) lo1049 hi1049 accepted1049
def lo1050b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨4,by decide⟩
def lo1050b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨5,by decide⟩
def lo1050 : CheckedMoment :=
  CheckedMoment.ofBessel lo1050b1 lo1050b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1050b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨9,by decide⟩
def hi1050b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨10,by decide⟩
def hi1050 : CheckedMoment :=
  CheckedMoment.ofBessel hi1050b1 hi1050b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1050 : meanBracketCheck (133/250) lo1050 hi1050=true := by decide +kernel
def bracket1050 : MeanBracket := meanBracketOfMoments (133/250) lo1050 hi1050 accepted1050
def lo1051b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨14,by decide⟩
def lo1051b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨15,by decide⟩
def lo1051 : CheckedMoment :=
  CheckedMoment.ofBessel lo1051b1 lo1051b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1051b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨19,by decide⟩
def hi1051b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨20,by decide⟩
def hi1051 : CheckedMoment :=
  CheckedMoment.ofBessel hi1051b1 hi1051b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1051 : meanBracketCheck (533/1000) lo1051 hi1051=true := by decide +kernel
def bracket1051 : MeanBracket := meanBracketOfMoments (533/1000) lo1051 hi1051 accepted1051
def lo1052b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨24,by decide⟩
def lo1052b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨25,by decide⟩
def lo1052 : CheckedMoment :=
  CheckedMoment.ofBessel lo1052b1 lo1052b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1052b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨29,by decide⟩
def hi1052b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨30,by decide⟩
def hi1052 : CheckedMoment :=
  CheckedMoment.ofBessel hi1052b1 hi1052b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1052 : meanBracketCheck (267/500) lo1052 hi1052=true := by decide +kernel
def bracket1052 : MeanBracket := meanBracketOfMoments (267/500) lo1052 hi1052 accepted1052
def lo1053b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨34,by decide⟩
def lo1053b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨35,by decide⟩
def lo1053 : CheckedMoment :=
  CheckedMoment.ofBessel lo1053b1 lo1053b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1053b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨39,by decide⟩
def hi1053b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨40,by decide⟩
def hi1053 : CheckedMoment :=
  CheckedMoment.ofBessel hi1053b1 hi1053b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1053 : meanBracketCheck (107/200) lo1053 hi1053=true := by decide +kernel
def bracket1053 : MeanBracket := meanBracketOfMoments (107/200) lo1053 hi1053 accepted1053
def lo1054b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨44,by decide⟩
def lo1054b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨45,by decide⟩
def lo1054 : CheckedMoment :=
  CheckedMoment.ofBessel lo1054b1 lo1054b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1054b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨49,by decide⟩
def hi1054b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨50,by decide⟩
def hi1054 : CheckedMoment :=
  CheckedMoment.ofBessel hi1054b1 hi1054b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1054 : meanBracketCheck (67/125) lo1054 hi1054=true := by decide +kernel
def bracket1054 : MeanBracket := meanBracketOfMoments (67/125) lo1054 hi1054 accepted1054
def lo1055b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨54,by decide⟩
def lo1055b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨55,by decide⟩
def lo1055 : CheckedMoment :=
  CheckedMoment.ofBessel lo1055b1 lo1055b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1055b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨59,by decide⟩
def hi1055b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0164.rows BesselBatch0164.accepted ⟨60,by decide⟩
def hi1055 : CheckedMoment :=
  CheckedMoment.ofBessel hi1055b1 hi1055b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1055 : meanBracketCheck (537/1000) lo1055 hi1055=true := by decide +kernel
def bracket1055 : MeanBracket := meanBracketOfMoments (537/1000) lo1055 hi1055 accepted1055
#print axioms bracket1040
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0065
