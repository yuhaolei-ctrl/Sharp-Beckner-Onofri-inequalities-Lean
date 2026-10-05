import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0165
import BecknerOnofri.EntropyScalarCertificate.Bessel0166
import BecknerOnofri.EntropyScalarCertificate.Bessel0167
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0066
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1056b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨0,by decide⟩
def lo1056b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨1,by decide⟩
def lo1056 : CheckedMoment :=
  CheckedMoment.ofBessel lo1056b1 lo1056b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1056b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨5,by decide⟩
def hi1056b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨6,by decide⟩
def hi1056 : CheckedMoment :=
  CheckedMoment.ofBessel hi1056b1 hi1056b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1056 : meanBracketCheck (269/500) lo1056 hi1056=true := by decide +kernel
def bracket1056 : MeanBracket := meanBracketOfMoments (269/500) lo1056 hi1056 accepted1056
def lo1057b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨10,by decide⟩
def lo1057b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨11,by decide⟩
def lo1057 : CheckedMoment :=
  CheckedMoment.ofBessel lo1057b1 lo1057b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1057b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨15,by decide⟩
def hi1057b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨16,by decide⟩
def hi1057 : CheckedMoment :=
  CheckedMoment.ofBessel hi1057b1 hi1057b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1057 : meanBracketCheck (539/1000) lo1057 hi1057=true := by decide +kernel
def bracket1057 : MeanBracket := meanBracketOfMoments (539/1000) lo1057 hi1057 accepted1057
def lo1058b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨20,by decide⟩
def lo1058b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨21,by decide⟩
def lo1058 : CheckedMoment :=
  CheckedMoment.ofBessel lo1058b1 lo1058b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1058b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨25,by decide⟩
def hi1058b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨26,by decide⟩
def hi1058 : CheckedMoment :=
  CheckedMoment.ofBessel hi1058b1 hi1058b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1058 : meanBracketCheck (27/50) lo1058 hi1058=true := by decide +kernel
def bracket1058 : MeanBracket := meanBracketOfMoments (27/50) lo1058 hi1058 accepted1058
def lo1059b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨30,by decide⟩
def lo1059b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨31,by decide⟩
def lo1059 : CheckedMoment :=
  CheckedMoment.ofBessel lo1059b1 lo1059b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1059b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨35,by decide⟩
def hi1059b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨36,by decide⟩
def hi1059 : CheckedMoment :=
  CheckedMoment.ofBessel hi1059b1 hi1059b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1059 : meanBracketCheck (541/1000) lo1059 hi1059=true := by decide +kernel
def bracket1059 : MeanBracket := meanBracketOfMoments (541/1000) lo1059 hi1059 accepted1059
def lo1060b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨40,by decide⟩
def lo1060b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨41,by decide⟩
def lo1060 : CheckedMoment :=
  CheckedMoment.ofBessel lo1060b1 lo1060b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1060b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨45,by decide⟩
def hi1060b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨46,by decide⟩
def hi1060 : CheckedMoment :=
  CheckedMoment.ofBessel hi1060b1 hi1060b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1060 : meanBracketCheck (271/500) lo1060 hi1060=true := by decide +kernel
def bracket1060 : MeanBracket := meanBracketOfMoments (271/500) lo1060 hi1060 accepted1060
def lo1061b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨50,by decide⟩
def lo1061b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨51,by decide⟩
def lo1061 : CheckedMoment :=
  CheckedMoment.ofBessel lo1061b1 lo1061b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1061b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨55,by decide⟩
def hi1061b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨56,by decide⟩
def hi1061 : CheckedMoment :=
  CheckedMoment.ofBessel hi1061b1 hi1061b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1061 : meanBracketCheck (543/1000) lo1061 hi1061=true := by decide +kernel
def bracket1061 : MeanBracket := meanBracketOfMoments (543/1000) lo1061 hi1061 accepted1061
def lo1062b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨60,by decide⟩
def lo1062b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨61,by decide⟩
def lo1062 : CheckedMoment :=
  CheckedMoment.ofBessel lo1062b1 lo1062b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1062b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨1,by decide⟩
def hi1062b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨2,by decide⟩
def hi1062 : CheckedMoment :=
  CheckedMoment.ofBessel hi1062b1 hi1062b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1062 : meanBracketCheck (68/125) lo1062 hi1062=true := by decide +kernel
def bracket1062 : MeanBracket := meanBracketOfMoments (68/125) lo1062 hi1062 accepted1062
def lo1063b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨6,by decide⟩
def lo1063b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨7,by decide⟩
def lo1063 : CheckedMoment :=
  CheckedMoment.ofBessel lo1063b1 lo1063b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1063b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨11,by decide⟩
def hi1063b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨12,by decide⟩
def hi1063 : CheckedMoment :=
  CheckedMoment.ofBessel hi1063b1 hi1063b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1063 : meanBracketCheck (109/200) lo1063 hi1063=true := by decide +kernel
def bracket1063 : MeanBracket := meanBracketOfMoments (109/200) lo1063 hi1063 accepted1063
def lo1064b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨16,by decide⟩
def lo1064b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨17,by decide⟩
def lo1064 : CheckedMoment :=
  CheckedMoment.ofBessel lo1064b1 lo1064b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1064b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨21,by decide⟩
def hi1064b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨22,by decide⟩
def hi1064 : CheckedMoment :=
  CheckedMoment.ofBessel hi1064b1 hi1064b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1064 : meanBracketCheck (273/500) lo1064 hi1064=true := by decide +kernel
def bracket1064 : MeanBracket := meanBracketOfMoments (273/500) lo1064 hi1064 accepted1064
def lo1065b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨26,by decide⟩
def lo1065b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨27,by decide⟩
def lo1065 : CheckedMoment :=
  CheckedMoment.ofBessel lo1065b1 lo1065b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1065b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨31,by decide⟩
def hi1065b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨32,by decide⟩
def hi1065 : CheckedMoment :=
  CheckedMoment.ofBessel hi1065b1 hi1065b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1065 : meanBracketCheck (547/1000) lo1065 hi1065=true := by decide +kernel
def bracket1065 : MeanBracket := meanBracketOfMoments (547/1000) lo1065 hi1065 accepted1065
def lo1066b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨36,by decide⟩
def lo1066b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨37,by decide⟩
def lo1066 : CheckedMoment :=
  CheckedMoment.ofBessel lo1066b1 lo1066b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1066b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨41,by decide⟩
def hi1066b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨42,by decide⟩
def hi1066 : CheckedMoment :=
  CheckedMoment.ofBessel hi1066b1 hi1066b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1066 : meanBracketCheck (137/250) lo1066 hi1066=true := by decide +kernel
def bracket1066 : MeanBracket := meanBracketOfMoments (137/250) lo1066 hi1066 accepted1066
def lo1067b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨46,by decide⟩
def lo1067b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨47,by decide⟩
def lo1067 : CheckedMoment :=
  CheckedMoment.ofBessel lo1067b1 lo1067b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1067b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨51,by decide⟩
def hi1067b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨52,by decide⟩
def hi1067 : CheckedMoment :=
  CheckedMoment.ofBessel hi1067b1 hi1067b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1067 : meanBracketCheck (549/1000) lo1067 hi1067=true := by decide +kernel
def bracket1067 : MeanBracket := meanBracketOfMoments (549/1000) lo1067 hi1067 accepted1067
def lo1068b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨56,by decide⟩
def lo1068b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨57,by decide⟩
def lo1068 : CheckedMoment :=
  CheckedMoment.ofBessel lo1068b1 lo1068b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1068b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨61,by decide⟩
def hi1068b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨62,by decide⟩
def hi1068 : CheckedMoment :=
  CheckedMoment.ofBessel hi1068b1 hi1068b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1068 : meanBracketCheck (11/20) lo1068 hi1068=true := by decide +kernel
def bracket1068 : MeanBracket := meanBracketOfMoments (11/20) lo1068 hi1068 accepted1068
def lo1069b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨2,by decide⟩
def lo1069b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨3,by decide⟩
def lo1069 : CheckedMoment :=
  CheckedMoment.ofBessel lo1069b1 lo1069b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1069b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨7,by decide⟩
def hi1069b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨8,by decide⟩
def hi1069 : CheckedMoment :=
  CheckedMoment.ofBessel hi1069b1 hi1069b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1069 : meanBracketCheck (551/1000) lo1069 hi1069=true := by decide +kernel
def bracket1069 : MeanBracket := meanBracketOfMoments (551/1000) lo1069 hi1069 accepted1069
def lo1070b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨12,by decide⟩
def lo1070b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨13,by decide⟩
def lo1070 : CheckedMoment :=
  CheckedMoment.ofBessel lo1070b1 lo1070b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1070b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨17,by decide⟩
def hi1070b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨18,by decide⟩
def hi1070 : CheckedMoment :=
  CheckedMoment.ofBessel hi1070b1 hi1070b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1070 : meanBracketCheck (69/125) lo1070 hi1070=true := by decide +kernel
def bracket1070 : MeanBracket := meanBracketOfMoments (69/125) lo1070 hi1070 accepted1070
def lo1071b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨22,by decide⟩
def lo1071b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨23,by decide⟩
def lo1071 : CheckedMoment :=
  CheckedMoment.ofBessel lo1071b1 lo1071b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1071b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨27,by decide⟩
def hi1071b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨28,by decide⟩
def hi1071 : CheckedMoment :=
  CheckedMoment.ofBessel hi1071b1 hi1071b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1071 : meanBracketCheck (553/1000) lo1071 hi1071=true := by decide +kernel
def bracket1071 : MeanBracket := meanBracketOfMoments (553/1000) lo1071 hi1071 accepted1071
#print axioms bracket1056
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0066
