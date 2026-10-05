module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0170
public import BecknerOnofri.EntropyScalarCertificate.Bessel0171
public import BecknerOnofri.EntropyScalarCertificate.Bessel0172

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0068
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1088b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨0,by decide⟩
def lo1088b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨1,by decide⟩
def lo1088 : CheckedMoment :=
  CheckedMoment.ofBessel lo1088b1 lo1088b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1088b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨5,by decide⟩
def hi1088b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨6,by decide⟩
def hi1088 : CheckedMoment :=
  CheckedMoment.ofBessel hi1088b1 hi1088b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1088 : meanBracketCheck (57/100) lo1088 hi1088=true := by decide +kernel
def bracket1088 : MeanBracket := meanBracketOfMoments (57/100) lo1088 hi1088 accepted1088
def lo1089b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨10,by decide⟩
def lo1089b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨11,by decide⟩
def lo1089 : CheckedMoment :=
  CheckedMoment.ofBessel lo1089b1 lo1089b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1089b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨15,by decide⟩
def hi1089b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨16,by decide⟩
def hi1089 : CheckedMoment :=
  CheckedMoment.ofBessel hi1089b1 hi1089b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1089 : meanBracketCheck (571/1000) lo1089 hi1089=true := by decide +kernel
def bracket1089 : MeanBracket := meanBracketOfMoments (571/1000) lo1089 hi1089 accepted1089
def lo1090b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨20,by decide⟩
def lo1090b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨21,by decide⟩
def lo1090 : CheckedMoment :=
  CheckedMoment.ofBessel lo1090b1 lo1090b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1090b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨25,by decide⟩
def hi1090b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨26,by decide⟩
def hi1090 : CheckedMoment :=
  CheckedMoment.ofBessel hi1090b1 hi1090b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1090 : meanBracketCheck (143/250) lo1090 hi1090=true := by decide +kernel
def bracket1090 : MeanBracket := meanBracketOfMoments (143/250) lo1090 hi1090 accepted1090
def lo1091b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨30,by decide⟩
def lo1091b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨31,by decide⟩
def lo1091 : CheckedMoment :=
  CheckedMoment.ofBessel lo1091b1 lo1091b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1091b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨35,by decide⟩
def hi1091b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨36,by decide⟩
def hi1091 : CheckedMoment :=
  CheckedMoment.ofBessel hi1091b1 hi1091b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1091 : meanBracketCheck (573/1000) lo1091 hi1091=true := by decide +kernel
def bracket1091 : MeanBracket := meanBracketOfMoments (573/1000) lo1091 hi1091 accepted1091
def lo1092b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨40,by decide⟩
def lo1092b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨41,by decide⟩
def lo1092 : CheckedMoment :=
  CheckedMoment.ofBessel lo1092b1 lo1092b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1092b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨45,by decide⟩
def hi1092b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨46,by decide⟩
def hi1092 : CheckedMoment :=
  CheckedMoment.ofBessel hi1092b1 hi1092b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1092 : meanBracketCheck (287/500) lo1092 hi1092=true := by decide +kernel
def bracket1092 : MeanBracket := meanBracketOfMoments (287/500) lo1092 hi1092 accepted1092
def lo1093b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨50,by decide⟩
def lo1093b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨51,by decide⟩
def lo1093 : CheckedMoment :=
  CheckedMoment.ofBessel lo1093b1 lo1093b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1093b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨55,by decide⟩
def hi1093b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨56,by decide⟩
def hi1093 : CheckedMoment :=
  CheckedMoment.ofBessel hi1093b1 hi1093b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1093 : meanBracketCheck (23/40) lo1093 hi1093=true := by decide +kernel
def bracket1093 : MeanBracket := meanBracketOfMoments (23/40) lo1093 hi1093 accepted1093
def lo1094b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨60,by decide⟩
def lo1094b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨61,by decide⟩
def lo1094 : CheckedMoment :=
  CheckedMoment.ofBessel lo1094b1 lo1094b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1094b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨1,by decide⟩
def hi1094b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨2,by decide⟩
def hi1094 : CheckedMoment :=
  CheckedMoment.ofBessel hi1094b1 hi1094b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1094 : meanBracketCheck (72/125) lo1094 hi1094=true := by decide +kernel
def bracket1094 : MeanBracket := meanBracketOfMoments (72/125) lo1094 hi1094 accepted1094
def lo1095b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨6,by decide⟩
def lo1095b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨7,by decide⟩
def lo1095 : CheckedMoment :=
  CheckedMoment.ofBessel lo1095b1 lo1095b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1095b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨11,by decide⟩
def hi1095b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨12,by decide⟩
def hi1095 : CheckedMoment :=
  CheckedMoment.ofBessel hi1095b1 hi1095b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1095 : meanBracketCheck (577/1000) lo1095 hi1095=true := by decide +kernel
def bracket1095 : MeanBracket := meanBracketOfMoments (577/1000) lo1095 hi1095 accepted1095
def lo1096b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨16,by decide⟩
def lo1096b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨17,by decide⟩
def lo1096 : CheckedMoment :=
  CheckedMoment.ofBessel lo1096b1 lo1096b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1096b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨21,by decide⟩
def hi1096b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨22,by decide⟩
def hi1096 : CheckedMoment :=
  CheckedMoment.ofBessel hi1096b1 hi1096b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1096 : meanBracketCheck (289/500) lo1096 hi1096=true := by decide +kernel
def bracket1096 : MeanBracket := meanBracketOfMoments (289/500) lo1096 hi1096 accepted1096
def lo1097b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨26,by decide⟩
def lo1097b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨27,by decide⟩
def lo1097 : CheckedMoment :=
  CheckedMoment.ofBessel lo1097b1 lo1097b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1097b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨31,by decide⟩
def hi1097b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨32,by decide⟩
def hi1097 : CheckedMoment :=
  CheckedMoment.ofBessel hi1097b1 hi1097b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1097 : meanBracketCheck (579/1000) lo1097 hi1097=true := by decide +kernel
def bracket1097 : MeanBracket := meanBracketOfMoments (579/1000) lo1097 hi1097 accepted1097
def lo1098b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨36,by decide⟩
def lo1098b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨37,by decide⟩
def lo1098 : CheckedMoment :=
  CheckedMoment.ofBessel lo1098b1 lo1098b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1098b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨41,by decide⟩
def hi1098b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨42,by decide⟩
def hi1098 : CheckedMoment :=
  CheckedMoment.ofBessel hi1098b1 hi1098b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1098 : meanBracketCheck (29/50) lo1098 hi1098=true := by decide +kernel
def bracket1098 : MeanBracket := meanBracketOfMoments (29/50) lo1098 hi1098 accepted1098
def lo1099b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨46,by decide⟩
def lo1099b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨47,by decide⟩
def lo1099 : CheckedMoment :=
  CheckedMoment.ofBessel lo1099b1 lo1099b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1099b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨51,by decide⟩
def hi1099b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨52,by decide⟩
def hi1099 : CheckedMoment :=
  CheckedMoment.ofBessel hi1099b1 hi1099b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1099 : meanBracketCheck (581/1000) lo1099 hi1099=true := by decide +kernel
def bracket1099 : MeanBracket := meanBracketOfMoments (581/1000) lo1099 hi1099 accepted1099
def lo1100b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨56,by decide⟩
def lo1100b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨57,by decide⟩
def lo1100 : CheckedMoment :=
  CheckedMoment.ofBessel lo1100b1 lo1100b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1100b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨61,by decide⟩
def hi1100b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨62,by decide⟩
def hi1100 : CheckedMoment :=
  CheckedMoment.ofBessel hi1100b1 hi1100b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1100 : meanBracketCheck (291/500) lo1100 hi1100=true := by decide +kernel
def bracket1100 : MeanBracket := meanBracketOfMoments (291/500) lo1100 hi1100 accepted1100
def lo1101b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨2,by decide⟩
def lo1101b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨3,by decide⟩
def lo1101 : CheckedMoment :=
  CheckedMoment.ofBessel lo1101b1 lo1101b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1101b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨7,by decide⟩
def hi1101b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨8,by decide⟩
def hi1101 : CheckedMoment :=
  CheckedMoment.ofBessel hi1101b1 hi1101b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1101 : meanBracketCheck (583/1000) lo1101 hi1101=true := by decide +kernel
def bracket1101 : MeanBracket := meanBracketOfMoments (583/1000) lo1101 hi1101 accepted1101
def lo1102b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨12,by decide⟩
def lo1102b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨13,by decide⟩
def lo1102 : CheckedMoment :=
  CheckedMoment.ofBessel lo1102b1 lo1102b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1102b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨17,by decide⟩
def hi1102b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨18,by decide⟩
def hi1102 : CheckedMoment :=
  CheckedMoment.ofBessel hi1102b1 hi1102b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1102 : meanBracketCheck (73/125) lo1102 hi1102=true := by decide +kernel
def bracket1102 : MeanBracket := meanBracketOfMoments (73/125) lo1102 hi1102 accepted1102
def lo1103b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨22,by decide⟩
def lo1103b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨23,by decide⟩
def lo1103 : CheckedMoment :=
  CheckedMoment.ofBessel lo1103b1 lo1103b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1103b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨27,by decide⟩
def hi1103b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨28,by decide⟩
def hi1103 : CheckedMoment :=
  CheckedMoment.ofBessel hi1103b1 hi1103b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1103 : meanBracketCheck (117/200) lo1103 hi1103=true := by decide +kernel
def bracket1103 : MeanBracket := meanBracketOfMoments (117/200) lo1103 hi1103 accepted1103
#print axioms bracket1088
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0068
