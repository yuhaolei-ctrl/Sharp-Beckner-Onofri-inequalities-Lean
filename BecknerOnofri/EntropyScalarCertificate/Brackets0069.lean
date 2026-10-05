import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0172
import BecknerOnofri.EntropyScalarCertificate.Bessel0173
import BecknerOnofri.EntropyScalarCertificate.Bessel0174
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0069
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1104b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨32,by decide⟩
def lo1104b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨33,by decide⟩
def lo1104 : CheckedMoment :=
  CheckedMoment.ofBessel lo1104b1 lo1104b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1104b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨37,by decide⟩
def hi1104b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨38,by decide⟩
def hi1104 : CheckedMoment :=
  CheckedMoment.ofBessel hi1104b1 hi1104b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1104 : meanBracketCheck (293/500) lo1104 hi1104=true := by decide +kernel
def bracket1104 : MeanBracket := meanBracketOfMoments (293/500) lo1104 hi1104 accepted1104
def lo1105b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨42,by decide⟩
def lo1105b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨43,by decide⟩
def lo1105 : CheckedMoment :=
  CheckedMoment.ofBessel lo1105b1 lo1105b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1105b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨47,by decide⟩
def hi1105b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨48,by decide⟩
def hi1105 : CheckedMoment :=
  CheckedMoment.ofBessel hi1105b1 hi1105b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1105 : meanBracketCheck (587/1000) lo1105 hi1105=true := by decide +kernel
def bracket1105 : MeanBracket := meanBracketOfMoments (587/1000) lo1105 hi1105 accepted1105
def lo1106b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨52,by decide⟩
def lo1106b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨53,by decide⟩
def lo1106 : CheckedMoment :=
  CheckedMoment.ofBessel lo1106b1 lo1106b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1106b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨57,by decide⟩
def hi1106b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨58,by decide⟩
def hi1106 : CheckedMoment :=
  CheckedMoment.ofBessel hi1106b1 hi1106b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1106 : meanBracketCheck (147/250) lo1106 hi1106=true := by decide +kernel
def bracket1106 : MeanBracket := meanBracketOfMoments (147/250) lo1106 hi1106 accepted1106
def lo1107b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨62,by decide⟩
def lo1107b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨63,by decide⟩
def lo1107 : CheckedMoment :=
  CheckedMoment.ofBessel lo1107b1 lo1107b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1107b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨3,by decide⟩
def hi1107b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨4,by decide⟩
def hi1107 : CheckedMoment :=
  CheckedMoment.ofBessel hi1107b1 hi1107b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1107 : meanBracketCheck (589/1000) lo1107 hi1107=true := by decide +kernel
def bracket1107 : MeanBracket := meanBracketOfMoments (589/1000) lo1107 hi1107 accepted1107
def lo1108b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨8,by decide⟩
def lo1108b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨9,by decide⟩
def lo1108 : CheckedMoment :=
  CheckedMoment.ofBessel lo1108b1 lo1108b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1108b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨13,by decide⟩
def hi1108b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨14,by decide⟩
def hi1108 : CheckedMoment :=
  CheckedMoment.ofBessel hi1108b1 hi1108b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1108 : meanBracketCheck (59/100) lo1108 hi1108=true := by decide +kernel
def bracket1108 : MeanBracket := meanBracketOfMoments (59/100) lo1108 hi1108 accepted1108
def lo1109b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨18,by decide⟩
def lo1109b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨19,by decide⟩
def lo1109 : CheckedMoment :=
  CheckedMoment.ofBessel lo1109b1 lo1109b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1109b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨23,by decide⟩
def hi1109b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨24,by decide⟩
def hi1109 : CheckedMoment :=
  CheckedMoment.ofBessel hi1109b1 hi1109b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1109 : meanBracketCheck (591/1000) lo1109 hi1109=true := by decide +kernel
def bracket1109 : MeanBracket := meanBracketOfMoments (591/1000) lo1109 hi1109 accepted1109
def lo1110b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨28,by decide⟩
def lo1110b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨29,by decide⟩
def lo1110 : CheckedMoment :=
  CheckedMoment.ofBessel lo1110b1 lo1110b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1110b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨33,by decide⟩
def hi1110b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨34,by decide⟩
def hi1110 : CheckedMoment :=
  CheckedMoment.ofBessel hi1110b1 hi1110b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1110 : meanBracketCheck (74/125) lo1110 hi1110=true := by decide +kernel
def bracket1110 : MeanBracket := meanBracketOfMoments (74/125) lo1110 hi1110 accepted1110
def lo1111b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨38,by decide⟩
def lo1111b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨39,by decide⟩
def lo1111 : CheckedMoment :=
  CheckedMoment.ofBessel lo1111b1 lo1111b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1111b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨43,by decide⟩
def hi1111b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨44,by decide⟩
def hi1111 : CheckedMoment :=
  CheckedMoment.ofBessel hi1111b1 hi1111b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1111 : meanBracketCheck (593/1000) lo1111 hi1111=true := by decide +kernel
def bracket1111 : MeanBracket := meanBracketOfMoments (593/1000) lo1111 hi1111 accepted1111
def lo1112b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨48,by decide⟩
def lo1112b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨49,by decide⟩
def lo1112 : CheckedMoment :=
  CheckedMoment.ofBessel lo1112b1 lo1112b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1112b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨53,by decide⟩
def hi1112b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨54,by decide⟩
def hi1112 : CheckedMoment :=
  CheckedMoment.ofBessel hi1112b1 hi1112b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1112 : meanBracketCheck (297/500) lo1112 hi1112=true := by decide +kernel
def bracket1112 : MeanBracket := meanBracketOfMoments (297/500) lo1112 hi1112 accepted1112
def lo1113b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨58,by decide⟩
def lo1113b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨59,by decide⟩
def lo1113 : CheckedMoment :=
  CheckedMoment.ofBessel lo1113b1 lo1113b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1113b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨63,by decide⟩
def hi1113b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨0,by decide⟩
def hi1113 : CheckedMoment :=
  CheckedMoment.ofBessel hi1113b1 hi1113b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1113 : meanBracketCheck (119/200) lo1113 hi1113=true := by decide +kernel
def bracket1113 : MeanBracket := meanBracketOfMoments (119/200) lo1113 hi1113 accepted1113
def lo1114b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨4,by decide⟩
def lo1114b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨5,by decide⟩
def lo1114 : CheckedMoment :=
  CheckedMoment.ofBessel lo1114b1 lo1114b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1114b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨9,by decide⟩
def hi1114b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨10,by decide⟩
def hi1114 : CheckedMoment :=
  CheckedMoment.ofBessel hi1114b1 hi1114b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1114 : meanBracketCheck (149/250) lo1114 hi1114=true := by decide +kernel
def bracket1114 : MeanBracket := meanBracketOfMoments (149/250) lo1114 hi1114 accepted1114
def lo1115b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨14,by decide⟩
def lo1115b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨15,by decide⟩
def lo1115 : CheckedMoment :=
  CheckedMoment.ofBessel lo1115b1 lo1115b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1115b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨19,by decide⟩
def hi1115b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨20,by decide⟩
def hi1115 : CheckedMoment :=
  CheckedMoment.ofBessel hi1115b1 hi1115b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1115 : meanBracketCheck (597/1000) lo1115 hi1115=true := by decide +kernel
def bracket1115 : MeanBracket := meanBracketOfMoments (597/1000) lo1115 hi1115 accepted1115
def lo1116b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨24,by decide⟩
def lo1116b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨25,by decide⟩
def lo1116 : CheckedMoment :=
  CheckedMoment.ofBessel lo1116b1 lo1116b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1116b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨29,by decide⟩
def hi1116b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨30,by decide⟩
def hi1116 : CheckedMoment :=
  CheckedMoment.ofBessel hi1116b1 hi1116b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1116 : meanBracketCheck (299/500) lo1116 hi1116=true := by decide +kernel
def bracket1116 : MeanBracket := meanBracketOfMoments (299/500) lo1116 hi1116 accepted1116
def lo1117b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨34,by decide⟩
def lo1117b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨35,by decide⟩
def lo1117 : CheckedMoment :=
  CheckedMoment.ofBessel lo1117b1 lo1117b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1117b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨39,by decide⟩
def hi1117b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨40,by decide⟩
def hi1117 : CheckedMoment :=
  CheckedMoment.ofBessel hi1117b1 hi1117b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1117 : meanBracketCheck (599/1000) lo1117 hi1117=true := by decide +kernel
def bracket1117 : MeanBracket := meanBracketOfMoments (599/1000) lo1117 hi1117 accepted1117
def lo1118b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨44,by decide⟩
def lo1118b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨45,by decide⟩
def lo1118 : CheckedMoment :=
  CheckedMoment.ofBessel lo1118b1 lo1118b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1118b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨49,by decide⟩
def hi1118b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨50,by decide⟩
def hi1118 : CheckedMoment :=
  CheckedMoment.ofBessel hi1118b1 hi1118b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1118 : meanBracketCheck (3/5) lo1118 hi1118=true := by decide +kernel
def bracket1118 : MeanBracket := meanBracketOfMoments (3/5) lo1118 hi1118 accepted1118
def lo1119b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨54,by decide⟩
def lo1119b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨55,by decide⟩
def lo1119 : CheckedMoment :=
  CheckedMoment.ofBessel lo1119b1 lo1119b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1119b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨59,by decide⟩
def hi1119b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0174.rows BesselBatch0174.accepted ⟨60,by decide⟩
def hi1119 : CheckedMoment :=
  CheckedMoment.ofBessel hi1119b1 hi1119b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1119 : meanBracketCheck (601/1000) lo1119 hi1119=true := by decide +kernel
def bracket1119 : MeanBracket := meanBracketOfMoments (601/1000) lo1119 hi1119 accepted1119
#print axioms bracket1104
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0069
