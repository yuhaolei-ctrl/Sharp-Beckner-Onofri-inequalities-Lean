import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0177
import BecknerOnofri.EntropyScalarCertificate.Bessel0178
import BecknerOnofri.EntropyScalarCertificate.Bessel0179
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0071
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1136b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨32,by decide⟩
def lo1136b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨33,by decide⟩
def lo1136 : CheckedMoment :=
  CheckedMoment.ofBessel lo1136b1 lo1136b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1136b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨37,by decide⟩
def hi1136b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨38,by decide⟩
def hi1136 : CheckedMoment :=
  CheckedMoment.ofBessel hi1136b1 hi1136b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1136 : meanBracketCheck (309/500) lo1136 hi1136=true := by decide +kernel
def bracket1136 : MeanBracket := meanBracketOfMoments (309/500) lo1136 hi1136 accepted1136
def lo1137b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨42,by decide⟩
def lo1137b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨43,by decide⟩
def lo1137 : CheckedMoment :=
  CheckedMoment.ofBessel lo1137b1 lo1137b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1137b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨47,by decide⟩
def hi1137b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨48,by decide⟩
def hi1137 : CheckedMoment :=
  CheckedMoment.ofBessel hi1137b1 hi1137b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1137 : meanBracketCheck (619/1000) lo1137 hi1137=true := by decide +kernel
def bracket1137 : MeanBracket := meanBracketOfMoments (619/1000) lo1137 hi1137 accepted1137
def lo1138b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨52,by decide⟩
def lo1138b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨53,by decide⟩
def lo1138 : CheckedMoment :=
  CheckedMoment.ofBessel lo1138b1 lo1138b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1138b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨57,by decide⟩
def hi1138b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨58,by decide⟩
def hi1138 : CheckedMoment :=
  CheckedMoment.ofBessel hi1138b1 hi1138b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1138 : meanBracketCheck (31/50) lo1138 hi1138=true := by decide +kernel
def bracket1138 : MeanBracket := meanBracketOfMoments (31/50) lo1138 hi1138 accepted1138
def lo1139b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨62,by decide⟩
def lo1139b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨63,by decide⟩
def lo1139 : CheckedMoment :=
  CheckedMoment.ofBessel lo1139b1 lo1139b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1139b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨3,by decide⟩
def hi1139b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨4,by decide⟩
def hi1139 : CheckedMoment :=
  CheckedMoment.ofBessel hi1139b1 hi1139b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1139 : meanBracketCheck (621/1000) lo1139 hi1139=true := by decide +kernel
def bracket1139 : MeanBracket := meanBracketOfMoments (621/1000) lo1139 hi1139 accepted1139
def lo1140b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨8,by decide⟩
def lo1140b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨9,by decide⟩
def lo1140 : CheckedMoment :=
  CheckedMoment.ofBessel lo1140b1 lo1140b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1140b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨13,by decide⟩
def hi1140b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨14,by decide⟩
def hi1140 : CheckedMoment :=
  CheckedMoment.ofBessel hi1140b1 hi1140b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1140 : meanBracketCheck (311/500) lo1140 hi1140=true := by decide +kernel
def bracket1140 : MeanBracket := meanBracketOfMoments (311/500) lo1140 hi1140 accepted1140
def lo1141b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨18,by decide⟩
def lo1141b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨19,by decide⟩
def lo1141 : CheckedMoment :=
  CheckedMoment.ofBessel lo1141b1 lo1141b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1141b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨23,by decide⟩
def hi1141b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨24,by decide⟩
def hi1141 : CheckedMoment :=
  CheckedMoment.ofBessel hi1141b1 hi1141b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1141 : meanBracketCheck (623/1000) lo1141 hi1141=true := by decide +kernel
def bracket1141 : MeanBracket := meanBracketOfMoments (623/1000) lo1141 hi1141 accepted1141
def lo1142b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨28,by decide⟩
def lo1142b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨29,by decide⟩
def lo1142 : CheckedMoment :=
  CheckedMoment.ofBessel lo1142b1 lo1142b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1142b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨33,by decide⟩
def hi1142b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨34,by decide⟩
def hi1142 : CheckedMoment :=
  CheckedMoment.ofBessel hi1142b1 hi1142b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1142 : meanBracketCheck (78/125) lo1142 hi1142=true := by decide +kernel
def bracket1142 : MeanBracket := meanBracketOfMoments (78/125) lo1142 hi1142 accepted1142
def lo1143b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨38,by decide⟩
def lo1143b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨39,by decide⟩
def lo1143 : CheckedMoment :=
  CheckedMoment.ofBessel lo1143b1 lo1143b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1143b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨43,by decide⟩
def hi1143b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨44,by decide⟩
def hi1143 : CheckedMoment :=
  CheckedMoment.ofBessel hi1143b1 hi1143b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1143 : meanBracketCheck (5/8) lo1143 hi1143=true := by decide +kernel
def bracket1143 : MeanBracket := meanBracketOfMoments (5/8) lo1143 hi1143 accepted1143
def lo1144b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨48,by decide⟩
def lo1144b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨49,by decide⟩
def lo1144 : CheckedMoment :=
  CheckedMoment.ofBessel lo1144b1 lo1144b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1144b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨53,by decide⟩
def hi1144b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨54,by decide⟩
def hi1144 : CheckedMoment :=
  CheckedMoment.ofBessel hi1144b1 hi1144b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1144 : meanBracketCheck (313/500) lo1144 hi1144=true := by decide +kernel
def bracket1144 : MeanBracket := meanBracketOfMoments (313/500) lo1144 hi1144 accepted1144
def lo1145b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨58,by decide⟩
def lo1145b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨59,by decide⟩
def lo1145 : CheckedMoment :=
  CheckedMoment.ofBessel lo1145b1 lo1145b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1145b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨63,by decide⟩
def hi1145b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨0,by decide⟩
def hi1145 : CheckedMoment :=
  CheckedMoment.ofBessel hi1145b1 hi1145b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1145 : meanBracketCheck (627/1000) lo1145 hi1145=true := by decide +kernel
def bracket1145 : MeanBracket := meanBracketOfMoments (627/1000) lo1145 hi1145 accepted1145
def lo1146b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨4,by decide⟩
def lo1146b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨5,by decide⟩
def lo1146 : CheckedMoment :=
  CheckedMoment.ofBessel lo1146b1 lo1146b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1146b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨9,by decide⟩
def hi1146b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨10,by decide⟩
def hi1146 : CheckedMoment :=
  CheckedMoment.ofBessel hi1146b1 hi1146b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1146 : meanBracketCheck (157/250) lo1146 hi1146=true := by decide +kernel
def bracket1146 : MeanBracket := meanBracketOfMoments (157/250) lo1146 hi1146 accepted1146
def lo1147b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨14,by decide⟩
def lo1147b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨15,by decide⟩
def lo1147 : CheckedMoment :=
  CheckedMoment.ofBessel lo1147b1 lo1147b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1147b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨19,by decide⟩
def hi1147b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨20,by decide⟩
def hi1147 : CheckedMoment :=
  CheckedMoment.ofBessel hi1147b1 hi1147b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1147 : meanBracketCheck (629/1000) lo1147 hi1147=true := by decide +kernel
def bracket1147 : MeanBracket := meanBracketOfMoments (629/1000) lo1147 hi1147 accepted1147
def lo1148b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨24,by decide⟩
def lo1148b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨25,by decide⟩
def lo1148 : CheckedMoment :=
  CheckedMoment.ofBessel lo1148b1 lo1148b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1148b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨29,by decide⟩
def hi1148b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨30,by decide⟩
def hi1148 : CheckedMoment :=
  CheckedMoment.ofBessel hi1148b1 hi1148b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1148 : meanBracketCheck (63/100) lo1148 hi1148=true := by decide +kernel
def bracket1148 : MeanBracket := meanBracketOfMoments (63/100) lo1148 hi1148 accepted1148
def lo1149b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨34,by decide⟩
def lo1149b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨35,by decide⟩
def lo1149 : CheckedMoment :=
  CheckedMoment.ofBessel lo1149b1 lo1149b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1149b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨39,by decide⟩
def hi1149b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨40,by decide⟩
def hi1149 : CheckedMoment :=
  CheckedMoment.ofBessel hi1149b1 hi1149b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1149 : meanBracketCheck (631/1000) lo1149 hi1149=true := by decide +kernel
def bracket1149 : MeanBracket := meanBracketOfMoments (631/1000) lo1149 hi1149 accepted1149
def lo1150b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨44,by decide⟩
def lo1150b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨45,by decide⟩
def lo1150 : CheckedMoment :=
  CheckedMoment.ofBessel lo1150b1 lo1150b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1150b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨49,by decide⟩
def hi1150b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨50,by decide⟩
def hi1150 : CheckedMoment :=
  CheckedMoment.ofBessel hi1150b1 hi1150b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1150 : meanBracketCheck (79/125) lo1150 hi1150=true := by decide +kernel
def bracket1150 : MeanBracket := meanBracketOfMoments (79/125) lo1150 hi1150 accepted1150
def lo1151b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨54,by decide⟩
def lo1151b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨55,by decide⟩
def lo1151 : CheckedMoment :=
  CheckedMoment.ofBessel lo1151b1 lo1151b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1151b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨59,by decide⟩
def hi1151b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨60,by decide⟩
def hi1151 : CheckedMoment :=
  CheckedMoment.ofBessel hi1151b1 hi1151b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1151 : meanBracketCheck (633/1000) lo1151 hi1151=true := by decide +kernel
def bracket1151 : MeanBracket := meanBracketOfMoments (633/1000) lo1151 hi1151 accepted1151
#print axioms bracket1136
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0071
