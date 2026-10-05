import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0185
import BecknerOnofri.EntropyScalarCertificate.Bessel0186
import BecknerOnofri.EntropyScalarCertificate.Bessel0187
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0074
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1184b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨0,by decide⟩
def lo1184b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨1,by decide⟩
def lo1184 : CheckedMoment :=
  CheckedMoment.ofBessel lo1184b1 lo1184b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1184b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨5,by decide⟩
def hi1184b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨6,by decide⟩
def hi1184 : CheckedMoment :=
  CheckedMoment.ofBessel hi1184b1 hi1184b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1184 : meanBracketCheck (333/500) lo1184 hi1184=true := by decide +kernel
def bracket1184 : MeanBracket := meanBracketOfMoments (333/500) lo1184 hi1184 accepted1184
def lo1185b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨10,by decide⟩
def lo1185b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨11,by decide⟩
def lo1185 : CheckedMoment :=
  CheckedMoment.ofBessel lo1185b1 lo1185b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1185b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨15,by decide⟩
def hi1185b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨16,by decide⟩
def hi1185 : CheckedMoment :=
  CheckedMoment.ofBessel hi1185b1 hi1185b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1185 : meanBracketCheck (667/1000) lo1185 hi1185=true := by decide +kernel
def bracket1185 : MeanBracket := meanBracketOfMoments (667/1000) lo1185 hi1185 accepted1185
def lo1186b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨20,by decide⟩
def lo1186b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨21,by decide⟩
def lo1186 : CheckedMoment :=
  CheckedMoment.ofBessel lo1186b1 lo1186b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1186b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨25,by decide⟩
def hi1186b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨26,by decide⟩
def hi1186 : CheckedMoment :=
  CheckedMoment.ofBessel hi1186b1 hi1186b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1186 : meanBracketCheck (167/250) lo1186 hi1186=true := by decide +kernel
def bracket1186 : MeanBracket := meanBracketOfMoments (167/250) lo1186 hi1186 accepted1186
def lo1187b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨30,by decide⟩
def lo1187b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨31,by decide⟩
def lo1187 : CheckedMoment :=
  CheckedMoment.ofBessel lo1187b1 lo1187b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1187b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨35,by decide⟩
def hi1187b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨36,by decide⟩
def hi1187 : CheckedMoment :=
  CheckedMoment.ofBessel hi1187b1 hi1187b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1187 : meanBracketCheck (669/1000) lo1187 hi1187=true := by decide +kernel
def bracket1187 : MeanBracket := meanBracketOfMoments (669/1000) lo1187 hi1187 accepted1187
def lo1188b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨40,by decide⟩
def lo1188b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨41,by decide⟩
def lo1188 : CheckedMoment :=
  CheckedMoment.ofBessel lo1188b1 lo1188b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1188b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨45,by decide⟩
def hi1188b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨46,by decide⟩
def hi1188 : CheckedMoment :=
  CheckedMoment.ofBessel hi1188b1 hi1188b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1188 : meanBracketCheck (67/100) lo1188 hi1188=true := by decide +kernel
def bracket1188 : MeanBracket := meanBracketOfMoments (67/100) lo1188 hi1188 accepted1188
def lo1189b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨50,by decide⟩
def lo1189b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨51,by decide⟩
def lo1189 : CheckedMoment :=
  CheckedMoment.ofBessel lo1189b1 lo1189b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1189b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨55,by decide⟩
def hi1189b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨56,by decide⟩
def hi1189 : CheckedMoment :=
  CheckedMoment.ofBessel hi1189b1 hi1189b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1189 : meanBracketCheck (671/1000) lo1189 hi1189=true := by decide +kernel
def bracket1189 : MeanBracket := meanBracketOfMoments (671/1000) lo1189 hi1189 accepted1189
def lo1190b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨60,by decide⟩
def lo1190b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨61,by decide⟩
def lo1190 : CheckedMoment :=
  CheckedMoment.ofBessel lo1190b1 lo1190b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1190b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨1,by decide⟩
def hi1190b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨2,by decide⟩
def hi1190 : CheckedMoment :=
  CheckedMoment.ofBessel hi1190b1 hi1190b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1190 : meanBracketCheck (84/125) lo1190 hi1190=true := by decide +kernel
def bracket1190 : MeanBracket := meanBracketOfMoments (84/125) lo1190 hi1190 accepted1190
def lo1191b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨6,by decide⟩
def lo1191b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨7,by decide⟩
def lo1191 : CheckedMoment :=
  CheckedMoment.ofBessel lo1191b1 lo1191b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1191b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨11,by decide⟩
def hi1191b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨12,by decide⟩
def hi1191 : CheckedMoment :=
  CheckedMoment.ofBessel hi1191b1 hi1191b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1191 : meanBracketCheck (673/1000) lo1191 hi1191=true := by decide +kernel
def bracket1191 : MeanBracket := meanBracketOfMoments (673/1000) lo1191 hi1191 accepted1191
def lo1192b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨16,by decide⟩
def lo1192b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨17,by decide⟩
def lo1192 : CheckedMoment :=
  CheckedMoment.ofBessel lo1192b1 lo1192b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1192b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨21,by decide⟩
def hi1192b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨22,by decide⟩
def hi1192 : CheckedMoment :=
  CheckedMoment.ofBessel hi1192b1 hi1192b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1192 : meanBracketCheck (337/500) lo1192 hi1192=true := by decide +kernel
def bracket1192 : MeanBracket := meanBracketOfMoments (337/500) lo1192 hi1192 accepted1192
def lo1193b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨26,by decide⟩
def lo1193b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨27,by decide⟩
def lo1193 : CheckedMoment :=
  CheckedMoment.ofBessel lo1193b1 lo1193b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1193b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨31,by decide⟩
def hi1193b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨32,by decide⟩
def hi1193 : CheckedMoment :=
  CheckedMoment.ofBessel hi1193b1 hi1193b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1193 : meanBracketCheck (27/40) lo1193 hi1193=true := by decide +kernel
def bracket1193 : MeanBracket := meanBracketOfMoments (27/40) lo1193 hi1193 accepted1193
def lo1194b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨36,by decide⟩
def lo1194b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨37,by decide⟩
def lo1194 : CheckedMoment :=
  CheckedMoment.ofBessel lo1194b1 lo1194b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1194b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨41,by decide⟩
def hi1194b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨42,by decide⟩
def hi1194 : CheckedMoment :=
  CheckedMoment.ofBessel hi1194b1 hi1194b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1194 : meanBracketCheck (169/250) lo1194 hi1194=true := by decide +kernel
def bracket1194 : MeanBracket := meanBracketOfMoments (169/250) lo1194 hi1194 accepted1194
def lo1195b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨46,by decide⟩
def lo1195b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨47,by decide⟩
def lo1195 : CheckedMoment :=
  CheckedMoment.ofBessel lo1195b1 lo1195b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1195b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨51,by decide⟩
def hi1195b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨52,by decide⟩
def hi1195 : CheckedMoment :=
  CheckedMoment.ofBessel hi1195b1 hi1195b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1195 : meanBracketCheck (677/1000) lo1195 hi1195=true := by decide +kernel
def bracket1195 : MeanBracket := meanBracketOfMoments (677/1000) lo1195 hi1195 accepted1195
def lo1196b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨56,by decide⟩
def lo1196b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨57,by decide⟩
def lo1196 : CheckedMoment :=
  CheckedMoment.ofBessel lo1196b1 lo1196b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1196b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨61,by decide⟩
def hi1196b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨62,by decide⟩
def hi1196 : CheckedMoment :=
  CheckedMoment.ofBessel hi1196b1 hi1196b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1196 : meanBracketCheck (339/500) lo1196 hi1196=true := by decide +kernel
def bracket1196 : MeanBracket := meanBracketOfMoments (339/500) lo1196 hi1196 accepted1196
def lo1197b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨2,by decide⟩
def lo1197b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨3,by decide⟩
def lo1197 : CheckedMoment :=
  CheckedMoment.ofBessel lo1197b1 lo1197b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1197b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨7,by decide⟩
def hi1197b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨8,by decide⟩
def hi1197 : CheckedMoment :=
  CheckedMoment.ofBessel hi1197b1 hi1197b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1197 : meanBracketCheck (679/1000) lo1197 hi1197=true := by decide +kernel
def bracket1197 : MeanBracket := meanBracketOfMoments (679/1000) lo1197 hi1197 accepted1197
def lo1198b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨12,by decide⟩
def lo1198b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨13,by decide⟩
def lo1198 : CheckedMoment :=
  CheckedMoment.ofBessel lo1198b1 lo1198b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1198b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨17,by decide⟩
def hi1198b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨18,by decide⟩
def hi1198 : CheckedMoment :=
  CheckedMoment.ofBessel hi1198b1 hi1198b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1198 : meanBracketCheck (17/25) lo1198 hi1198=true := by decide +kernel
def bracket1198 : MeanBracket := meanBracketOfMoments (17/25) lo1198 hi1198 accepted1198
def lo1199b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨22,by decide⟩
def lo1199b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨23,by decide⟩
def lo1199 : CheckedMoment :=
  CheckedMoment.ofBessel lo1199b1 lo1199b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1199b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨27,by decide⟩
def hi1199b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨28,by decide⟩
def hi1199 : CheckedMoment :=
  CheckedMoment.ofBessel hi1199b1 hi1199b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1199 : meanBracketCheck (681/1000) lo1199 hi1199=true := by decide +kernel
def bracket1199 : MeanBracket := meanBracketOfMoments (681/1000) lo1199 hi1199 accepted1199
#print axioms bracket1184
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0074
