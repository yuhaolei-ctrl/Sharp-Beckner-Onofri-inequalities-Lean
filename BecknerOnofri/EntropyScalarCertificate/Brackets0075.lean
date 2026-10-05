module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0187
public import BecknerOnofri.EntropyScalarCertificate.Bessel0188
public import BecknerOnofri.EntropyScalarCertificate.Bessel0189

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0075
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1200b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨32,by decide⟩
def lo1200b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨33,by decide⟩
def lo1200 : CheckedMoment :=
  CheckedMoment.ofBessel lo1200b1 lo1200b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1200b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨37,by decide⟩
def hi1200b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨38,by decide⟩
def hi1200 : CheckedMoment :=
  CheckedMoment.ofBessel hi1200b1 hi1200b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1200 : meanBracketCheck (341/500) lo1200 hi1200=true := by decide +kernel
def bracket1200 : MeanBracket := meanBracketOfMoments (341/500) lo1200 hi1200 accepted1200
def lo1201b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨42,by decide⟩
def lo1201b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨43,by decide⟩
def lo1201 : CheckedMoment :=
  CheckedMoment.ofBessel lo1201b1 lo1201b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1201b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨47,by decide⟩
def hi1201b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨48,by decide⟩
def hi1201 : CheckedMoment :=
  CheckedMoment.ofBessel hi1201b1 hi1201b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1201 : meanBracketCheck (683/1000) lo1201 hi1201=true := by decide +kernel
def bracket1201 : MeanBracket := meanBracketOfMoments (683/1000) lo1201 hi1201 accepted1201
def lo1202b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨52,by decide⟩
def lo1202b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨53,by decide⟩
def lo1202 : CheckedMoment :=
  CheckedMoment.ofBessel lo1202b1 lo1202b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1202b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨57,by decide⟩
def hi1202b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨58,by decide⟩
def hi1202 : CheckedMoment :=
  CheckedMoment.ofBessel hi1202b1 hi1202b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1202 : meanBracketCheck (171/250) lo1202 hi1202=true := by decide +kernel
def bracket1202 : MeanBracket := meanBracketOfMoments (171/250) lo1202 hi1202 accepted1202
def lo1203b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨62,by decide⟩
def lo1203b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨63,by decide⟩
def lo1203 : CheckedMoment :=
  CheckedMoment.ofBessel lo1203b1 lo1203b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1203b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨3,by decide⟩
def hi1203b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨4,by decide⟩
def hi1203 : CheckedMoment :=
  CheckedMoment.ofBessel hi1203b1 hi1203b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1203 : meanBracketCheck (137/200) lo1203 hi1203=true := by decide +kernel
def bracket1203 : MeanBracket := meanBracketOfMoments (137/200) lo1203 hi1203 accepted1203
def lo1204b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨8,by decide⟩
def lo1204b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨9,by decide⟩
def lo1204 : CheckedMoment :=
  CheckedMoment.ofBessel lo1204b1 lo1204b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1204b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨13,by decide⟩
def hi1204b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨14,by decide⟩
def hi1204 : CheckedMoment :=
  CheckedMoment.ofBessel hi1204b1 hi1204b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1204 : meanBracketCheck (343/500) lo1204 hi1204=true := by decide +kernel
def bracket1204 : MeanBracket := meanBracketOfMoments (343/500) lo1204 hi1204 accepted1204
def lo1205b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨18,by decide⟩
def lo1205b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨19,by decide⟩
def lo1205 : CheckedMoment :=
  CheckedMoment.ofBessel lo1205b1 lo1205b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1205b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨23,by decide⟩
def hi1205b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨24,by decide⟩
def hi1205 : CheckedMoment :=
  CheckedMoment.ofBessel hi1205b1 hi1205b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1205 : meanBracketCheck (687/1000) lo1205 hi1205=true := by decide +kernel
def bracket1205 : MeanBracket := meanBracketOfMoments (687/1000) lo1205 hi1205 accepted1205
def lo1206b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨28,by decide⟩
def lo1206b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨29,by decide⟩
def lo1206 : CheckedMoment :=
  CheckedMoment.ofBessel lo1206b1 lo1206b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1206b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨33,by decide⟩
def hi1206b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨34,by decide⟩
def hi1206 : CheckedMoment :=
  CheckedMoment.ofBessel hi1206b1 hi1206b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1206 : meanBracketCheck (86/125) lo1206 hi1206=true := by decide +kernel
def bracket1206 : MeanBracket := meanBracketOfMoments (86/125) lo1206 hi1206 accepted1206
def lo1207b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨38,by decide⟩
def lo1207b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨39,by decide⟩
def lo1207 : CheckedMoment :=
  CheckedMoment.ofBessel lo1207b1 lo1207b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1207b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨43,by decide⟩
def hi1207b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨44,by decide⟩
def hi1207 : CheckedMoment :=
  CheckedMoment.ofBessel hi1207b1 hi1207b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1207 : meanBracketCheck (689/1000) lo1207 hi1207=true := by decide +kernel
def bracket1207 : MeanBracket := meanBracketOfMoments (689/1000) lo1207 hi1207 accepted1207
def lo1208b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨48,by decide⟩
def lo1208b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨49,by decide⟩
def lo1208 : CheckedMoment :=
  CheckedMoment.ofBessel lo1208b1 lo1208b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1208b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨53,by decide⟩
def hi1208b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨54,by decide⟩
def hi1208 : CheckedMoment :=
  CheckedMoment.ofBessel hi1208b1 hi1208b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1208 : meanBracketCheck (69/100) lo1208 hi1208=true := by decide +kernel
def bracket1208 : MeanBracket := meanBracketOfMoments (69/100) lo1208 hi1208 accepted1208
def lo1209b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨58,by decide⟩
def lo1209b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨59,by decide⟩
def lo1209 : CheckedMoment :=
  CheckedMoment.ofBessel lo1209b1 lo1209b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1209b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨63,by decide⟩
def hi1209b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨0,by decide⟩
def hi1209 : CheckedMoment :=
  CheckedMoment.ofBessel hi1209b1 hi1209b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1209 : meanBracketCheck (691/1000) lo1209 hi1209=true := by decide +kernel
def bracket1209 : MeanBracket := meanBracketOfMoments (691/1000) lo1209 hi1209 accepted1209
def lo1210b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨4,by decide⟩
def lo1210b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨5,by decide⟩
def lo1210 : CheckedMoment :=
  CheckedMoment.ofBessel lo1210b1 lo1210b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1210b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨9,by decide⟩
def hi1210b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨10,by decide⟩
def hi1210 : CheckedMoment :=
  CheckedMoment.ofBessel hi1210b1 hi1210b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1210 : meanBracketCheck (173/250) lo1210 hi1210=true := by decide +kernel
def bracket1210 : MeanBracket := meanBracketOfMoments (173/250) lo1210 hi1210 accepted1210
def lo1211b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨14,by decide⟩
def lo1211b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨15,by decide⟩
def lo1211 : CheckedMoment :=
  CheckedMoment.ofBessel lo1211b1 lo1211b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1211b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨19,by decide⟩
def hi1211b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨20,by decide⟩
def hi1211 : CheckedMoment :=
  CheckedMoment.ofBessel hi1211b1 hi1211b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1211 : meanBracketCheck (693/1000) lo1211 hi1211=true := by decide +kernel
def bracket1211 : MeanBracket := meanBracketOfMoments (693/1000) lo1211 hi1211 accepted1211
def lo1212b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨24,by decide⟩
def lo1212b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨25,by decide⟩
def lo1212 : CheckedMoment :=
  CheckedMoment.ofBessel lo1212b1 lo1212b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1212b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨29,by decide⟩
def hi1212b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨30,by decide⟩
def hi1212 : CheckedMoment :=
  CheckedMoment.ofBessel hi1212b1 hi1212b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1212 : meanBracketCheck (347/500) lo1212 hi1212=true := by decide +kernel
def bracket1212 : MeanBracket := meanBracketOfMoments (347/500) lo1212 hi1212 accepted1212
def lo1213b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨34,by decide⟩
def lo1213b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨35,by decide⟩
def lo1213 : CheckedMoment :=
  CheckedMoment.ofBessel lo1213b1 lo1213b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1213b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨39,by decide⟩
def hi1213b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨40,by decide⟩
def hi1213 : CheckedMoment :=
  CheckedMoment.ofBessel hi1213b1 hi1213b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1213 : meanBracketCheck (139/200) lo1213 hi1213=true := by decide +kernel
def bracket1213 : MeanBracket := meanBracketOfMoments (139/200) lo1213 hi1213 accepted1213
def lo1214b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨44,by decide⟩
def lo1214b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨45,by decide⟩
def lo1214 : CheckedMoment :=
  CheckedMoment.ofBessel lo1214b1 lo1214b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1214b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨49,by decide⟩
def hi1214b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨50,by decide⟩
def hi1214 : CheckedMoment :=
  CheckedMoment.ofBessel hi1214b1 hi1214b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1214 : meanBracketCheck (87/125) lo1214 hi1214=true := by decide +kernel
def bracket1214 : MeanBracket := meanBracketOfMoments (87/125) lo1214 hi1214 accepted1214
def lo1215b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨54,by decide⟩
def lo1215b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨55,by decide⟩
def lo1215 : CheckedMoment :=
  CheckedMoment.ofBessel lo1215b1 lo1215b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1215b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨59,by decide⟩
def hi1215b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0189.rows BesselBatch0189.accepted ⟨60,by decide⟩
def hi1215 : CheckedMoment :=
  CheckedMoment.ofBessel hi1215b1 hi1215b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1215 : meanBracketCheck (697/1000) lo1215 hi1215=true := by decide +kernel
def bracket1215 : MeanBracket := meanBracketOfMoments (697/1000) lo1215 hi1215 accepted1215
#print axioms bracket1200
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0075
