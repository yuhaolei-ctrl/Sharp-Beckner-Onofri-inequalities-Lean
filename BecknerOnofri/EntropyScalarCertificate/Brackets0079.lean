module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0197
public import BecknerOnofri.EntropyScalarCertificate.Bessel0198
public import BecknerOnofri.EntropyScalarCertificate.Bessel0199

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0079
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1264b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨32,by decide⟩
def lo1264b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨33,by decide⟩
def lo1264 : CheckedMoment :=
  CheckedMoment.ofBessel lo1264b1 lo1264b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1264b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨37,by decide⟩
def hi1264b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨38,by decide⟩
def hi1264 : CheckedMoment :=
  CheckedMoment.ofBessel hi1264b1 hi1264b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1264 : meanBracketCheck (373/500) lo1264 hi1264=true := by decide +kernel
def bracket1264 : MeanBracket := meanBracketOfMoments (373/500) lo1264 hi1264 accepted1264
def lo1265b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨42,by decide⟩
def lo1265b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨43,by decide⟩
def lo1265 : CheckedMoment :=
  CheckedMoment.ofBessel lo1265b1 lo1265b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1265b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨47,by decide⟩
def hi1265b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨48,by decide⟩
def hi1265 : CheckedMoment :=
  CheckedMoment.ofBessel hi1265b1 hi1265b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1265 : meanBracketCheck (747/1000) lo1265 hi1265=true := by decide +kernel
def bracket1265 : MeanBracket := meanBracketOfMoments (747/1000) lo1265 hi1265 accepted1265
def lo1266b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨52,by decide⟩
def lo1266b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨53,by decide⟩
def lo1266 : CheckedMoment :=
  CheckedMoment.ofBessel lo1266b1 lo1266b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1266b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨57,by decide⟩
def hi1266b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨58,by decide⟩
def hi1266 : CheckedMoment :=
  CheckedMoment.ofBessel hi1266b1 hi1266b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1266 : meanBracketCheck (187/250) lo1266 hi1266=true := by decide +kernel
def bracket1266 : MeanBracket := meanBracketOfMoments (187/250) lo1266 hi1266 accepted1266
def lo1267b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨62,by decide⟩
def lo1267b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨63,by decide⟩
def lo1267 : CheckedMoment :=
  CheckedMoment.ofBessel lo1267b1 lo1267b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1267b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨3,by decide⟩
def hi1267b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨4,by decide⟩
def hi1267 : CheckedMoment :=
  CheckedMoment.ofBessel hi1267b1 hi1267b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1267 : meanBracketCheck (749/1000) lo1267 hi1267=true := by decide +kernel
def bracket1267 : MeanBracket := meanBracketOfMoments (749/1000) lo1267 hi1267 accepted1267
def lo1268b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨8,by decide⟩
def lo1268b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨9,by decide⟩
def lo1268 : CheckedMoment :=
  CheckedMoment.ofBessel lo1268b1 lo1268b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1268b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨13,by decide⟩
def hi1268b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨14,by decide⟩
def hi1268 : CheckedMoment :=
  CheckedMoment.ofBessel hi1268b1 hi1268b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1268 : meanBracketCheck (3/4) lo1268 hi1268=true := by decide +kernel
def bracket1268 : MeanBracket := meanBracketOfMoments (3/4) lo1268 hi1268 accepted1268
def lo1269b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨18,by decide⟩
def lo1269b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨19,by decide⟩
def lo1269 : CheckedMoment :=
  CheckedMoment.ofBessel lo1269b1 lo1269b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1269b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨23,by decide⟩
def hi1269b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨24,by decide⟩
def hi1269 : CheckedMoment :=
  CheckedMoment.ofBessel hi1269b1 hi1269b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1269 : meanBracketCheck (751/1000) lo1269 hi1269=true := by decide +kernel
def bracket1269 : MeanBracket := meanBracketOfMoments (751/1000) lo1269 hi1269 accepted1269
def lo1270b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨28,by decide⟩
def lo1270b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨29,by decide⟩
def lo1270 : CheckedMoment :=
  CheckedMoment.ofBessel lo1270b1 lo1270b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1270b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨33,by decide⟩
def hi1270b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨34,by decide⟩
def hi1270 : CheckedMoment :=
  CheckedMoment.ofBessel hi1270b1 hi1270b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1270 : meanBracketCheck (94/125) lo1270 hi1270=true := by decide +kernel
def bracket1270 : MeanBracket := meanBracketOfMoments (94/125) lo1270 hi1270 accepted1270
def lo1271b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨38,by decide⟩
def lo1271b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨39,by decide⟩
def lo1271 : CheckedMoment :=
  CheckedMoment.ofBessel lo1271b1 lo1271b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1271b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨43,by decide⟩
def hi1271b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨44,by decide⟩
def hi1271 : CheckedMoment :=
  CheckedMoment.ofBessel hi1271b1 hi1271b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1271 : meanBracketCheck (753/1000) lo1271 hi1271=true := by decide +kernel
def bracket1271 : MeanBracket := meanBracketOfMoments (753/1000) lo1271 hi1271 accepted1271
def lo1272b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨48,by decide⟩
def lo1272b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨49,by decide⟩
def lo1272 : CheckedMoment :=
  CheckedMoment.ofBessel lo1272b1 lo1272b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1272b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨53,by decide⟩
def hi1272b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨54,by decide⟩
def hi1272 : CheckedMoment :=
  CheckedMoment.ofBessel hi1272b1 hi1272b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1272 : meanBracketCheck (377/500) lo1272 hi1272=true := by decide +kernel
def bracket1272 : MeanBracket := meanBracketOfMoments (377/500) lo1272 hi1272 accepted1272
def lo1273b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨58,by decide⟩
def lo1273b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨59,by decide⟩
def lo1273 : CheckedMoment :=
  CheckedMoment.ofBessel lo1273b1 lo1273b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1273b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0198.rows BesselBatch0198.accepted ⟨63,by decide⟩
def hi1273b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨0,by decide⟩
def hi1273 : CheckedMoment :=
  CheckedMoment.ofBessel hi1273b1 hi1273b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1273 : meanBracketCheck (151/200) lo1273 hi1273=true := by decide +kernel
def bracket1273 : MeanBracket := meanBracketOfMoments (151/200) lo1273 hi1273 accepted1273
def lo1274b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨4,by decide⟩
def lo1274b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨5,by decide⟩
def lo1274 : CheckedMoment :=
  CheckedMoment.ofBessel lo1274b1 lo1274b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1274b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨9,by decide⟩
def hi1274b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨10,by decide⟩
def hi1274 : CheckedMoment :=
  CheckedMoment.ofBessel hi1274b1 hi1274b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1274 : meanBracketCheck (189/250) lo1274 hi1274=true := by decide +kernel
def bracket1274 : MeanBracket := meanBracketOfMoments (189/250) lo1274 hi1274 accepted1274
def lo1275b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨14,by decide⟩
def lo1275b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨15,by decide⟩
def lo1275 : CheckedMoment :=
  CheckedMoment.ofBessel lo1275b1 lo1275b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1275b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨19,by decide⟩
def hi1275b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨20,by decide⟩
def hi1275 : CheckedMoment :=
  CheckedMoment.ofBessel hi1275b1 hi1275b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1275 : meanBracketCheck (757/1000) lo1275 hi1275=true := by decide +kernel
def bracket1275 : MeanBracket := meanBracketOfMoments (757/1000) lo1275 hi1275 accepted1275
def lo1276b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨24,by decide⟩
def lo1276b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨25,by decide⟩
def lo1276 : CheckedMoment :=
  CheckedMoment.ofBessel lo1276b1 lo1276b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1276b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨29,by decide⟩
def hi1276b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨30,by decide⟩
def hi1276 : CheckedMoment :=
  CheckedMoment.ofBessel hi1276b1 hi1276b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1276 : meanBracketCheck (379/500) lo1276 hi1276=true := by decide +kernel
def bracket1276 : MeanBracket := meanBracketOfMoments (379/500) lo1276 hi1276 accepted1276
def lo1277b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨34,by decide⟩
def lo1277b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨35,by decide⟩
def lo1277 : CheckedMoment :=
  CheckedMoment.ofBessel lo1277b1 lo1277b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1277b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨39,by decide⟩
def hi1277b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨40,by decide⟩
def hi1277 : CheckedMoment :=
  CheckedMoment.ofBessel hi1277b1 hi1277b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1277 : meanBracketCheck (759/1000) lo1277 hi1277=true := by decide +kernel
def bracket1277 : MeanBracket := meanBracketOfMoments (759/1000) lo1277 hi1277 accepted1277
def lo1278b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨44,by decide⟩
def lo1278b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨45,by decide⟩
def lo1278 : CheckedMoment :=
  CheckedMoment.ofBessel lo1278b1 lo1278b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1278b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨49,by decide⟩
def hi1278b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨50,by decide⟩
def hi1278 : CheckedMoment :=
  CheckedMoment.ofBessel hi1278b1 hi1278b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1278 : meanBracketCheck (19/25) lo1278 hi1278=true := by decide +kernel
def bracket1278 : MeanBracket := meanBracketOfMoments (19/25) lo1278 hi1278 accepted1278
def lo1279b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨54,by decide⟩
def lo1279b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨55,by decide⟩
def lo1279 : CheckedMoment :=
  CheckedMoment.ofBessel lo1279b1 lo1279b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1279b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨59,by decide⟩
def hi1279b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0199.rows BesselBatch0199.accepted ⟨60,by decide⟩
def hi1279 : CheckedMoment :=
  CheckedMoment.ofBessel hi1279b1 hi1279b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1279 : meanBracketCheck (761/1000) lo1279 hi1279=true := by decide +kernel
def bracket1279 : MeanBracket := meanBracketOfMoments (761/1000) lo1279 hi1279 accepted1279
#print axioms bracket1264
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0079
