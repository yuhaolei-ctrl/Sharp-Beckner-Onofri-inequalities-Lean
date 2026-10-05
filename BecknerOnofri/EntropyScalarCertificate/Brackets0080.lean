module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0200
public import BecknerOnofri.EntropyScalarCertificate.Bessel0201
public import BecknerOnofri.EntropyScalarCertificate.Bessel0202

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0080
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1280b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨0,by decide⟩
def lo1280b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨1,by decide⟩
def lo1280 : CheckedMoment :=
  CheckedMoment.ofBessel lo1280b1 lo1280b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1280b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨5,by decide⟩
def hi1280b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨6,by decide⟩
def hi1280 : CheckedMoment :=
  CheckedMoment.ofBessel hi1280b1 hi1280b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1280 : meanBracketCheck (381/500) lo1280 hi1280=true := by decide +kernel
def bracket1280 : MeanBracket := meanBracketOfMoments (381/500) lo1280 hi1280 accepted1280
def lo1281b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨10,by decide⟩
def lo1281b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨11,by decide⟩
def lo1281 : CheckedMoment :=
  CheckedMoment.ofBessel lo1281b1 lo1281b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1281b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨15,by decide⟩
def hi1281b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨16,by decide⟩
def hi1281 : CheckedMoment :=
  CheckedMoment.ofBessel hi1281b1 hi1281b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1281 : meanBracketCheck (763/1000) lo1281 hi1281=true := by decide +kernel
def bracket1281 : MeanBracket := meanBracketOfMoments (763/1000) lo1281 hi1281 accepted1281
def lo1282b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨20,by decide⟩
def lo1282b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨21,by decide⟩
def lo1282 : CheckedMoment :=
  CheckedMoment.ofBessel lo1282b1 lo1282b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1282b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨25,by decide⟩
def hi1282b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨26,by decide⟩
def hi1282 : CheckedMoment :=
  CheckedMoment.ofBessel hi1282b1 hi1282b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1282 : meanBracketCheck (191/250) lo1282 hi1282=true := by decide +kernel
def bracket1282 : MeanBracket := meanBracketOfMoments (191/250) lo1282 hi1282 accepted1282
def lo1283b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨30,by decide⟩
def lo1283b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨31,by decide⟩
def lo1283 : CheckedMoment :=
  CheckedMoment.ofBessel lo1283b1 lo1283b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1283b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨35,by decide⟩
def hi1283b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨36,by decide⟩
def hi1283 : CheckedMoment :=
  CheckedMoment.ofBessel hi1283b1 hi1283b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1283 : meanBracketCheck (153/200) lo1283 hi1283=true := by decide +kernel
def bracket1283 : MeanBracket := meanBracketOfMoments (153/200) lo1283 hi1283 accepted1283
def lo1284b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨40,by decide⟩
def lo1284b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨41,by decide⟩
def lo1284 : CheckedMoment :=
  CheckedMoment.ofBessel lo1284b1 lo1284b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1284b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨45,by decide⟩
def hi1284b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨46,by decide⟩
def hi1284 : CheckedMoment :=
  CheckedMoment.ofBessel hi1284b1 hi1284b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1284 : meanBracketCheck (383/500) lo1284 hi1284=true := by decide +kernel
def bracket1284 : MeanBracket := meanBracketOfMoments (383/500) lo1284 hi1284 accepted1284
def lo1285b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨50,by decide⟩
def lo1285b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨51,by decide⟩
def lo1285 : CheckedMoment :=
  CheckedMoment.ofBessel lo1285b1 lo1285b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1285b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨55,by decide⟩
def hi1285b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨56,by decide⟩
def hi1285 : CheckedMoment :=
  CheckedMoment.ofBessel hi1285b1 hi1285b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1285 : meanBracketCheck (767/1000) lo1285 hi1285=true := by decide +kernel
def bracket1285 : MeanBracket := meanBracketOfMoments (767/1000) lo1285 hi1285 accepted1285
def lo1286b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨60,by decide⟩
def lo1286b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0200.rows BesselBatch0200.accepted ⟨61,by decide⟩
def lo1286 : CheckedMoment :=
  CheckedMoment.ofBessel lo1286b1 lo1286b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1286b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨1,by decide⟩
def hi1286b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨2,by decide⟩
def hi1286 : CheckedMoment :=
  CheckedMoment.ofBessel hi1286b1 hi1286b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1286 : meanBracketCheck (96/125) lo1286 hi1286=true := by decide +kernel
def bracket1286 : MeanBracket := meanBracketOfMoments (96/125) lo1286 hi1286 accepted1286
def lo1287b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨6,by decide⟩
def lo1287b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨7,by decide⟩
def lo1287 : CheckedMoment :=
  CheckedMoment.ofBessel lo1287b1 lo1287b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1287b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨11,by decide⟩
def hi1287b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨12,by decide⟩
def hi1287 : CheckedMoment :=
  CheckedMoment.ofBessel hi1287b1 hi1287b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1287 : meanBracketCheck (769/1000) lo1287 hi1287=true := by decide +kernel
def bracket1287 : MeanBracket := meanBracketOfMoments (769/1000) lo1287 hi1287 accepted1287
def lo1288b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨16,by decide⟩
def lo1288b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨17,by decide⟩
def lo1288 : CheckedMoment :=
  CheckedMoment.ofBessel lo1288b1 lo1288b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1288b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨21,by decide⟩
def hi1288b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨22,by decide⟩
def hi1288 : CheckedMoment :=
  CheckedMoment.ofBessel hi1288b1 hi1288b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1288 : meanBracketCheck (77/100) lo1288 hi1288=true := by decide +kernel
def bracket1288 : MeanBracket := meanBracketOfMoments (77/100) lo1288 hi1288 accepted1288
def lo1289b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨26,by decide⟩
def lo1289b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨27,by decide⟩
def lo1289 : CheckedMoment :=
  CheckedMoment.ofBessel lo1289b1 lo1289b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1289b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨31,by decide⟩
def hi1289b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨32,by decide⟩
def hi1289 : CheckedMoment :=
  CheckedMoment.ofBessel hi1289b1 hi1289b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1289 : meanBracketCheck (771/1000) lo1289 hi1289=true := by decide +kernel
def bracket1289 : MeanBracket := meanBracketOfMoments (771/1000) lo1289 hi1289 accepted1289
def lo1290b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨36,by decide⟩
def lo1290b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨37,by decide⟩
def lo1290 : CheckedMoment :=
  CheckedMoment.ofBessel lo1290b1 lo1290b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1290b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨41,by decide⟩
def hi1290b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨42,by decide⟩
def hi1290 : CheckedMoment :=
  CheckedMoment.ofBessel hi1290b1 hi1290b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1290 : meanBracketCheck (193/250) lo1290 hi1290=true := by decide +kernel
def bracket1290 : MeanBracket := meanBracketOfMoments (193/250) lo1290 hi1290 accepted1290
def lo1291b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨46,by decide⟩
def lo1291b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨47,by decide⟩
def lo1291 : CheckedMoment :=
  CheckedMoment.ofBessel lo1291b1 lo1291b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1291b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨51,by decide⟩
def hi1291b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨52,by decide⟩
def hi1291 : CheckedMoment :=
  CheckedMoment.ofBessel hi1291b1 hi1291b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1291 : meanBracketCheck (773/1000) lo1291 hi1291=true := by decide +kernel
def bracket1291 : MeanBracket := meanBracketOfMoments (773/1000) lo1291 hi1291 accepted1291
def lo1292b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨56,by decide⟩
def lo1292b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨57,by decide⟩
def lo1292 : CheckedMoment :=
  CheckedMoment.ofBessel lo1292b1 lo1292b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1292b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨61,by decide⟩
def hi1292b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨62,by decide⟩
def hi1292 : CheckedMoment :=
  CheckedMoment.ofBessel hi1292b1 hi1292b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1292 : meanBracketCheck (387/500) lo1292 hi1292=true := by decide +kernel
def bracket1292 : MeanBracket := meanBracketOfMoments (387/500) lo1292 hi1292 accepted1292
def lo1293b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨2,by decide⟩
def lo1293b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨3,by decide⟩
def lo1293 : CheckedMoment :=
  CheckedMoment.ofBessel lo1293b1 lo1293b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1293b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨7,by decide⟩
def hi1293b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨8,by decide⟩
def hi1293 : CheckedMoment :=
  CheckedMoment.ofBessel hi1293b1 hi1293b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1293 : meanBracketCheck (31/40) lo1293 hi1293=true := by decide +kernel
def bracket1293 : MeanBracket := meanBracketOfMoments (31/40) lo1293 hi1293 accepted1293
def lo1294b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨12,by decide⟩
def lo1294b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨13,by decide⟩
def lo1294 : CheckedMoment :=
  CheckedMoment.ofBessel lo1294b1 lo1294b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1294b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨17,by decide⟩
def hi1294b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨18,by decide⟩
def hi1294 : CheckedMoment :=
  CheckedMoment.ofBessel hi1294b1 hi1294b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1294 : meanBracketCheck (97/125) lo1294 hi1294=true := by decide +kernel
def bracket1294 : MeanBracket := meanBracketOfMoments (97/125) lo1294 hi1294 accepted1294
def lo1295b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨22,by decide⟩
def lo1295b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨23,by decide⟩
def lo1295 : CheckedMoment :=
  CheckedMoment.ofBessel lo1295b1 lo1295b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1295b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨27,by decide⟩
def hi1295b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨28,by decide⟩
def hi1295 : CheckedMoment :=
  CheckedMoment.ofBessel hi1295b1 hi1295b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1295 : meanBracketCheck (777/1000) lo1295 hi1295=true := by decide +kernel
def bracket1295 : MeanBracket := meanBracketOfMoments (777/1000) lo1295 hi1295 accepted1295
#print axioms bracket1280
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0080
