import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0202
import BecknerOnofri.EntropyScalarCertificate.Bessel0203
import BecknerOnofri.EntropyScalarCertificate.Bessel0204
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0081
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1296b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨32,by decide⟩
def lo1296b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨33,by decide⟩
def lo1296 : CheckedMoment :=
  CheckedMoment.ofBessel lo1296b1 lo1296b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1296b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨37,by decide⟩
def hi1296b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨38,by decide⟩
def hi1296 : CheckedMoment :=
  CheckedMoment.ofBessel hi1296b1 hi1296b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1296 : meanBracketCheck (389/500) lo1296 hi1296=true := by decide +kernel
def bracket1296 : MeanBracket := meanBracketOfMoments (389/500) lo1296 hi1296 accepted1296
def lo1297b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨42,by decide⟩
def lo1297b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨43,by decide⟩
def lo1297 : CheckedMoment :=
  CheckedMoment.ofBessel lo1297b1 lo1297b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1297b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨47,by decide⟩
def hi1297b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨48,by decide⟩
def hi1297 : CheckedMoment :=
  CheckedMoment.ofBessel hi1297b1 hi1297b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1297 : meanBracketCheck (779/1000) lo1297 hi1297=true := by decide +kernel
def bracket1297 : MeanBracket := meanBracketOfMoments (779/1000) lo1297 hi1297 accepted1297
def lo1298b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨52,by decide⟩
def lo1298b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨53,by decide⟩
def lo1298 : CheckedMoment :=
  CheckedMoment.ofBessel lo1298b1 lo1298b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1298b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨57,by decide⟩
def hi1298b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨58,by decide⟩
def hi1298 : CheckedMoment :=
  CheckedMoment.ofBessel hi1298b1 hi1298b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1298 : meanBracketCheck (39/50) lo1298 hi1298=true := by decide +kernel
def bracket1298 : MeanBracket := meanBracketOfMoments (39/50) lo1298 hi1298 accepted1298
def lo1299b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨62,by decide⟩
def lo1299b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨63,by decide⟩
def lo1299 : CheckedMoment :=
  CheckedMoment.ofBessel lo1299b1 lo1299b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1299b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨3,by decide⟩
def hi1299b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨4,by decide⟩
def hi1299 : CheckedMoment :=
  CheckedMoment.ofBessel hi1299b1 hi1299b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1299 : meanBracketCheck (781/1000) lo1299 hi1299=true := by decide +kernel
def bracket1299 : MeanBracket := meanBracketOfMoments (781/1000) lo1299 hi1299 accepted1299
def lo1300b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨8,by decide⟩
def lo1300b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨9,by decide⟩
def lo1300 : CheckedMoment :=
  CheckedMoment.ofBessel lo1300b1 lo1300b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1300b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨13,by decide⟩
def hi1300b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨14,by decide⟩
def hi1300 : CheckedMoment :=
  CheckedMoment.ofBessel hi1300b1 hi1300b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1300 : meanBracketCheck (391/500) lo1300 hi1300=true := by decide +kernel
def bracket1300 : MeanBracket := meanBracketOfMoments (391/500) lo1300 hi1300 accepted1300
def lo1301b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨18,by decide⟩
def lo1301b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨19,by decide⟩
def lo1301 : CheckedMoment :=
  CheckedMoment.ofBessel lo1301b1 lo1301b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1301b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨23,by decide⟩
def hi1301b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨24,by decide⟩
def hi1301 : CheckedMoment :=
  CheckedMoment.ofBessel hi1301b1 hi1301b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1301 : meanBracketCheck (783/1000) lo1301 hi1301=true := by decide +kernel
def bracket1301 : MeanBracket := meanBracketOfMoments (783/1000) lo1301 hi1301 accepted1301
def lo1302b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨28,by decide⟩
def lo1302b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨29,by decide⟩
def lo1302 : CheckedMoment :=
  CheckedMoment.ofBessel lo1302b1 lo1302b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1302b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨33,by decide⟩
def hi1302b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨34,by decide⟩
def hi1302 : CheckedMoment :=
  CheckedMoment.ofBessel hi1302b1 hi1302b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1302 : meanBracketCheck (98/125) lo1302 hi1302=true := by decide +kernel
def bracket1302 : MeanBracket := meanBracketOfMoments (98/125) lo1302 hi1302 accepted1302
def lo1303b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨38,by decide⟩
def lo1303b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨39,by decide⟩
def lo1303 : CheckedMoment :=
  CheckedMoment.ofBessel lo1303b1 lo1303b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1303b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨43,by decide⟩
def hi1303b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨44,by decide⟩
def hi1303 : CheckedMoment :=
  CheckedMoment.ofBessel hi1303b1 hi1303b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1303 : meanBracketCheck (157/200) lo1303 hi1303=true := by decide +kernel
def bracket1303 : MeanBracket := meanBracketOfMoments (157/200) lo1303 hi1303 accepted1303
def lo1304b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨48,by decide⟩
def lo1304b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨49,by decide⟩
def lo1304 : CheckedMoment :=
  CheckedMoment.ofBessel lo1304b1 lo1304b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1304b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨53,by decide⟩
def hi1304b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨54,by decide⟩
def hi1304 : CheckedMoment :=
  CheckedMoment.ofBessel hi1304b1 hi1304b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1304 : meanBracketCheck (393/500) lo1304 hi1304=true := by decide +kernel
def bracket1304 : MeanBracket := meanBracketOfMoments (393/500) lo1304 hi1304 accepted1304
def lo1305b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨58,by decide⟩
def lo1305b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨59,by decide⟩
def lo1305 : CheckedMoment :=
  CheckedMoment.ofBessel lo1305b1 lo1305b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1305b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨63,by decide⟩
def hi1305b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨0,by decide⟩
def hi1305 : CheckedMoment :=
  CheckedMoment.ofBessel hi1305b1 hi1305b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1305 : meanBracketCheck (787/1000) lo1305 hi1305=true := by decide +kernel
def bracket1305 : MeanBracket := meanBracketOfMoments (787/1000) lo1305 hi1305 accepted1305
def lo1306b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨4,by decide⟩
def lo1306b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨5,by decide⟩
def lo1306 : CheckedMoment :=
  CheckedMoment.ofBessel lo1306b1 lo1306b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1306b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨9,by decide⟩
def hi1306b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨10,by decide⟩
def hi1306 : CheckedMoment :=
  CheckedMoment.ofBessel hi1306b1 hi1306b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1306 : meanBracketCheck (197/250) lo1306 hi1306=true := by decide +kernel
def bracket1306 : MeanBracket := meanBracketOfMoments (197/250) lo1306 hi1306 accepted1306
def lo1307b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨14,by decide⟩
def lo1307b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨15,by decide⟩
def lo1307 : CheckedMoment :=
  CheckedMoment.ofBessel lo1307b1 lo1307b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1307b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨19,by decide⟩
def hi1307b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨20,by decide⟩
def hi1307 : CheckedMoment :=
  CheckedMoment.ofBessel hi1307b1 hi1307b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1307 : meanBracketCheck (789/1000) lo1307 hi1307=true := by decide +kernel
def bracket1307 : MeanBracket := meanBracketOfMoments (789/1000) lo1307 hi1307 accepted1307
def lo1308b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨24,by decide⟩
def lo1308b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨25,by decide⟩
def lo1308 : CheckedMoment :=
  CheckedMoment.ofBessel lo1308b1 lo1308b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1308b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨29,by decide⟩
def hi1308b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨30,by decide⟩
def hi1308 : CheckedMoment :=
  CheckedMoment.ofBessel hi1308b1 hi1308b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1308 : meanBracketCheck (79/100) lo1308 hi1308=true := by decide +kernel
def bracket1308 : MeanBracket := meanBracketOfMoments (79/100) lo1308 hi1308 accepted1308
def lo1309b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨34,by decide⟩
def lo1309b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨35,by decide⟩
def lo1309 : CheckedMoment :=
  CheckedMoment.ofBessel lo1309b1 lo1309b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1309b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨39,by decide⟩
def hi1309b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨40,by decide⟩
def hi1309 : CheckedMoment :=
  CheckedMoment.ofBessel hi1309b1 hi1309b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1309 : meanBracketCheck (791/1000) lo1309 hi1309=true := by decide +kernel
def bracket1309 : MeanBracket := meanBracketOfMoments (791/1000) lo1309 hi1309 accepted1309
def lo1310b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨44,by decide⟩
def lo1310b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨45,by decide⟩
def lo1310 : CheckedMoment :=
  CheckedMoment.ofBessel lo1310b1 lo1310b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1310b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨49,by decide⟩
def hi1310b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨50,by decide⟩
def hi1310 : CheckedMoment :=
  CheckedMoment.ofBessel hi1310b1 hi1310b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1310 : meanBracketCheck (99/125) lo1310 hi1310=true := by decide +kernel
def bracket1310 : MeanBracket := meanBracketOfMoments (99/125) lo1310 hi1310 accepted1310
def lo1311b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨54,by decide⟩
def lo1311b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨55,by decide⟩
def lo1311 : CheckedMoment :=
  CheckedMoment.ofBessel lo1311b1 lo1311b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1311b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨59,by decide⟩
def hi1311b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨60,by decide⟩
def hi1311 : CheckedMoment :=
  CheckedMoment.ofBessel hi1311b1 hi1311b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1311 : meanBracketCheck (793/1000) lo1311 hi1311=true := by decide +kernel
def bracket1311 : MeanBracket := meanBracketOfMoments (793/1000) lo1311 hi1311 accepted1311
#print axioms bracket1296
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0081
