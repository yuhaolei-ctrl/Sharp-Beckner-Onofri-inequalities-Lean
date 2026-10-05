import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0192
import BecknerOnofri.EntropyScalarCertificate.Bessel0193
import BecknerOnofri.EntropyScalarCertificate.Bessel0194
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0077
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1232b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨32,by decide⟩
def lo1232b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨33,by decide⟩
def lo1232 : CheckedMoment :=
  CheckedMoment.ofBessel lo1232b1 lo1232b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1232b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨37,by decide⟩
def hi1232b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨38,by decide⟩
def hi1232 : CheckedMoment :=
  CheckedMoment.ofBessel hi1232b1 hi1232b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1232 : meanBracketCheck (357/500) lo1232 hi1232=true := by decide +kernel
def bracket1232 : MeanBracket := meanBracketOfMoments (357/500) lo1232 hi1232 accepted1232
def lo1233b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨42,by decide⟩
def lo1233b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨43,by decide⟩
def lo1233 : CheckedMoment :=
  CheckedMoment.ofBessel lo1233b1 lo1233b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1233b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨47,by decide⟩
def hi1233b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨48,by decide⟩
def hi1233 : CheckedMoment :=
  CheckedMoment.ofBessel hi1233b1 hi1233b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1233 : meanBracketCheck (143/200) lo1233 hi1233=true := by decide +kernel
def bracket1233 : MeanBracket := meanBracketOfMoments (143/200) lo1233 hi1233 accepted1233
def lo1234b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨52,by decide⟩
def lo1234b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨53,by decide⟩
def lo1234 : CheckedMoment :=
  CheckedMoment.ofBessel lo1234b1 lo1234b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1234b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨57,by decide⟩
def hi1234b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨58,by decide⟩
def hi1234 : CheckedMoment :=
  CheckedMoment.ofBessel hi1234b1 hi1234b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1234 : meanBracketCheck (179/250) lo1234 hi1234=true := by decide +kernel
def bracket1234 : MeanBracket := meanBracketOfMoments (179/250) lo1234 hi1234 accepted1234
def lo1235b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨62,by decide⟩
def lo1235b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨63,by decide⟩
def lo1235 : CheckedMoment :=
  CheckedMoment.ofBessel lo1235b1 lo1235b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1235b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨3,by decide⟩
def hi1235b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨4,by decide⟩
def hi1235 : CheckedMoment :=
  CheckedMoment.ofBessel hi1235b1 hi1235b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1235 : meanBracketCheck (717/1000) lo1235 hi1235=true := by decide +kernel
def bracket1235 : MeanBracket := meanBracketOfMoments (717/1000) lo1235 hi1235 accepted1235
def lo1236b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨8,by decide⟩
def lo1236b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨9,by decide⟩
def lo1236 : CheckedMoment :=
  CheckedMoment.ofBessel lo1236b1 lo1236b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1236b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨13,by decide⟩
def hi1236b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨14,by decide⟩
def hi1236 : CheckedMoment :=
  CheckedMoment.ofBessel hi1236b1 hi1236b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1236 : meanBracketCheck (359/500) lo1236 hi1236=true := by decide +kernel
def bracket1236 : MeanBracket := meanBracketOfMoments (359/500) lo1236 hi1236 accepted1236
def lo1237b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨18,by decide⟩
def lo1237b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨19,by decide⟩
def lo1237 : CheckedMoment :=
  CheckedMoment.ofBessel lo1237b1 lo1237b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1237b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨23,by decide⟩
def hi1237b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨24,by decide⟩
def hi1237 : CheckedMoment :=
  CheckedMoment.ofBessel hi1237b1 hi1237b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1237 : meanBracketCheck (719/1000) lo1237 hi1237=true := by decide +kernel
def bracket1237 : MeanBracket := meanBracketOfMoments (719/1000) lo1237 hi1237 accepted1237
def lo1238b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨28,by decide⟩
def lo1238b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨29,by decide⟩
def lo1238 : CheckedMoment :=
  CheckedMoment.ofBessel lo1238b1 lo1238b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1238b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨33,by decide⟩
def hi1238b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨34,by decide⟩
def hi1238 : CheckedMoment :=
  CheckedMoment.ofBessel hi1238b1 hi1238b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1238 : meanBracketCheck (18/25) lo1238 hi1238=true := by decide +kernel
def bracket1238 : MeanBracket := meanBracketOfMoments (18/25) lo1238 hi1238 accepted1238
def lo1239b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨38,by decide⟩
def lo1239b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨39,by decide⟩
def lo1239 : CheckedMoment :=
  CheckedMoment.ofBessel lo1239b1 lo1239b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1239b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨43,by decide⟩
def hi1239b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨44,by decide⟩
def hi1239 : CheckedMoment :=
  CheckedMoment.ofBessel hi1239b1 hi1239b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1239 : meanBracketCheck (721/1000) lo1239 hi1239=true := by decide +kernel
def bracket1239 : MeanBracket := meanBracketOfMoments (721/1000) lo1239 hi1239 accepted1239
def lo1240b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨48,by decide⟩
def lo1240b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨49,by decide⟩
def lo1240 : CheckedMoment :=
  CheckedMoment.ofBessel lo1240b1 lo1240b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1240b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨53,by decide⟩
def hi1240b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨54,by decide⟩
def hi1240 : CheckedMoment :=
  CheckedMoment.ofBessel hi1240b1 hi1240b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1240 : meanBracketCheck (361/500) lo1240 hi1240=true := by decide +kernel
def bracket1240 : MeanBracket := meanBracketOfMoments (361/500) lo1240 hi1240 accepted1240
def lo1241b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨58,by decide⟩
def lo1241b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨59,by decide⟩
def lo1241 : CheckedMoment :=
  CheckedMoment.ofBessel lo1241b1 lo1241b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1241b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨63,by decide⟩
def hi1241b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨0,by decide⟩
def hi1241 : CheckedMoment :=
  CheckedMoment.ofBessel hi1241b1 hi1241b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1241 : meanBracketCheck (723/1000) lo1241 hi1241=true := by decide +kernel
def bracket1241 : MeanBracket := meanBracketOfMoments (723/1000) lo1241 hi1241 accepted1241
def lo1242b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨4,by decide⟩
def lo1242b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨5,by decide⟩
def lo1242 : CheckedMoment :=
  CheckedMoment.ofBessel lo1242b1 lo1242b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1242b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨9,by decide⟩
def hi1242b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨10,by decide⟩
def hi1242 : CheckedMoment :=
  CheckedMoment.ofBessel hi1242b1 hi1242b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1242 : meanBracketCheck (181/250) lo1242 hi1242=true := by decide +kernel
def bracket1242 : MeanBracket := meanBracketOfMoments (181/250) lo1242 hi1242 accepted1242
def lo1243b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨14,by decide⟩
def lo1243b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨15,by decide⟩
def lo1243 : CheckedMoment :=
  CheckedMoment.ofBessel lo1243b1 lo1243b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1243b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨19,by decide⟩
def hi1243b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨20,by decide⟩
def hi1243 : CheckedMoment :=
  CheckedMoment.ofBessel hi1243b1 hi1243b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1243 : meanBracketCheck (29/40) lo1243 hi1243=true := by decide +kernel
def bracket1243 : MeanBracket := meanBracketOfMoments (29/40) lo1243 hi1243 accepted1243
def lo1244b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨24,by decide⟩
def lo1244b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨25,by decide⟩
def lo1244 : CheckedMoment :=
  CheckedMoment.ofBessel lo1244b1 lo1244b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1244b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨29,by decide⟩
def hi1244b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨30,by decide⟩
def hi1244 : CheckedMoment :=
  CheckedMoment.ofBessel hi1244b1 hi1244b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1244 : meanBracketCheck (363/500) lo1244 hi1244=true := by decide +kernel
def bracket1244 : MeanBracket := meanBracketOfMoments (363/500) lo1244 hi1244 accepted1244
def lo1245b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨34,by decide⟩
def lo1245b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨35,by decide⟩
def lo1245 : CheckedMoment :=
  CheckedMoment.ofBessel lo1245b1 lo1245b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1245b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨39,by decide⟩
def hi1245b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨40,by decide⟩
def hi1245 : CheckedMoment :=
  CheckedMoment.ofBessel hi1245b1 hi1245b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1245 : meanBracketCheck (727/1000) lo1245 hi1245=true := by decide +kernel
def bracket1245 : MeanBracket := meanBracketOfMoments (727/1000) lo1245 hi1245 accepted1245
def lo1246b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨44,by decide⟩
def lo1246b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨45,by decide⟩
def lo1246 : CheckedMoment :=
  CheckedMoment.ofBessel lo1246b1 lo1246b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1246b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨49,by decide⟩
def hi1246b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨50,by decide⟩
def hi1246 : CheckedMoment :=
  CheckedMoment.ofBessel hi1246b1 hi1246b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1246 : meanBracketCheck (91/125) lo1246 hi1246=true := by decide +kernel
def bracket1246 : MeanBracket := meanBracketOfMoments (91/125) lo1246 hi1246 accepted1246
def lo1247b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨54,by decide⟩
def lo1247b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨55,by decide⟩
def lo1247 : CheckedMoment :=
  CheckedMoment.ofBessel lo1247b1 lo1247b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1247b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨59,by decide⟩
def hi1247b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨60,by decide⟩
def hi1247 : CheckedMoment :=
  CheckedMoment.ofBessel hi1247b1 hi1247b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1247 : meanBracketCheck (729/1000) lo1247 hi1247=true := by decide +kernel
def bracket1247 : MeanBracket := meanBracketOfMoments (729/1000) lo1247 hi1247 accepted1247
#print axioms bracket1232
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0077
