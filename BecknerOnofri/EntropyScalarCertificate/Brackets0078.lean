import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0195
import BecknerOnofri.EntropyScalarCertificate.Bessel0196
import BecknerOnofri.EntropyScalarCertificate.Bessel0197
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0078
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1248b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨0,by decide⟩
def lo1248b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨1,by decide⟩
def lo1248 : CheckedMoment :=
  CheckedMoment.ofBessel lo1248b1 lo1248b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1248b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨5,by decide⟩
def hi1248b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨6,by decide⟩
def hi1248 : CheckedMoment :=
  CheckedMoment.ofBessel hi1248b1 hi1248b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1248 : meanBracketCheck (73/100) lo1248 hi1248=true := by decide +kernel
def bracket1248 : MeanBracket := meanBracketOfMoments (73/100) lo1248 hi1248 accepted1248
def lo1249b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨10,by decide⟩
def lo1249b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨11,by decide⟩
def lo1249 : CheckedMoment :=
  CheckedMoment.ofBessel lo1249b1 lo1249b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1249b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨15,by decide⟩
def hi1249b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨16,by decide⟩
def hi1249 : CheckedMoment :=
  CheckedMoment.ofBessel hi1249b1 hi1249b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1249 : meanBracketCheck (731/1000) lo1249 hi1249=true := by decide +kernel
def bracket1249 : MeanBracket := meanBracketOfMoments (731/1000) lo1249 hi1249 accepted1249
def lo1250b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨20,by decide⟩
def lo1250b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨21,by decide⟩
def lo1250 : CheckedMoment :=
  CheckedMoment.ofBessel lo1250b1 lo1250b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1250b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨25,by decide⟩
def hi1250b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨26,by decide⟩
def hi1250 : CheckedMoment :=
  CheckedMoment.ofBessel hi1250b1 hi1250b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1250 : meanBracketCheck (183/250) lo1250 hi1250=true := by decide +kernel
def bracket1250 : MeanBracket := meanBracketOfMoments (183/250) lo1250 hi1250 accepted1250
def lo1251b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨30,by decide⟩
def lo1251b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨31,by decide⟩
def lo1251 : CheckedMoment :=
  CheckedMoment.ofBessel lo1251b1 lo1251b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1251b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨35,by decide⟩
def hi1251b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨36,by decide⟩
def hi1251 : CheckedMoment :=
  CheckedMoment.ofBessel hi1251b1 hi1251b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1251 : meanBracketCheck (733/1000) lo1251 hi1251=true := by decide +kernel
def bracket1251 : MeanBracket := meanBracketOfMoments (733/1000) lo1251 hi1251 accepted1251
def lo1252b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨40,by decide⟩
def lo1252b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨41,by decide⟩
def lo1252 : CheckedMoment :=
  CheckedMoment.ofBessel lo1252b1 lo1252b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1252b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨45,by decide⟩
def hi1252b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨46,by decide⟩
def hi1252 : CheckedMoment :=
  CheckedMoment.ofBessel hi1252b1 hi1252b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1252 : meanBracketCheck (367/500) lo1252 hi1252=true := by decide +kernel
def bracket1252 : MeanBracket := meanBracketOfMoments (367/500) lo1252 hi1252 accepted1252
def lo1253b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨50,by decide⟩
def lo1253b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨51,by decide⟩
def lo1253 : CheckedMoment :=
  CheckedMoment.ofBessel lo1253b1 lo1253b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1253b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨55,by decide⟩
def hi1253b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨56,by decide⟩
def hi1253 : CheckedMoment :=
  CheckedMoment.ofBessel hi1253b1 hi1253b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1253 : meanBracketCheck (147/200) lo1253 hi1253=true := by decide +kernel
def bracket1253 : MeanBracket := meanBracketOfMoments (147/200) lo1253 hi1253 accepted1253
def lo1254b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨60,by decide⟩
def lo1254b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨61,by decide⟩
def lo1254 : CheckedMoment :=
  CheckedMoment.ofBessel lo1254b1 lo1254b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1254b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨1,by decide⟩
def hi1254b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨2,by decide⟩
def hi1254 : CheckedMoment :=
  CheckedMoment.ofBessel hi1254b1 hi1254b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1254 : meanBracketCheck (92/125) lo1254 hi1254=true := by decide +kernel
def bracket1254 : MeanBracket := meanBracketOfMoments (92/125) lo1254 hi1254 accepted1254
def lo1255b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨6,by decide⟩
def lo1255b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨7,by decide⟩
def lo1255 : CheckedMoment :=
  CheckedMoment.ofBessel lo1255b1 lo1255b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1255b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨11,by decide⟩
def hi1255b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨12,by decide⟩
def hi1255 : CheckedMoment :=
  CheckedMoment.ofBessel hi1255b1 hi1255b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1255 : meanBracketCheck (737/1000) lo1255 hi1255=true := by decide +kernel
def bracket1255 : MeanBracket := meanBracketOfMoments (737/1000) lo1255 hi1255 accepted1255
def lo1256b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨16,by decide⟩
def lo1256b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨17,by decide⟩
def lo1256 : CheckedMoment :=
  CheckedMoment.ofBessel lo1256b1 lo1256b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1256b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨21,by decide⟩
def hi1256b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨22,by decide⟩
def hi1256 : CheckedMoment :=
  CheckedMoment.ofBessel hi1256b1 hi1256b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1256 : meanBracketCheck (369/500) lo1256 hi1256=true := by decide +kernel
def bracket1256 : MeanBracket := meanBracketOfMoments (369/500) lo1256 hi1256 accepted1256
def lo1257b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨26,by decide⟩
def lo1257b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨27,by decide⟩
def lo1257 : CheckedMoment :=
  CheckedMoment.ofBessel lo1257b1 lo1257b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1257b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨31,by decide⟩
def hi1257b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨32,by decide⟩
def hi1257 : CheckedMoment :=
  CheckedMoment.ofBessel hi1257b1 hi1257b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1257 : meanBracketCheck (739/1000) lo1257 hi1257=true := by decide +kernel
def bracket1257 : MeanBracket := meanBracketOfMoments (739/1000) lo1257 hi1257 accepted1257
def lo1258b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨36,by decide⟩
def lo1258b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨37,by decide⟩
def lo1258 : CheckedMoment :=
  CheckedMoment.ofBessel lo1258b1 lo1258b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1258b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨41,by decide⟩
def hi1258b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨42,by decide⟩
def hi1258 : CheckedMoment :=
  CheckedMoment.ofBessel hi1258b1 hi1258b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1258 : meanBracketCheck (37/50) lo1258 hi1258=true := by decide +kernel
def bracket1258 : MeanBracket := meanBracketOfMoments (37/50) lo1258 hi1258 accepted1258
def lo1259b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨46,by decide⟩
def lo1259b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨47,by decide⟩
def lo1259 : CheckedMoment :=
  CheckedMoment.ofBessel lo1259b1 lo1259b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1259b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨51,by decide⟩
def hi1259b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨52,by decide⟩
def hi1259 : CheckedMoment :=
  CheckedMoment.ofBessel hi1259b1 hi1259b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1259 : meanBracketCheck (741/1000) lo1259 hi1259=true := by decide +kernel
def bracket1259 : MeanBracket := meanBracketOfMoments (741/1000) lo1259 hi1259 accepted1259
def lo1260b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨56,by decide⟩
def lo1260b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨57,by decide⟩
def lo1260 : CheckedMoment :=
  CheckedMoment.ofBessel lo1260b1 lo1260b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1260b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨61,by decide⟩
def hi1260b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨62,by decide⟩
def hi1260 : CheckedMoment :=
  CheckedMoment.ofBessel hi1260b1 hi1260b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1260 : meanBracketCheck (371/500) lo1260 hi1260=true := by decide +kernel
def bracket1260 : MeanBracket := meanBracketOfMoments (371/500) lo1260 hi1260 accepted1260
def lo1261b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨2,by decide⟩
def lo1261b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨3,by decide⟩
def lo1261 : CheckedMoment :=
  CheckedMoment.ofBessel lo1261b1 lo1261b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1261b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨7,by decide⟩
def hi1261b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨8,by decide⟩
def hi1261 : CheckedMoment :=
  CheckedMoment.ofBessel hi1261b1 hi1261b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1261 : meanBracketCheck (743/1000) lo1261 hi1261=true := by decide +kernel
def bracket1261 : MeanBracket := meanBracketOfMoments (743/1000) lo1261 hi1261 accepted1261
def lo1262b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨12,by decide⟩
def lo1262b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨13,by decide⟩
def lo1262 : CheckedMoment :=
  CheckedMoment.ofBessel lo1262b1 lo1262b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1262b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨17,by decide⟩
def hi1262b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨18,by decide⟩
def hi1262 : CheckedMoment :=
  CheckedMoment.ofBessel hi1262b1 hi1262b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1262 : meanBracketCheck (93/125) lo1262 hi1262=true := by decide +kernel
def bracket1262 : MeanBracket := meanBracketOfMoments (93/125) lo1262 hi1262 accepted1262
def lo1263b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨22,by decide⟩
def lo1263b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨23,by decide⟩
def lo1263 : CheckedMoment :=
  CheckedMoment.ofBessel lo1263b1 lo1263b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1263b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨27,by decide⟩
def hi1263b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨28,by decide⟩
def hi1263 : CheckedMoment :=
  CheckedMoment.ofBessel hi1263b1 hi1263b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1263 : meanBracketCheck (149/200) lo1263 hi1263=true := by decide +kernel
def bracket1263 : MeanBracket := meanBracketOfMoments (149/200) lo1263 hi1263 accepted1263
#print axioms bracket1248
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0078
