import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0040
import BecknerOnofri.EntropyScalarCertificate.Bessel0041
import BecknerOnofri.EntropyScalarCertificate.Bessel0042
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0016
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0256b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨0,by decide⟩
def lo0256b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨1,by decide⟩
def lo0256 : CheckedMoment :=
  CheckedMoment.ofBessel lo0256b1 lo0256b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0256b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨5,by decide⟩
def hi0256b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨6,by decide⟩
def hi0256 : CheckedMoment :=
  CheckedMoment.ofBessel hi0256b1 hi0256b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0256 : meanBracketCheck (1077/10000) lo0256 hi0256=true := by decide +kernel
def bracket0256 : MeanBracket := meanBracketOfMoments (1077/10000) lo0256 hi0256 accepted0256
def lo0257b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨10,by decide⟩
def lo0257b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨11,by decide⟩
def lo0257 : CheckedMoment :=
  CheckedMoment.ofBessel lo0257b1 lo0257b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0257b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨15,by decide⟩
def hi0257b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨16,by decide⟩
def hi0257 : CheckedMoment :=
  CheckedMoment.ofBessel hi0257b1 hi0257b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0257 : meanBracketCheck (1079/10000) lo0257 hi0257=true := by decide +kernel
def bracket0257 : MeanBracket := meanBracketOfMoments (1079/10000) lo0257 hi0257 accepted0257
def lo0258b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨20,by decide⟩
def lo0258b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨21,by decide⟩
def lo0258 : CheckedMoment :=
  CheckedMoment.ofBessel lo0258b1 lo0258b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0258b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨25,by decide⟩
def hi0258b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨26,by decide⟩
def hi0258 : CheckedMoment :=
  CheckedMoment.ofBessel hi0258b1 hi0258b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0258 : meanBracketCheck (1081/10000) lo0258 hi0258=true := by decide +kernel
def bracket0258 : MeanBracket := meanBracketOfMoments (1081/10000) lo0258 hi0258 accepted0258
def lo0259b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨30,by decide⟩
def lo0259b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨31,by decide⟩
def lo0259 : CheckedMoment :=
  CheckedMoment.ofBessel lo0259b1 lo0259b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0259b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨35,by decide⟩
def hi0259b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨36,by decide⟩
def hi0259 : CheckedMoment :=
  CheckedMoment.ofBessel hi0259b1 hi0259b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0259 : meanBracketCheck (1083/10000) lo0259 hi0259=true := by decide +kernel
def bracket0259 : MeanBracket := meanBracketOfMoments (1083/10000) lo0259 hi0259 accepted0259
def lo0260b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨40,by decide⟩
def lo0260b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨41,by decide⟩
def lo0260 : CheckedMoment :=
  CheckedMoment.ofBessel lo0260b1 lo0260b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0260b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨45,by decide⟩
def hi0260b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨46,by decide⟩
def hi0260 : CheckedMoment :=
  CheckedMoment.ofBessel hi0260b1 hi0260b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0260 : meanBracketCheck (217/2000) lo0260 hi0260=true := by decide +kernel
def bracket0260 : MeanBracket := meanBracketOfMoments (217/2000) lo0260 hi0260 accepted0260
def lo0261b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨50,by decide⟩
def lo0261b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨51,by decide⟩
def lo0261 : CheckedMoment :=
  CheckedMoment.ofBessel lo0261b1 lo0261b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0261b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨55,by decide⟩
def hi0261b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨56,by decide⟩
def hi0261 : CheckedMoment :=
  CheckedMoment.ofBessel hi0261b1 hi0261b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0261 : meanBracketCheck (1087/10000) lo0261 hi0261=true := by decide +kernel
def bracket0261 : MeanBracket := meanBracketOfMoments (1087/10000) lo0261 hi0261 accepted0261
def lo0262b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨60,by decide⟩
def lo0262b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0040.rows BesselBatch0040.accepted ⟨61,by decide⟩
def lo0262 : CheckedMoment :=
  CheckedMoment.ofBessel lo0262b1 lo0262b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0262b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨1,by decide⟩
def hi0262b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨2,by decide⟩
def hi0262 : CheckedMoment :=
  CheckedMoment.ofBessel hi0262b1 hi0262b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0262 : meanBracketCheck (1089/10000) lo0262 hi0262=true := by decide +kernel
def bracket0262 : MeanBracket := meanBracketOfMoments (1089/10000) lo0262 hi0262 accepted0262
def lo0263b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨6,by decide⟩
def lo0263b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨7,by decide⟩
def lo0263 : CheckedMoment :=
  CheckedMoment.ofBessel lo0263b1 lo0263b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0263b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨11,by decide⟩
def hi0263b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨12,by decide⟩
def hi0263 : CheckedMoment :=
  CheckedMoment.ofBessel hi0263b1 hi0263b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0263 : meanBracketCheck (1091/10000) lo0263 hi0263=true := by decide +kernel
def bracket0263 : MeanBracket := meanBracketOfMoments (1091/10000) lo0263 hi0263 accepted0263
def lo0264b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨16,by decide⟩
def lo0264b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨17,by decide⟩
def lo0264 : CheckedMoment :=
  CheckedMoment.ofBessel lo0264b1 lo0264b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0264b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨21,by decide⟩
def hi0264b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨22,by decide⟩
def hi0264 : CheckedMoment :=
  CheckedMoment.ofBessel hi0264b1 hi0264b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0264 : meanBracketCheck (1093/10000) lo0264 hi0264=true := by decide +kernel
def bracket0264 : MeanBracket := meanBracketOfMoments (1093/10000) lo0264 hi0264 accepted0264
def lo0265b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨26,by decide⟩
def lo0265b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨27,by decide⟩
def lo0265 : CheckedMoment :=
  CheckedMoment.ofBessel lo0265b1 lo0265b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0265b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨31,by decide⟩
def hi0265b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨32,by decide⟩
def hi0265 : CheckedMoment :=
  CheckedMoment.ofBessel hi0265b1 hi0265b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0265 : meanBracketCheck (219/2000) lo0265 hi0265=true := by decide +kernel
def bracket0265 : MeanBracket := meanBracketOfMoments (219/2000) lo0265 hi0265 accepted0265
def lo0266b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨36,by decide⟩
def lo0266b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨37,by decide⟩
def lo0266 : CheckedMoment :=
  CheckedMoment.ofBessel lo0266b1 lo0266b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0266b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨41,by decide⟩
def hi0266b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨42,by decide⟩
def hi0266 : CheckedMoment :=
  CheckedMoment.ofBessel hi0266b1 hi0266b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0266 : meanBracketCheck (1097/10000) lo0266 hi0266=true := by decide +kernel
def bracket0266 : MeanBracket := meanBracketOfMoments (1097/10000) lo0266 hi0266 accepted0266
def lo0267b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨46,by decide⟩
def lo0267b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨47,by decide⟩
def lo0267 : CheckedMoment :=
  CheckedMoment.ofBessel lo0267b1 lo0267b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0267b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨51,by decide⟩
def hi0267b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨52,by decide⟩
def hi0267 : CheckedMoment :=
  CheckedMoment.ofBessel hi0267b1 hi0267b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0267 : meanBracketCheck (1099/10000) lo0267 hi0267=true := by decide +kernel
def bracket0267 : MeanBracket := meanBracketOfMoments (1099/10000) lo0267 hi0267 accepted0267
def lo0268b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨56,by decide⟩
def lo0268b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨57,by decide⟩
def lo0268 : CheckedMoment :=
  CheckedMoment.ofBessel lo0268b1 lo0268b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0268b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨61,by decide⟩
def hi0268b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨62,by decide⟩
def hi0268 : CheckedMoment :=
  CheckedMoment.ofBessel hi0268b1 hi0268b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0268 : meanBracketCheck (1101/10000) lo0268 hi0268=true := by decide +kernel
def bracket0268 : MeanBracket := meanBracketOfMoments (1101/10000) lo0268 hi0268 accepted0268
def lo0269b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨2,by decide⟩
def lo0269b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨3,by decide⟩
def lo0269 : CheckedMoment :=
  CheckedMoment.ofBessel lo0269b1 lo0269b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0269b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨7,by decide⟩
def hi0269b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨8,by decide⟩
def hi0269 : CheckedMoment :=
  CheckedMoment.ofBessel hi0269b1 hi0269b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0269 : meanBracketCheck (1103/10000) lo0269 hi0269=true := by decide +kernel
def bracket0269 : MeanBracket := meanBracketOfMoments (1103/10000) lo0269 hi0269 accepted0269
def lo0270b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨12,by decide⟩
def lo0270b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨13,by decide⟩
def lo0270 : CheckedMoment :=
  CheckedMoment.ofBessel lo0270b1 lo0270b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0270b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨17,by decide⟩
def hi0270b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨18,by decide⟩
def hi0270 : CheckedMoment :=
  CheckedMoment.ofBessel hi0270b1 hi0270b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0270 : meanBracketCheck (221/2000) lo0270 hi0270=true := by decide +kernel
def bracket0270 : MeanBracket := meanBracketOfMoments (221/2000) lo0270 hi0270 accepted0270
def lo0271b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨22,by decide⟩
def lo0271b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨23,by decide⟩
def lo0271 : CheckedMoment :=
  CheckedMoment.ofBessel lo0271b1 lo0271b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0271b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨27,by decide⟩
def hi0271b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨28,by decide⟩
def hi0271 : CheckedMoment :=
  CheckedMoment.ofBessel hi0271b1 hi0271b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0271 : meanBracketCheck (1107/10000) lo0271 hi0271=true := by decide +kernel
def bracket0271 : MeanBracket := meanBracketOfMoments (1107/10000) lo0271 hi0271 accepted0271
#print axioms bracket0256
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0016
