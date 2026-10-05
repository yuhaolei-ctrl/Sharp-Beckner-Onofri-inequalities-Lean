import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0032
import BecknerOnofri.EntropyScalarCertificate.Bessel0033
import BecknerOnofri.EntropyScalarCertificate.Bessel0034
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0013
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0208b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨32,by decide⟩
def lo0208b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨33,by decide⟩
def lo0208 : CheckedMoment :=
  CheckedMoment.ofBessel lo0208b1 lo0208b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0208b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨37,by decide⟩
def hi0208b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨38,by decide⟩
def hi0208 : CheckedMoment :=
  CheckedMoment.ofBessel hi0208b1 hi0208b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0208 : meanBracketCheck (981/10000) lo0208 hi0208=true := by decide +kernel
def bracket0208 : MeanBracket := meanBracketOfMoments (981/10000) lo0208 hi0208 accepted0208
def lo0209b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨42,by decide⟩
def lo0209b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨43,by decide⟩
def lo0209 : CheckedMoment :=
  CheckedMoment.ofBessel lo0209b1 lo0209b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0209b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨47,by decide⟩
def hi0209b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨48,by decide⟩
def hi0209 : CheckedMoment :=
  CheckedMoment.ofBessel hi0209b1 hi0209b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0209 : meanBracketCheck (983/10000) lo0209 hi0209=true := by decide +kernel
def bracket0209 : MeanBracket := meanBracketOfMoments (983/10000) lo0209 hi0209 accepted0209
def lo0210b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨52,by decide⟩
def lo0210b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨53,by decide⟩
def lo0210 : CheckedMoment :=
  CheckedMoment.ofBessel lo0210b1 lo0210b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0210b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨57,by decide⟩
def hi0210b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨58,by decide⟩
def hi0210 : CheckedMoment :=
  CheckedMoment.ofBessel hi0210b1 hi0210b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0210 : meanBracketCheck (197/2000) lo0210 hi0210=true := by decide +kernel
def bracket0210 : MeanBracket := meanBracketOfMoments (197/2000) lo0210 hi0210 accepted0210
def lo0211b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨62,by decide⟩
def lo0211b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨63,by decide⟩
def lo0211 : CheckedMoment :=
  CheckedMoment.ofBessel lo0211b1 lo0211b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0211b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨3,by decide⟩
def hi0211b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨4,by decide⟩
def hi0211 : CheckedMoment :=
  CheckedMoment.ofBessel hi0211b1 hi0211b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0211 : meanBracketCheck (987/10000) lo0211 hi0211=true := by decide +kernel
def bracket0211 : MeanBracket := meanBracketOfMoments (987/10000) lo0211 hi0211 accepted0211
def lo0212b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨8,by decide⟩
def lo0212b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨9,by decide⟩
def lo0212 : CheckedMoment :=
  CheckedMoment.ofBessel lo0212b1 lo0212b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0212b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨13,by decide⟩
def hi0212b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨14,by decide⟩
def hi0212 : CheckedMoment :=
  CheckedMoment.ofBessel hi0212b1 hi0212b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0212 : meanBracketCheck (989/10000) lo0212 hi0212=true := by decide +kernel
def bracket0212 : MeanBracket := meanBracketOfMoments (989/10000) lo0212 hi0212 accepted0212
def lo0213b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨18,by decide⟩
def lo0213b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨19,by decide⟩
def lo0213 : CheckedMoment :=
  CheckedMoment.ofBessel lo0213b1 lo0213b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0213b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨23,by decide⟩
def hi0213b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨24,by decide⟩
def hi0213 : CheckedMoment :=
  CheckedMoment.ofBessel hi0213b1 hi0213b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0213 : meanBracketCheck (991/10000) lo0213 hi0213=true := by decide +kernel
def bracket0213 : MeanBracket := meanBracketOfMoments (991/10000) lo0213 hi0213 accepted0213
def lo0214b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨28,by decide⟩
def lo0214b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨29,by decide⟩
def lo0214 : CheckedMoment :=
  CheckedMoment.ofBessel lo0214b1 lo0214b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0214b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨33,by decide⟩
def hi0214b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨34,by decide⟩
def hi0214 : CheckedMoment :=
  CheckedMoment.ofBessel hi0214b1 hi0214b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0214 : meanBracketCheck (993/10000) lo0214 hi0214=true := by decide +kernel
def bracket0214 : MeanBracket := meanBracketOfMoments (993/10000) lo0214 hi0214 accepted0214
def lo0215b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨38,by decide⟩
def lo0215b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨39,by decide⟩
def lo0215 : CheckedMoment :=
  CheckedMoment.ofBessel lo0215b1 lo0215b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0215b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨43,by decide⟩
def hi0215b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨44,by decide⟩
def hi0215 : CheckedMoment :=
  CheckedMoment.ofBessel hi0215b1 hi0215b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0215 : meanBracketCheck (199/2000) lo0215 hi0215=true := by decide +kernel
def bracket0215 : MeanBracket := meanBracketOfMoments (199/2000) lo0215 hi0215 accepted0215
def lo0216b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨48,by decide⟩
def lo0216b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨49,by decide⟩
def lo0216 : CheckedMoment :=
  CheckedMoment.ofBessel lo0216b1 lo0216b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0216b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨53,by decide⟩
def hi0216b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨54,by decide⟩
def hi0216 : CheckedMoment :=
  CheckedMoment.ofBessel hi0216b1 hi0216b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0216 : meanBracketCheck (997/10000) lo0216 hi0216=true := by decide +kernel
def bracket0216 : MeanBracket := meanBracketOfMoments (997/10000) lo0216 hi0216 accepted0216
def lo0217b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨58,by decide⟩
def lo0217b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨59,by decide⟩
def lo0217 : CheckedMoment :=
  CheckedMoment.ofBessel lo0217b1 lo0217b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0217b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨63,by decide⟩
def hi0217b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨0,by decide⟩
def hi0217 : CheckedMoment :=
  CheckedMoment.ofBessel hi0217b1 hi0217b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0217 : meanBracketCheck (999/10000) lo0217 hi0217=true := by decide +kernel
def bracket0217 : MeanBracket := meanBracketOfMoments (999/10000) lo0217 hi0217 accepted0217
def lo0218b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨4,by decide⟩
def lo0218b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨5,by decide⟩
def lo0218 : CheckedMoment :=
  CheckedMoment.ofBessel lo0218b1 lo0218b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0218b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨9,by decide⟩
def hi0218b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨10,by decide⟩
def hi0218 : CheckedMoment :=
  CheckedMoment.ofBessel hi0218b1 hi0218b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0218 : meanBracketCheck (1001/10000) lo0218 hi0218=true := by decide +kernel
def bracket0218 : MeanBracket := meanBracketOfMoments (1001/10000) lo0218 hi0218 accepted0218
def lo0219b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨14,by decide⟩
def lo0219b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨15,by decide⟩
def lo0219 : CheckedMoment :=
  CheckedMoment.ofBessel lo0219b1 lo0219b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0219b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨19,by decide⟩
def hi0219b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨20,by decide⟩
def hi0219 : CheckedMoment :=
  CheckedMoment.ofBessel hi0219b1 hi0219b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0219 : meanBracketCheck (1003/10000) lo0219 hi0219=true := by decide +kernel
def bracket0219 : MeanBracket := meanBracketOfMoments (1003/10000) lo0219 hi0219 accepted0219
def lo0220b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨24,by decide⟩
def lo0220b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨25,by decide⟩
def lo0220 : CheckedMoment :=
  CheckedMoment.ofBessel lo0220b1 lo0220b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0220b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨29,by decide⟩
def hi0220b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨30,by decide⟩
def hi0220 : CheckedMoment :=
  CheckedMoment.ofBessel hi0220b1 hi0220b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0220 : meanBracketCheck (201/2000) lo0220 hi0220=true := by decide +kernel
def bracket0220 : MeanBracket := meanBracketOfMoments (201/2000) lo0220 hi0220 accepted0220
def lo0221b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨34,by decide⟩
def lo0221b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨35,by decide⟩
def lo0221 : CheckedMoment :=
  CheckedMoment.ofBessel lo0221b1 lo0221b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0221b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨39,by decide⟩
def hi0221b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨40,by decide⟩
def hi0221 : CheckedMoment :=
  CheckedMoment.ofBessel hi0221b1 hi0221b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0221 : meanBracketCheck (1007/10000) lo0221 hi0221=true := by decide +kernel
def bracket0221 : MeanBracket := meanBracketOfMoments (1007/10000) lo0221 hi0221 accepted0221
def lo0222b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨44,by decide⟩
def lo0222b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨45,by decide⟩
def lo0222 : CheckedMoment :=
  CheckedMoment.ofBessel lo0222b1 lo0222b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0222b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨49,by decide⟩
def hi0222b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨50,by decide⟩
def hi0222 : CheckedMoment :=
  CheckedMoment.ofBessel hi0222b1 hi0222b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0222 : meanBracketCheck (1009/10000) lo0222 hi0222=true := by decide +kernel
def bracket0222 : MeanBracket := meanBracketOfMoments (1009/10000) lo0222 hi0222 accepted0222
def lo0223b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨54,by decide⟩
def lo0223b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨55,by decide⟩
def lo0223 : CheckedMoment :=
  CheckedMoment.ofBessel lo0223b1 lo0223b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0223b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨59,by decide⟩
def hi0223b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨60,by decide⟩
def hi0223 : CheckedMoment :=
  CheckedMoment.ofBessel hi0223b1 hi0223b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0223 : meanBracketCheck (1011/10000) lo0223 hi0223=true := by decide +kernel
def bracket0223 : MeanBracket := meanBracketOfMoments (1011/10000) lo0223 hi0223 accepted0223
#print axioms bracket0208
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0013
