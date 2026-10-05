import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0055
import BecknerOnofri.EntropyScalarCertificate.Bessel0056
import BecknerOnofri.EntropyScalarCertificate.Bessel0057
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0022
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0352b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨0,by decide⟩
def lo0352b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨1,by decide⟩
def lo0352 : CheckedMoment :=
  CheckedMoment.ofBessel lo0352b1 lo0352b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0352b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨5,by decide⟩
def hi0352b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨6,by decide⟩
def hi0352 : CheckedMoment :=
  CheckedMoment.ofBessel hi0352b1 hi0352b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0352 : meanBracketCheck (1269/10000) lo0352 hi0352=true := by decide +kernel
def bracket0352 : MeanBracket := meanBracketOfMoments (1269/10000) lo0352 hi0352 accepted0352
def lo0353b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨10,by decide⟩
def lo0353b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨11,by decide⟩
def lo0353 : CheckedMoment :=
  CheckedMoment.ofBessel lo0353b1 lo0353b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0353b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨15,by decide⟩
def hi0353b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨16,by decide⟩
def hi0353 : CheckedMoment :=
  CheckedMoment.ofBessel hi0353b1 hi0353b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0353 : meanBracketCheck (1271/10000) lo0353 hi0353=true := by decide +kernel
def bracket0353 : MeanBracket := meanBracketOfMoments (1271/10000) lo0353 hi0353 accepted0353
def lo0354b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨20,by decide⟩
def lo0354b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨21,by decide⟩
def lo0354 : CheckedMoment :=
  CheckedMoment.ofBessel lo0354b1 lo0354b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0354b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨25,by decide⟩
def hi0354b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨26,by decide⟩
def hi0354 : CheckedMoment :=
  CheckedMoment.ofBessel hi0354b1 hi0354b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0354 : meanBracketCheck (1273/10000) lo0354 hi0354=true := by decide +kernel
def bracket0354 : MeanBracket := meanBracketOfMoments (1273/10000) lo0354 hi0354 accepted0354
def lo0355b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨30,by decide⟩
def lo0355b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨31,by decide⟩
def lo0355 : CheckedMoment :=
  CheckedMoment.ofBessel lo0355b1 lo0355b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0355b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨35,by decide⟩
def hi0355b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨36,by decide⟩
def hi0355 : CheckedMoment :=
  CheckedMoment.ofBessel hi0355b1 hi0355b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0355 : meanBracketCheck (51/400) lo0355 hi0355=true := by decide +kernel
def bracket0355 : MeanBracket := meanBracketOfMoments (51/400) lo0355 hi0355 accepted0355
def lo0356b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨40,by decide⟩
def lo0356b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨41,by decide⟩
def lo0356 : CheckedMoment :=
  CheckedMoment.ofBessel lo0356b1 lo0356b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0356b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨45,by decide⟩
def hi0356b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨46,by decide⟩
def hi0356 : CheckedMoment :=
  CheckedMoment.ofBessel hi0356b1 hi0356b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0356 : meanBracketCheck (1277/10000) lo0356 hi0356=true := by decide +kernel
def bracket0356 : MeanBracket := meanBracketOfMoments (1277/10000) lo0356 hi0356 accepted0356
def lo0357b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨50,by decide⟩
def lo0357b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨51,by decide⟩
def lo0357 : CheckedMoment :=
  CheckedMoment.ofBessel lo0357b1 lo0357b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0357b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨55,by decide⟩
def hi0357b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨56,by decide⟩
def hi0357 : CheckedMoment :=
  CheckedMoment.ofBessel hi0357b1 hi0357b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0357 : meanBracketCheck (1279/10000) lo0357 hi0357=true := by decide +kernel
def bracket0357 : MeanBracket := meanBracketOfMoments (1279/10000) lo0357 hi0357 accepted0357
def lo0358b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨60,by decide⟩
def lo0358b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨61,by decide⟩
def lo0358 : CheckedMoment :=
  CheckedMoment.ofBessel lo0358b1 lo0358b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0358b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨1,by decide⟩
def hi0358b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨2,by decide⟩
def hi0358 : CheckedMoment :=
  CheckedMoment.ofBessel hi0358b1 hi0358b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0358 : meanBracketCheck (1281/10000) lo0358 hi0358=true := by decide +kernel
def bracket0358 : MeanBracket := meanBracketOfMoments (1281/10000) lo0358 hi0358 accepted0358
def lo0359b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨6,by decide⟩
def lo0359b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨7,by decide⟩
def lo0359 : CheckedMoment :=
  CheckedMoment.ofBessel lo0359b1 lo0359b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0359b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨11,by decide⟩
def hi0359b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨12,by decide⟩
def hi0359 : CheckedMoment :=
  CheckedMoment.ofBessel hi0359b1 hi0359b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0359 : meanBracketCheck (1283/10000) lo0359 hi0359=true := by decide +kernel
def bracket0359 : MeanBracket := meanBracketOfMoments (1283/10000) lo0359 hi0359 accepted0359
def lo0360b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨16,by decide⟩
def lo0360b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨17,by decide⟩
def lo0360 : CheckedMoment :=
  CheckedMoment.ofBessel lo0360b1 lo0360b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0360b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨21,by decide⟩
def hi0360b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨22,by decide⟩
def hi0360 : CheckedMoment :=
  CheckedMoment.ofBessel hi0360b1 hi0360b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0360 : meanBracketCheck (257/2000) lo0360 hi0360=true := by decide +kernel
def bracket0360 : MeanBracket := meanBracketOfMoments (257/2000) lo0360 hi0360 accepted0360
def lo0361b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨26,by decide⟩
def lo0361b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨27,by decide⟩
def lo0361 : CheckedMoment :=
  CheckedMoment.ofBessel lo0361b1 lo0361b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0361b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨31,by decide⟩
def hi0361b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨32,by decide⟩
def hi0361 : CheckedMoment :=
  CheckedMoment.ofBessel hi0361b1 hi0361b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0361 : meanBracketCheck (1287/10000) lo0361 hi0361=true := by decide +kernel
def bracket0361 : MeanBracket := meanBracketOfMoments (1287/10000) lo0361 hi0361 accepted0361
def lo0362b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨36,by decide⟩
def lo0362b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨37,by decide⟩
def lo0362 : CheckedMoment :=
  CheckedMoment.ofBessel lo0362b1 lo0362b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0362b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨41,by decide⟩
def hi0362b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨42,by decide⟩
def hi0362 : CheckedMoment :=
  CheckedMoment.ofBessel hi0362b1 hi0362b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0362 : meanBracketCheck (1289/10000) lo0362 hi0362=true := by decide +kernel
def bracket0362 : MeanBracket := meanBracketOfMoments (1289/10000) lo0362 hi0362 accepted0362
def lo0363b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨46,by decide⟩
def lo0363b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨47,by decide⟩
def lo0363 : CheckedMoment :=
  CheckedMoment.ofBessel lo0363b1 lo0363b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0363b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨51,by decide⟩
def hi0363b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨52,by decide⟩
def hi0363 : CheckedMoment :=
  CheckedMoment.ofBessel hi0363b1 hi0363b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0363 : meanBracketCheck (1291/10000) lo0363 hi0363=true := by decide +kernel
def bracket0363 : MeanBracket := meanBracketOfMoments (1291/10000) lo0363 hi0363 accepted0363
def lo0364b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨56,by decide⟩
def lo0364b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨57,by decide⟩
def lo0364 : CheckedMoment :=
  CheckedMoment.ofBessel lo0364b1 lo0364b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0364b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨61,by decide⟩
def hi0364b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨62,by decide⟩
def hi0364 : CheckedMoment :=
  CheckedMoment.ofBessel hi0364b1 hi0364b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0364 : meanBracketCheck (1293/10000) lo0364 hi0364=true := by decide +kernel
def bracket0364 : MeanBracket := meanBracketOfMoments (1293/10000) lo0364 hi0364 accepted0364
def lo0365b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨2,by decide⟩
def lo0365b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨3,by decide⟩
def lo0365 : CheckedMoment :=
  CheckedMoment.ofBessel lo0365b1 lo0365b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0365b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨7,by decide⟩
def hi0365b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨8,by decide⟩
def hi0365 : CheckedMoment :=
  CheckedMoment.ofBessel hi0365b1 hi0365b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0365 : meanBracketCheck (259/2000) lo0365 hi0365=true := by decide +kernel
def bracket0365 : MeanBracket := meanBracketOfMoments (259/2000) lo0365 hi0365 accepted0365
def lo0366b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨12,by decide⟩
def lo0366b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨13,by decide⟩
def lo0366 : CheckedMoment :=
  CheckedMoment.ofBessel lo0366b1 lo0366b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0366b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨17,by decide⟩
def hi0366b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨18,by decide⟩
def hi0366 : CheckedMoment :=
  CheckedMoment.ofBessel hi0366b1 hi0366b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0366 : meanBracketCheck (1297/10000) lo0366 hi0366=true := by decide +kernel
def bracket0366 : MeanBracket := meanBracketOfMoments (1297/10000) lo0366 hi0366 accepted0366
def lo0367b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨22,by decide⟩
def lo0367b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨23,by decide⟩
def lo0367 : CheckedMoment :=
  CheckedMoment.ofBessel lo0367b1 lo0367b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0367b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨27,by decide⟩
def hi0367b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨28,by decide⟩
def hi0367 : CheckedMoment :=
  CheckedMoment.ofBessel hi0367b1 hi0367b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0367 : meanBracketCheck (1299/10000) lo0367 hi0367=true := by decide +kernel
def bracket0367 : MeanBracket := meanBracketOfMoments (1299/10000) lo0367 hi0367 accepted0367
#print axioms bracket0352
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0022
