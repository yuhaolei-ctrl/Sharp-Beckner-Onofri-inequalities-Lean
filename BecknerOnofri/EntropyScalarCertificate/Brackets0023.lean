import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0057
import BecknerOnofri.EntropyScalarCertificate.Bessel0058
import BecknerOnofri.EntropyScalarCertificate.Bessel0059
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0023
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0368b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨32,by decide⟩
def lo0368b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨33,by decide⟩
def lo0368 : CheckedMoment :=
  CheckedMoment.ofBessel lo0368b1 lo0368b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0368b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨37,by decide⟩
def hi0368b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨38,by decide⟩
def hi0368 : CheckedMoment :=
  CheckedMoment.ofBessel hi0368b1 hi0368b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0368 : meanBracketCheck (1301/10000) lo0368 hi0368=true := by decide +kernel
def bracket0368 : MeanBracket := meanBracketOfMoments (1301/10000) lo0368 hi0368 accepted0368
def lo0369b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨42,by decide⟩
def lo0369b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨43,by decide⟩
def lo0369 : CheckedMoment :=
  CheckedMoment.ofBessel lo0369b1 lo0369b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0369b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨47,by decide⟩
def hi0369b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨48,by decide⟩
def hi0369 : CheckedMoment :=
  CheckedMoment.ofBessel hi0369b1 hi0369b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0369 : meanBracketCheck (1303/10000) lo0369 hi0369=true := by decide +kernel
def bracket0369 : MeanBracket := meanBracketOfMoments (1303/10000) lo0369 hi0369 accepted0369
def lo0370b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨52,by decide⟩
def lo0370b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨53,by decide⟩
def lo0370 : CheckedMoment :=
  CheckedMoment.ofBessel lo0370b1 lo0370b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0370b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨57,by decide⟩
def hi0370b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨58,by decide⟩
def hi0370 : CheckedMoment :=
  CheckedMoment.ofBessel hi0370b1 hi0370b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0370 : meanBracketCheck (261/2000) lo0370 hi0370=true := by decide +kernel
def bracket0370 : MeanBracket := meanBracketOfMoments (261/2000) lo0370 hi0370 accepted0370
def lo0371b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨62,by decide⟩
def lo0371b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0057.rows BesselBatch0057.accepted ⟨63,by decide⟩
def lo0371 : CheckedMoment :=
  CheckedMoment.ofBessel lo0371b1 lo0371b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0371b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨3,by decide⟩
def hi0371b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨4,by decide⟩
def hi0371 : CheckedMoment :=
  CheckedMoment.ofBessel hi0371b1 hi0371b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0371 : meanBracketCheck (1307/10000) lo0371 hi0371=true := by decide +kernel
def bracket0371 : MeanBracket := meanBracketOfMoments (1307/10000) lo0371 hi0371 accepted0371
def lo0372b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨8,by decide⟩
def lo0372b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨9,by decide⟩
def lo0372 : CheckedMoment :=
  CheckedMoment.ofBessel lo0372b1 lo0372b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0372b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨13,by decide⟩
def hi0372b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨14,by decide⟩
def hi0372 : CheckedMoment :=
  CheckedMoment.ofBessel hi0372b1 hi0372b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0372 : meanBracketCheck (1309/10000) lo0372 hi0372=true := by decide +kernel
def bracket0372 : MeanBracket := meanBracketOfMoments (1309/10000) lo0372 hi0372 accepted0372
def lo0373b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨18,by decide⟩
def lo0373b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨19,by decide⟩
def lo0373 : CheckedMoment :=
  CheckedMoment.ofBessel lo0373b1 lo0373b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0373b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨23,by decide⟩
def hi0373b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨24,by decide⟩
def hi0373 : CheckedMoment :=
  CheckedMoment.ofBessel hi0373b1 hi0373b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0373 : meanBracketCheck (1311/10000) lo0373 hi0373=true := by decide +kernel
def bracket0373 : MeanBracket := meanBracketOfMoments (1311/10000) lo0373 hi0373 accepted0373
def lo0374b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨28,by decide⟩
def lo0374b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨29,by decide⟩
def lo0374 : CheckedMoment :=
  CheckedMoment.ofBessel lo0374b1 lo0374b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0374b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨33,by decide⟩
def hi0374b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨34,by decide⟩
def hi0374 : CheckedMoment :=
  CheckedMoment.ofBessel hi0374b1 hi0374b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0374 : meanBracketCheck (1313/10000) lo0374 hi0374=true := by decide +kernel
def bracket0374 : MeanBracket := meanBracketOfMoments (1313/10000) lo0374 hi0374 accepted0374
def lo0375b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨38,by decide⟩
def lo0375b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨39,by decide⟩
def lo0375 : CheckedMoment :=
  CheckedMoment.ofBessel lo0375b1 lo0375b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0375b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨43,by decide⟩
def hi0375b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨44,by decide⟩
def hi0375 : CheckedMoment :=
  CheckedMoment.ofBessel hi0375b1 hi0375b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0375 : meanBracketCheck (263/2000) lo0375 hi0375=true := by decide +kernel
def bracket0375 : MeanBracket := meanBracketOfMoments (263/2000) lo0375 hi0375 accepted0375
def lo0376b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨48,by decide⟩
def lo0376b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨49,by decide⟩
def lo0376 : CheckedMoment :=
  CheckedMoment.ofBessel lo0376b1 lo0376b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0376b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨53,by decide⟩
def hi0376b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨54,by decide⟩
def hi0376 : CheckedMoment :=
  CheckedMoment.ofBessel hi0376b1 hi0376b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0376 : meanBracketCheck (1317/10000) lo0376 hi0376=true := by decide +kernel
def bracket0376 : MeanBracket := meanBracketOfMoments (1317/10000) lo0376 hi0376 accepted0376
def lo0377b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨58,by decide⟩
def lo0377b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨59,by decide⟩
def lo0377 : CheckedMoment :=
  CheckedMoment.ofBessel lo0377b1 lo0377b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0377b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0058.rows BesselBatch0058.accepted ⟨63,by decide⟩
def hi0377b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨0,by decide⟩
def hi0377 : CheckedMoment :=
  CheckedMoment.ofBessel hi0377b1 hi0377b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0377 : meanBracketCheck (1319/10000) lo0377 hi0377=true := by decide +kernel
def bracket0377 : MeanBracket := meanBracketOfMoments (1319/10000) lo0377 hi0377 accepted0377
def lo0378b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨4,by decide⟩
def lo0378b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨5,by decide⟩
def lo0378 : CheckedMoment :=
  CheckedMoment.ofBessel lo0378b1 lo0378b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0378b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨9,by decide⟩
def hi0378b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨10,by decide⟩
def hi0378 : CheckedMoment :=
  CheckedMoment.ofBessel hi0378b1 hi0378b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0378 : meanBracketCheck (1321/10000) lo0378 hi0378=true := by decide +kernel
def bracket0378 : MeanBracket := meanBracketOfMoments (1321/10000) lo0378 hi0378 accepted0378
def lo0379b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨14,by decide⟩
def lo0379b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨15,by decide⟩
def lo0379 : CheckedMoment :=
  CheckedMoment.ofBessel lo0379b1 lo0379b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0379b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨19,by decide⟩
def hi0379b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨20,by decide⟩
def hi0379 : CheckedMoment :=
  CheckedMoment.ofBessel hi0379b1 hi0379b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0379 : meanBracketCheck (1323/10000) lo0379 hi0379=true := by decide +kernel
def bracket0379 : MeanBracket := meanBracketOfMoments (1323/10000) lo0379 hi0379 accepted0379
def lo0380b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨24,by decide⟩
def lo0380b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨25,by decide⟩
def lo0380 : CheckedMoment :=
  CheckedMoment.ofBessel lo0380b1 lo0380b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0380b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨29,by decide⟩
def hi0380b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨30,by decide⟩
def hi0380 : CheckedMoment :=
  CheckedMoment.ofBessel hi0380b1 hi0380b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0380 : meanBracketCheck (53/400) lo0380 hi0380=true := by decide +kernel
def bracket0380 : MeanBracket := meanBracketOfMoments (53/400) lo0380 hi0380 accepted0380
def lo0381b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨34,by decide⟩
def lo0381b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨35,by decide⟩
def lo0381 : CheckedMoment :=
  CheckedMoment.ofBessel lo0381b1 lo0381b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0381b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨39,by decide⟩
def hi0381b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨40,by decide⟩
def hi0381 : CheckedMoment :=
  CheckedMoment.ofBessel hi0381b1 hi0381b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0381 : meanBracketCheck (1327/10000) lo0381 hi0381=true := by decide +kernel
def bracket0381 : MeanBracket := meanBracketOfMoments (1327/10000) lo0381 hi0381 accepted0381
def lo0382b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨44,by decide⟩
def lo0382b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨45,by decide⟩
def lo0382 : CheckedMoment :=
  CheckedMoment.ofBessel lo0382b1 lo0382b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0382b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨49,by decide⟩
def hi0382b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨50,by decide⟩
def hi0382 : CheckedMoment :=
  CheckedMoment.ofBessel hi0382b1 hi0382b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0382 : meanBracketCheck (1329/10000) lo0382 hi0382=true := by decide +kernel
def bracket0382 : MeanBracket := meanBracketOfMoments (1329/10000) lo0382 hi0382 accepted0382
def lo0383b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨54,by decide⟩
def lo0383b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨55,by decide⟩
def lo0383 : CheckedMoment :=
  CheckedMoment.ofBessel lo0383b1 lo0383b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0383b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨59,by decide⟩
def hi0383b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0059.rows BesselBatch0059.accepted ⟨60,by decide⟩
def hi0383 : CheckedMoment :=
  CheckedMoment.ofBessel hi0383b1 hi0383b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0383 : meanBracketCheck (1331/10000) lo0383 hi0383=true := by decide +kernel
def bracket0383 : MeanBracket := meanBracketOfMoments (1331/10000) lo0383 hi0383 accepted0383
#print axioms bracket0368
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0023
