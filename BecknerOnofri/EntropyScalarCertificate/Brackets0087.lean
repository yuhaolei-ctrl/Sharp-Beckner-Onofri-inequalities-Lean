import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0217
import BecknerOnofri.EntropyScalarCertificate.Bessel0218
import BecknerOnofri.EntropyScalarCertificate.Bessel0219
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0087
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1392b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨32,by decide⟩
def lo1392b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨33,by decide⟩
def lo1392 : CheckedMoment :=
  CheckedMoment.ofBessel lo1392b1 lo1392b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1392b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨37,by decide⟩
def hi1392b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨38,by decide⟩
def hi1392 : CheckedMoment :=
  CheckedMoment.ofBessel hi1392b1 hi1392b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1392 : meanBracketCheck (4157/5000) lo1392 hi1392=true := by decide +kernel
def bracket1392 : MeanBracket := meanBracketOfMoments (4157/5000) lo1392 hi1392 accepted1392
def lo1393b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨42,by decide⟩
def lo1393b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨43,by decide⟩
def lo1393 : CheckedMoment :=
  CheckedMoment.ofBessel lo1393b1 lo1393b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1393b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨47,by decide⟩
def hi1393b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨48,by decide⟩
def hi1393 : CheckedMoment :=
  CheckedMoment.ofBessel hi1393b1 hi1393b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1393 : meanBracketCheck (1663/2000) lo1393 hi1393=true := by decide +kernel
def bracket1393 : MeanBracket := meanBracketOfMoments (1663/2000) lo1393 hi1393 accepted1393
def lo1394b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨52,by decide⟩
def lo1394b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨53,by decide⟩
def lo1394 : CheckedMoment :=
  CheckedMoment.ofBessel lo1394b1 lo1394b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1394b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨57,by decide⟩
def hi1394b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨58,by decide⟩
def hi1394 : CheckedMoment :=
  CheckedMoment.ofBessel hi1394b1 hi1394b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1394 : meanBracketCheck (2079/2500) lo1394 hi1394=true := by decide +kernel
def bracket1394 : MeanBracket := meanBracketOfMoments (2079/2500) lo1394 hi1394 accepted1394
def lo1395b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨62,by decide⟩
def lo1395b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨63,by decide⟩
def lo1395 : CheckedMoment :=
  CheckedMoment.ofBessel lo1395b1 lo1395b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1395b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨3,by decide⟩
def hi1395b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨4,by decide⟩
def hi1395 : CheckedMoment :=
  CheckedMoment.ofBessel hi1395b1 hi1395b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1395 : meanBracketCheck (8317/10000) lo1395 hi1395=true := by decide +kernel
def bracket1395 : MeanBracket := meanBracketOfMoments (8317/10000) lo1395 hi1395 accepted1395
def lo1396b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨8,by decide⟩
def lo1396b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨9,by decide⟩
def lo1396 : CheckedMoment :=
  CheckedMoment.ofBessel lo1396b1 lo1396b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1396b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨13,by decide⟩
def hi1396b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨14,by decide⟩
def hi1396 : CheckedMoment :=
  CheckedMoment.ofBessel hi1396b1 hi1396b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1396 : meanBracketCheck (4159/5000) lo1396 hi1396=true := by decide +kernel
def bracket1396 : MeanBracket := meanBracketOfMoments (4159/5000) lo1396 hi1396 accepted1396
def lo1397b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨18,by decide⟩
def lo1397b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨19,by decide⟩
def lo1397 : CheckedMoment :=
  CheckedMoment.ofBessel lo1397b1 lo1397b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1397b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨23,by decide⟩
def hi1397b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨24,by decide⟩
def hi1397 : CheckedMoment :=
  CheckedMoment.ofBessel hi1397b1 hi1397b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1397 : meanBracketCheck (8319/10000) lo1397 hi1397=true := by decide +kernel
def bracket1397 : MeanBracket := meanBracketOfMoments (8319/10000) lo1397 hi1397 accepted1397
def lo1398b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨28,by decide⟩
def lo1398b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨29,by decide⟩
def lo1398 : CheckedMoment :=
  CheckedMoment.ofBessel lo1398b1 lo1398b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1398b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨33,by decide⟩
def hi1398b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨34,by decide⟩
def hi1398 : CheckedMoment :=
  CheckedMoment.ofBessel hi1398b1 hi1398b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1398 : meanBracketCheck (104/125) lo1398 hi1398=true := by decide +kernel
def bracket1398 : MeanBracket := meanBracketOfMoments (104/125) lo1398 hi1398 accepted1398
def lo1399b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨38,by decide⟩
def lo1399b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨39,by decide⟩
def lo1399 : CheckedMoment :=
  CheckedMoment.ofBessel lo1399b1 lo1399b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1399b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨43,by decide⟩
def hi1399b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨44,by decide⟩
def hi1399 : CheckedMoment :=
  CheckedMoment.ofBessel hi1399b1 hi1399b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1399 : meanBracketCheck (8321/10000) lo1399 hi1399=true := by decide +kernel
def bracket1399 : MeanBracket := meanBracketOfMoments (8321/10000) lo1399 hi1399 accepted1399
def lo1400b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨48,by decide⟩
def lo1400b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨49,by decide⟩
def lo1400 : CheckedMoment :=
  CheckedMoment.ofBessel lo1400b1 lo1400b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1400b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨53,by decide⟩
def hi1400b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨54,by decide⟩
def hi1400 : CheckedMoment :=
  CheckedMoment.ofBessel hi1400b1 hi1400b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1400 : meanBracketCheck (4161/5000) lo1400 hi1400=true := by decide +kernel
def bracket1400 : MeanBracket := meanBracketOfMoments (4161/5000) lo1400 hi1400 accepted1400
def lo1401b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨58,by decide⟩
def lo1401b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨59,by decide⟩
def lo1401 : CheckedMoment :=
  CheckedMoment.ofBessel lo1401b1 lo1401b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1401b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨63,by decide⟩
def hi1401b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨0,by decide⟩
def hi1401 : CheckedMoment :=
  CheckedMoment.ofBessel hi1401b1 hi1401b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1401 : meanBracketCheck (8323/10000) lo1401 hi1401=true := by decide +kernel
def bracket1401 : MeanBracket := meanBracketOfMoments (8323/10000) lo1401 hi1401 accepted1401
def lo1402b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨4,by decide⟩
def lo1402b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨5,by decide⟩
def lo1402 : CheckedMoment :=
  CheckedMoment.ofBessel lo1402b1 lo1402b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1402b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨9,by decide⟩
def hi1402b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨10,by decide⟩
def hi1402 : CheckedMoment :=
  CheckedMoment.ofBessel hi1402b1 hi1402b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1402 : meanBracketCheck (2081/2500) lo1402 hi1402=true := by decide +kernel
def bracket1402 : MeanBracket := meanBracketOfMoments (2081/2500) lo1402 hi1402 accepted1402
def lo1403b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨14,by decide⟩
def lo1403b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨15,by decide⟩
def lo1403 : CheckedMoment :=
  CheckedMoment.ofBessel lo1403b1 lo1403b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1403b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨19,by decide⟩
def hi1403b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨20,by decide⟩
def hi1403 : CheckedMoment :=
  CheckedMoment.ofBessel hi1403b1 hi1403b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1403 : meanBracketCheck (333/400) lo1403 hi1403=true := by decide +kernel
def bracket1403 : MeanBracket := meanBracketOfMoments (333/400) lo1403 hi1403 accepted1403
def lo1404b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨24,by decide⟩
def lo1404b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨25,by decide⟩
def lo1404 : CheckedMoment :=
  CheckedMoment.ofBessel lo1404b1 lo1404b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1404b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨29,by decide⟩
def hi1404b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨30,by decide⟩
def hi1404 : CheckedMoment :=
  CheckedMoment.ofBessel hi1404b1 hi1404b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1404 : meanBracketCheck (4163/5000) lo1404 hi1404=true := by decide +kernel
def bracket1404 : MeanBracket := meanBracketOfMoments (4163/5000) lo1404 hi1404 accepted1404
def lo1405b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨34,by decide⟩
def lo1405b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨35,by decide⟩
def lo1405 : CheckedMoment :=
  CheckedMoment.ofBessel lo1405b1 lo1405b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1405b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨39,by decide⟩
def hi1405b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨40,by decide⟩
def hi1405 : CheckedMoment :=
  CheckedMoment.ofBessel hi1405b1 hi1405b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1405 : meanBracketCheck (8327/10000) lo1405 hi1405=true := by decide +kernel
def bracket1405 : MeanBracket := meanBracketOfMoments (8327/10000) lo1405 hi1405 accepted1405
def lo1406b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨44,by decide⟩
def lo1406b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨45,by decide⟩
def lo1406 : CheckedMoment :=
  CheckedMoment.ofBessel lo1406b1 lo1406b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1406b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨49,by decide⟩
def hi1406b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨50,by decide⟩
def hi1406 : CheckedMoment :=
  CheckedMoment.ofBessel hi1406b1 hi1406b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1406 : meanBracketCheck (1041/1250) lo1406 hi1406=true := by decide +kernel
def bracket1406 : MeanBracket := meanBracketOfMoments (1041/1250) lo1406 hi1406 accepted1406
def lo1407b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨54,by decide⟩
def lo1407b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨55,by decide⟩
def lo1407 : CheckedMoment :=
  CheckedMoment.ofBessel lo1407b1 lo1407b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1407b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨59,by decide⟩
def hi1407b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨60,by decide⟩
def hi1407 : CheckedMoment :=
  CheckedMoment.ofBessel hi1407b1 hi1407b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1407 : meanBracketCheck (8329/10000) lo1407 hi1407=true := by decide +kernel
def bracket1407 : MeanBracket := meanBracketOfMoments (8329/10000) lo1407 hi1407 accepted1407
#print axioms bracket1392
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0087
