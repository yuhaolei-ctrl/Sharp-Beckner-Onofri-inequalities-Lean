import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0227
import BecknerOnofri.EntropyScalarCertificate.Bessel0228
import BecknerOnofri.EntropyScalarCertificate.Bessel0229
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0091
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1456b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨32,by decide⟩
def lo1456b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨33,by decide⟩
def lo1456 : CheckedMoment :=
  CheckedMoment.ofBessel lo1456b1 lo1456b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1456b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨37,by decide⟩
def hi1456b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨38,by decide⟩
def hi1456 : CheckedMoment :=
  CheckedMoment.ofBessel hi1456b1 hi1456b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1456 : meanBracketCheck (4189/5000) lo1456 hi1456=true := by decide +kernel
def bracket1456 : MeanBracket := meanBracketOfMoments (4189/5000) lo1456 hi1456 accepted1456
def lo1457b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨42,by decide⟩
def lo1457b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨43,by decide⟩
def lo1457 : CheckedMoment :=
  CheckedMoment.ofBessel lo1457b1 lo1457b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1457b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨47,by decide⟩
def hi1457b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨48,by decide⟩
def hi1457 : CheckedMoment :=
  CheckedMoment.ofBessel hi1457b1 hi1457b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1457 : meanBracketCheck (8379/10000) lo1457 hi1457=true := by decide +kernel
def bracket1457 : MeanBracket := meanBracketOfMoments (8379/10000) lo1457 hi1457 accepted1457
def lo1458b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨52,by decide⟩
def lo1458b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨53,by decide⟩
def lo1458 : CheckedMoment :=
  CheckedMoment.ofBessel lo1458b1 lo1458b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1458b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨57,by decide⟩
def hi1458b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨58,by decide⟩
def hi1458 : CheckedMoment :=
  CheckedMoment.ofBessel hi1458b1 hi1458b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1458 : meanBracketCheck (419/500) lo1458 hi1458=true := by decide +kernel
def bracket1458 : MeanBracket := meanBracketOfMoments (419/500) lo1458 hi1458 accepted1458
def lo1459b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨62,by decide⟩
def lo1459b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨63,by decide⟩
def lo1459 : CheckedMoment :=
  CheckedMoment.ofBessel lo1459b1 lo1459b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1459b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨3,by decide⟩
def hi1459b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨4,by decide⟩
def hi1459 : CheckedMoment :=
  CheckedMoment.ofBessel hi1459b1 hi1459b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1459 : meanBracketCheck (8381/10000) lo1459 hi1459=true := by decide +kernel
def bracket1459 : MeanBracket := meanBracketOfMoments (8381/10000) lo1459 hi1459 accepted1459
def lo1460b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨8,by decide⟩
def lo1460b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨9,by decide⟩
def lo1460 : CheckedMoment :=
  CheckedMoment.ofBessel lo1460b1 lo1460b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1460b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨13,by decide⟩
def hi1460b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨14,by decide⟩
def hi1460 : CheckedMoment :=
  CheckedMoment.ofBessel hi1460b1 hi1460b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1460 : meanBracketCheck (4191/5000) lo1460 hi1460=true := by decide +kernel
def bracket1460 : MeanBracket := meanBracketOfMoments (4191/5000) lo1460 hi1460 accepted1460
def lo1461b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨18,by decide⟩
def lo1461b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨19,by decide⟩
def lo1461 : CheckedMoment :=
  CheckedMoment.ofBessel lo1461b1 lo1461b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1461b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨23,by decide⟩
def hi1461b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨24,by decide⟩
def hi1461 : CheckedMoment :=
  CheckedMoment.ofBessel hi1461b1 hi1461b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1461 : meanBracketCheck (8383/10000) lo1461 hi1461=true := by decide +kernel
def bracket1461 : MeanBracket := meanBracketOfMoments (8383/10000) lo1461 hi1461 accepted1461
def lo1462b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨28,by decide⟩
def lo1462b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨29,by decide⟩
def lo1462 : CheckedMoment :=
  CheckedMoment.ofBessel lo1462b1 lo1462b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1462b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨33,by decide⟩
def hi1462b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨34,by decide⟩
def hi1462 : CheckedMoment :=
  CheckedMoment.ofBessel hi1462b1 hi1462b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1462 : meanBracketCheck (524/625) lo1462 hi1462=true := by decide +kernel
def bracket1462 : MeanBracket := meanBracketOfMoments (524/625) lo1462 hi1462 accepted1462
def lo1463b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨38,by decide⟩
def lo1463b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨39,by decide⟩
def lo1463 : CheckedMoment :=
  CheckedMoment.ofBessel lo1463b1 lo1463b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1463b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨43,by decide⟩
def hi1463b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨44,by decide⟩
def hi1463 : CheckedMoment :=
  CheckedMoment.ofBessel hi1463b1 hi1463b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1463 : meanBracketCheck (1677/2000) lo1463 hi1463=true := by decide +kernel
def bracket1463 : MeanBracket := meanBracketOfMoments (1677/2000) lo1463 hi1463 accepted1463
def lo1464b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨48,by decide⟩
def lo1464b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨49,by decide⟩
def lo1464 : CheckedMoment :=
  CheckedMoment.ofBessel lo1464b1 lo1464b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1464b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨53,by decide⟩
def hi1464b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨54,by decide⟩
def hi1464 : CheckedMoment :=
  CheckedMoment.ofBessel hi1464b1 hi1464b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1464 : meanBracketCheck (4193/5000) lo1464 hi1464=true := by decide +kernel
def bracket1464 : MeanBracket := meanBracketOfMoments (4193/5000) lo1464 hi1464 accepted1464
def lo1465b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨58,by decide⟩
def lo1465b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨59,by decide⟩
def lo1465 : CheckedMoment :=
  CheckedMoment.ofBessel lo1465b1 lo1465b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1465b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨63,by decide⟩
def hi1465b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨0,by decide⟩
def hi1465 : CheckedMoment :=
  CheckedMoment.ofBessel hi1465b1 hi1465b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1465 : meanBracketCheck (8387/10000) lo1465 hi1465=true := by decide +kernel
def bracket1465 : MeanBracket := meanBracketOfMoments (8387/10000) lo1465 hi1465 accepted1465
def lo1466b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨4,by decide⟩
def lo1466b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨5,by decide⟩
def lo1466 : CheckedMoment :=
  CheckedMoment.ofBessel lo1466b1 lo1466b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1466b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨9,by decide⟩
def hi1466b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨10,by decide⟩
def hi1466 : CheckedMoment :=
  CheckedMoment.ofBessel hi1466b1 hi1466b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1466 : meanBracketCheck (2097/2500) lo1466 hi1466=true := by decide +kernel
def bracket1466 : MeanBracket := meanBracketOfMoments (2097/2500) lo1466 hi1466 accepted1466
def lo1467b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨14,by decide⟩
def lo1467b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨15,by decide⟩
def lo1467 : CheckedMoment :=
  CheckedMoment.ofBessel lo1467b1 lo1467b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1467b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨19,by decide⟩
def hi1467b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨20,by decide⟩
def hi1467 : CheckedMoment :=
  CheckedMoment.ofBessel hi1467b1 hi1467b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1467 : meanBracketCheck (8389/10000) lo1467 hi1467=true := by decide +kernel
def bracket1467 : MeanBracket := meanBracketOfMoments (8389/10000) lo1467 hi1467 accepted1467
def lo1468b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨24,by decide⟩
def lo1468b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨25,by decide⟩
def lo1468 : CheckedMoment :=
  CheckedMoment.ofBessel lo1468b1 lo1468b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1468b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨29,by decide⟩
def hi1468b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨30,by decide⟩
def hi1468 : CheckedMoment :=
  CheckedMoment.ofBessel hi1468b1 hi1468b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1468 : meanBracketCheck (839/1000) lo1468 hi1468=true := by decide +kernel
def bracket1468 : MeanBracket := meanBracketOfMoments (839/1000) lo1468 hi1468 accepted1468
def lo1469b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨34,by decide⟩
def lo1469b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨35,by decide⟩
def lo1469 : CheckedMoment :=
  CheckedMoment.ofBessel lo1469b1 lo1469b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1469b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨39,by decide⟩
def hi1469b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨40,by decide⟩
def hi1469 : CheckedMoment :=
  CheckedMoment.ofBessel hi1469b1 hi1469b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1469 : meanBracketCheck (8391/10000) lo1469 hi1469=true := by decide +kernel
def bracket1469 : MeanBracket := meanBracketOfMoments (8391/10000) lo1469 hi1469 accepted1469
def lo1470b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨44,by decide⟩
def lo1470b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨45,by decide⟩
def lo1470 : CheckedMoment :=
  CheckedMoment.ofBessel lo1470b1 lo1470b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1470b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨49,by decide⟩
def hi1470b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨50,by decide⟩
def hi1470 : CheckedMoment :=
  CheckedMoment.ofBessel hi1470b1 hi1470b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1470 : meanBracketCheck (1049/1250) lo1470 hi1470=true := by decide +kernel
def bracket1470 : MeanBracket := meanBracketOfMoments (1049/1250) lo1470 hi1470 accepted1470
def lo1471b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨54,by decide⟩
def lo1471b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨55,by decide⟩
def lo1471 : CheckedMoment :=
  CheckedMoment.ofBessel lo1471b1 lo1471b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1471b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨59,by decide⟩
def hi1471b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨60,by decide⟩
def hi1471 : CheckedMoment :=
  CheckedMoment.ofBessel hi1471b1 hi1471b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1471 : meanBracketCheck (8393/10000) lo1471 hi1471=true := by decide +kernel
def bracket1471 : MeanBracket := meanBracketOfMoments (8393/10000) lo1471 hi1471 accepted1471
#print axioms bracket1456
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0091
