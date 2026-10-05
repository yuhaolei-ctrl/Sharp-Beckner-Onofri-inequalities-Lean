import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0232
import BecknerOnofri.EntropyScalarCertificate.Bessel0233
import BecknerOnofri.EntropyScalarCertificate.Bessel0234
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0093
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1488b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨32,by decide⟩
def lo1488b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨33,by decide⟩
def lo1488 : CheckedMoment :=
  CheckedMoment.ofBessel lo1488b1 lo1488b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1488b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨37,by decide⟩
def hi1488b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨38,by decide⟩
def hi1488 : CheckedMoment :=
  CheckedMoment.ofBessel hi1488b1 hi1488b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1488 : meanBracketCheck (841/1000) lo1488 hi1488=true := by decide +kernel
def bracket1488 : MeanBracket := meanBracketOfMoments (841/1000) lo1488 hi1488 accepted1488
def lo1489b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨42,by decide⟩
def lo1489b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨43,by decide⟩
def lo1489 : CheckedMoment :=
  CheckedMoment.ofBessel lo1489b1 lo1489b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1489b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨47,by decide⟩
def hi1489b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨48,by decide⟩
def hi1489 : CheckedMoment :=
  CheckedMoment.ofBessel hi1489b1 hi1489b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1489 : meanBracketCheck (8411/10000) lo1489 hi1489=true := by decide +kernel
def bracket1489 : MeanBracket := meanBracketOfMoments (8411/10000) lo1489 hi1489 accepted1489
def lo1490b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨52,by decide⟩
def lo1490b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨53,by decide⟩
def lo1490 : CheckedMoment :=
  CheckedMoment.ofBessel lo1490b1 lo1490b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1490b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨57,by decide⟩
def hi1490b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨58,by decide⟩
def hi1490 : CheckedMoment :=
  CheckedMoment.ofBessel hi1490b1 hi1490b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1490 : meanBracketCheck (2103/2500) lo1490 hi1490=true := by decide +kernel
def bracket1490 : MeanBracket := meanBracketOfMoments (2103/2500) lo1490 hi1490 accepted1490
def lo1491b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨62,by decide⟩
def lo1491b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨63,by decide⟩
def lo1491 : CheckedMoment :=
  CheckedMoment.ofBessel lo1491b1 lo1491b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1491b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨3,by decide⟩
def hi1491b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨4,by decide⟩
def hi1491 : CheckedMoment :=
  CheckedMoment.ofBessel hi1491b1 hi1491b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1491 : meanBracketCheck (8413/10000) lo1491 hi1491=true := by decide +kernel
def bracket1491 : MeanBracket := meanBracketOfMoments (8413/10000) lo1491 hi1491 accepted1491
def lo1492b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨8,by decide⟩
def lo1492b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨9,by decide⟩
def lo1492 : CheckedMoment :=
  CheckedMoment.ofBessel lo1492b1 lo1492b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1492b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨13,by decide⟩
def hi1492b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨14,by decide⟩
def hi1492 : CheckedMoment :=
  CheckedMoment.ofBessel hi1492b1 hi1492b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1492 : meanBracketCheck (4207/5000) lo1492 hi1492=true := by decide +kernel
def bracket1492 : MeanBracket := meanBracketOfMoments (4207/5000) lo1492 hi1492 accepted1492
def lo1493b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨18,by decide⟩
def lo1493b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨19,by decide⟩
def lo1493 : CheckedMoment :=
  CheckedMoment.ofBessel lo1493b1 lo1493b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1493b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨23,by decide⟩
def hi1493b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨24,by decide⟩
def hi1493 : CheckedMoment :=
  CheckedMoment.ofBessel hi1493b1 hi1493b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1493 : meanBracketCheck (1683/2000) lo1493 hi1493=true := by decide +kernel
def bracket1493 : MeanBracket := meanBracketOfMoments (1683/2000) lo1493 hi1493 accepted1493
def lo1494b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨28,by decide⟩
def lo1494b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨29,by decide⟩
def lo1494 : CheckedMoment :=
  CheckedMoment.ofBessel lo1494b1 lo1494b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1494b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨33,by decide⟩
def hi1494b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨34,by decide⟩
def hi1494 : CheckedMoment :=
  CheckedMoment.ofBessel hi1494b1 hi1494b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1494 : meanBracketCheck (526/625) lo1494 hi1494=true := by decide +kernel
def bracket1494 : MeanBracket := meanBracketOfMoments (526/625) lo1494 hi1494 accepted1494
def lo1495b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨38,by decide⟩
def lo1495b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨39,by decide⟩
def lo1495 : CheckedMoment :=
  CheckedMoment.ofBessel lo1495b1 lo1495b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1495b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨43,by decide⟩
def hi1495b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨44,by decide⟩
def hi1495 : CheckedMoment :=
  CheckedMoment.ofBessel hi1495b1 hi1495b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1495 : meanBracketCheck (8417/10000) lo1495 hi1495=true := by decide +kernel
def bracket1495 : MeanBracket := meanBracketOfMoments (8417/10000) lo1495 hi1495 accepted1495
def lo1496b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨48,by decide⟩
def lo1496b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨49,by decide⟩
def lo1496 : CheckedMoment :=
  CheckedMoment.ofBessel lo1496b1 lo1496b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1496b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨53,by decide⟩
def hi1496b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨54,by decide⟩
def hi1496 : CheckedMoment :=
  CheckedMoment.ofBessel hi1496b1 hi1496b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1496 : meanBracketCheck (4209/5000) lo1496 hi1496=true := by decide +kernel
def bracket1496 : MeanBracket := meanBracketOfMoments (4209/5000) lo1496 hi1496 accepted1496
def lo1497b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨58,by decide⟩
def lo1497b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨59,by decide⟩
def lo1497 : CheckedMoment :=
  CheckedMoment.ofBessel lo1497b1 lo1497b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1497b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨63,by decide⟩
def hi1497b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨0,by decide⟩
def hi1497 : CheckedMoment :=
  CheckedMoment.ofBessel hi1497b1 hi1497b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1497 : meanBracketCheck (8419/10000) lo1497 hi1497=true := by decide +kernel
def bracket1497 : MeanBracket := meanBracketOfMoments (8419/10000) lo1497 hi1497 accepted1497
def lo1498b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨4,by decide⟩
def lo1498b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨5,by decide⟩
def lo1498 : CheckedMoment :=
  CheckedMoment.ofBessel lo1498b1 lo1498b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1498b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨9,by decide⟩
def hi1498b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨10,by decide⟩
def hi1498 : CheckedMoment :=
  CheckedMoment.ofBessel hi1498b1 hi1498b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1498 : meanBracketCheck (421/500) lo1498 hi1498=true := by decide +kernel
def bracket1498 : MeanBracket := meanBracketOfMoments (421/500) lo1498 hi1498 accepted1498
def lo1499b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨14,by decide⟩
def lo1499b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨15,by decide⟩
def lo1499 : CheckedMoment :=
  CheckedMoment.ofBessel lo1499b1 lo1499b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1499b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨19,by decide⟩
def hi1499b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨20,by decide⟩
def hi1499 : CheckedMoment :=
  CheckedMoment.ofBessel hi1499b1 hi1499b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1499 : meanBracketCheck (8421/10000) lo1499 hi1499=true := by decide +kernel
def bracket1499 : MeanBracket := meanBracketOfMoments (8421/10000) lo1499 hi1499 accepted1499
def lo1500b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨24,by decide⟩
def lo1500b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨25,by decide⟩
def lo1500 : CheckedMoment :=
  CheckedMoment.ofBessel lo1500b1 lo1500b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1500b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨29,by decide⟩
def hi1500b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨30,by decide⟩
def hi1500 : CheckedMoment :=
  CheckedMoment.ofBessel hi1500b1 hi1500b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1500 : meanBracketCheck (4211/5000) lo1500 hi1500=true := by decide +kernel
def bracket1500 : MeanBracket := meanBracketOfMoments (4211/5000) lo1500 hi1500 accepted1500
def lo1501b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨34,by decide⟩
def lo1501b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨35,by decide⟩
def lo1501 : CheckedMoment :=
  CheckedMoment.ofBessel lo1501b1 lo1501b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1501b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨39,by decide⟩
def hi1501b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨40,by decide⟩
def hi1501 : CheckedMoment :=
  CheckedMoment.ofBessel hi1501b1 hi1501b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1501 : meanBracketCheck (8423/10000) lo1501 hi1501=true := by decide +kernel
def bracket1501 : MeanBracket := meanBracketOfMoments (8423/10000) lo1501 hi1501 accepted1501
def lo1502b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨44,by decide⟩
def lo1502b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨45,by decide⟩
def lo1502 : CheckedMoment :=
  CheckedMoment.ofBessel lo1502b1 lo1502b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1502b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨49,by decide⟩
def hi1502b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨50,by decide⟩
def hi1502 : CheckedMoment :=
  CheckedMoment.ofBessel hi1502b1 hi1502b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1502 : meanBracketCheck (1053/1250) lo1502 hi1502=true := by decide +kernel
def bracket1502 : MeanBracket := meanBracketOfMoments (1053/1250) lo1502 hi1502 accepted1502
def lo1503b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨54,by decide⟩
def lo1503b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨55,by decide⟩
def lo1503 : CheckedMoment :=
  CheckedMoment.ofBessel lo1503b1 lo1503b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1503b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨59,by decide⟩
def hi1503b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨60,by decide⟩
def hi1503 : CheckedMoment :=
  CheckedMoment.ofBessel hi1503b1 hi1503b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1503 : meanBracketCheck (337/400) lo1503 hi1503=true := by decide +kernel
def bracket1503 : MeanBracket := meanBracketOfMoments (337/400) lo1503 hi1503 accepted1503
#print axioms bracket1488
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0093
