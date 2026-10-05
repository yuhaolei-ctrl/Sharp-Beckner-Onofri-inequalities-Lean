module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0222
public import BecknerOnofri.EntropyScalarCertificate.Bessel0223
public import BecknerOnofri.EntropyScalarCertificate.Bessel0224

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0089
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1424b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨32,by decide⟩
def lo1424b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨33,by decide⟩
def lo1424 : CheckedMoment :=
  CheckedMoment.ofBessel lo1424b1 lo1424b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1424b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨37,by decide⟩
def hi1424b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨38,by decide⟩
def hi1424 : CheckedMoment :=
  CheckedMoment.ofBessel hi1424b1 hi1424b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1424 : meanBracketCheck (4173/5000) lo1424 hi1424=true := by decide +kernel
def bracket1424 : MeanBracket := meanBracketOfMoments (4173/5000) lo1424 hi1424 accepted1424
def lo1425b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨42,by decide⟩
def lo1425b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨43,by decide⟩
def lo1425 : CheckedMoment :=
  CheckedMoment.ofBessel lo1425b1 lo1425b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1425b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨47,by decide⟩
def hi1425b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨48,by decide⟩
def hi1425 : CheckedMoment :=
  CheckedMoment.ofBessel hi1425b1 hi1425b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1425 : meanBracketCheck (8347/10000) lo1425 hi1425=true := by decide +kernel
def bracket1425 : MeanBracket := meanBracketOfMoments (8347/10000) lo1425 hi1425 accepted1425
def lo1426b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨52,by decide⟩
def lo1426b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨53,by decide⟩
def lo1426 : CheckedMoment :=
  CheckedMoment.ofBessel lo1426b1 lo1426b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1426b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨57,by decide⟩
def hi1426b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨58,by decide⟩
def hi1426 : CheckedMoment :=
  CheckedMoment.ofBessel hi1426b1 hi1426b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1426 : meanBracketCheck (2087/2500) lo1426 hi1426=true := by decide +kernel
def bracket1426 : MeanBracket := meanBracketOfMoments (2087/2500) lo1426 hi1426 accepted1426
def lo1427b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨62,by decide⟩
def lo1427b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨63,by decide⟩
def lo1427 : CheckedMoment :=
  CheckedMoment.ofBessel lo1427b1 lo1427b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1427b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨3,by decide⟩
def hi1427b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨4,by decide⟩
def hi1427 : CheckedMoment :=
  CheckedMoment.ofBessel hi1427b1 hi1427b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1427 : meanBracketCheck (8349/10000) lo1427 hi1427=true := by decide +kernel
def bracket1427 : MeanBracket := meanBracketOfMoments (8349/10000) lo1427 hi1427 accepted1427
def lo1428b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨8,by decide⟩
def lo1428b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨9,by decide⟩
def lo1428 : CheckedMoment :=
  CheckedMoment.ofBessel lo1428b1 lo1428b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1428b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨13,by decide⟩
def hi1428b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨14,by decide⟩
def hi1428 : CheckedMoment :=
  CheckedMoment.ofBessel hi1428b1 hi1428b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1428 : meanBracketCheck (167/200) lo1428 hi1428=true := by decide +kernel
def bracket1428 : MeanBracket := meanBracketOfMoments (167/200) lo1428 hi1428 accepted1428
def lo1429b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨18,by decide⟩
def lo1429b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨19,by decide⟩
def lo1429 : CheckedMoment :=
  CheckedMoment.ofBessel lo1429b1 lo1429b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1429b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨23,by decide⟩
def hi1429b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨24,by decide⟩
def hi1429 : CheckedMoment :=
  CheckedMoment.ofBessel hi1429b1 hi1429b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1429 : meanBracketCheck (8351/10000) lo1429 hi1429=true := by decide +kernel
def bracket1429 : MeanBracket := meanBracketOfMoments (8351/10000) lo1429 hi1429 accepted1429
def lo1430b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨28,by decide⟩
def lo1430b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨29,by decide⟩
def lo1430 : CheckedMoment :=
  CheckedMoment.ofBessel lo1430b1 lo1430b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1430b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨33,by decide⟩
def hi1430b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨34,by decide⟩
def hi1430 : CheckedMoment :=
  CheckedMoment.ofBessel hi1430b1 hi1430b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1430 : meanBracketCheck (522/625) lo1430 hi1430=true := by decide +kernel
def bracket1430 : MeanBracket := meanBracketOfMoments (522/625) lo1430 hi1430 accepted1430
def lo1431b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨38,by decide⟩
def lo1431b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨39,by decide⟩
def lo1431 : CheckedMoment :=
  CheckedMoment.ofBessel lo1431b1 lo1431b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1431b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨43,by decide⟩
def hi1431b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨44,by decide⟩
def hi1431 : CheckedMoment :=
  CheckedMoment.ofBessel hi1431b1 hi1431b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1431 : meanBracketCheck (8353/10000) lo1431 hi1431=true := by decide +kernel
def bracket1431 : MeanBracket := meanBracketOfMoments (8353/10000) lo1431 hi1431 accepted1431
def lo1432b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨48,by decide⟩
def lo1432b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨49,by decide⟩
def lo1432 : CheckedMoment :=
  CheckedMoment.ofBessel lo1432b1 lo1432b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1432b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨53,by decide⟩
def hi1432b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨54,by decide⟩
def hi1432 : CheckedMoment :=
  CheckedMoment.ofBessel hi1432b1 hi1432b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1432 : meanBracketCheck (4177/5000) lo1432 hi1432=true := by decide +kernel
def bracket1432 : MeanBracket := meanBracketOfMoments (4177/5000) lo1432 hi1432 accepted1432
def lo1433b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨58,by decide⟩
def lo1433b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨59,by decide⟩
def lo1433 : CheckedMoment :=
  CheckedMoment.ofBessel lo1433b1 lo1433b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1433b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨63,by decide⟩
def hi1433b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨0,by decide⟩
def hi1433 : CheckedMoment :=
  CheckedMoment.ofBessel hi1433b1 hi1433b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1433 : meanBracketCheck (1671/2000) lo1433 hi1433=true := by decide +kernel
def bracket1433 : MeanBracket := meanBracketOfMoments (1671/2000) lo1433 hi1433 accepted1433
def lo1434b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨4,by decide⟩
def lo1434b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨5,by decide⟩
def lo1434 : CheckedMoment :=
  CheckedMoment.ofBessel lo1434b1 lo1434b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1434b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨9,by decide⟩
def hi1434b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨10,by decide⟩
def hi1434 : CheckedMoment :=
  CheckedMoment.ofBessel hi1434b1 hi1434b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1434 : meanBracketCheck (2089/2500) lo1434 hi1434=true := by decide +kernel
def bracket1434 : MeanBracket := meanBracketOfMoments (2089/2500) lo1434 hi1434 accepted1434
def lo1435b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨14,by decide⟩
def lo1435b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨15,by decide⟩
def lo1435 : CheckedMoment :=
  CheckedMoment.ofBessel lo1435b1 lo1435b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1435b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨19,by decide⟩
def hi1435b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨20,by decide⟩
def hi1435 : CheckedMoment :=
  CheckedMoment.ofBessel hi1435b1 hi1435b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1435 : meanBracketCheck (8357/10000) lo1435 hi1435=true := by decide +kernel
def bracket1435 : MeanBracket := meanBracketOfMoments (8357/10000) lo1435 hi1435 accepted1435
def lo1436b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨24,by decide⟩
def lo1436b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨25,by decide⟩
def lo1436 : CheckedMoment :=
  CheckedMoment.ofBessel lo1436b1 lo1436b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1436b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨29,by decide⟩
def hi1436b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨30,by decide⟩
def hi1436 : CheckedMoment :=
  CheckedMoment.ofBessel hi1436b1 hi1436b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1436 : meanBracketCheck (4179/5000) lo1436 hi1436=true := by decide +kernel
def bracket1436 : MeanBracket := meanBracketOfMoments (4179/5000) lo1436 hi1436 accepted1436
def lo1437b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨34,by decide⟩
def lo1437b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨35,by decide⟩
def lo1437 : CheckedMoment :=
  CheckedMoment.ofBessel lo1437b1 lo1437b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1437b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨39,by decide⟩
def hi1437b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨40,by decide⟩
def hi1437 : CheckedMoment :=
  CheckedMoment.ofBessel hi1437b1 hi1437b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1437 : meanBracketCheck (8359/10000) lo1437 hi1437=true := by decide +kernel
def bracket1437 : MeanBracket := meanBracketOfMoments (8359/10000) lo1437 hi1437 accepted1437
def lo1438b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨44,by decide⟩
def lo1438b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨45,by decide⟩
def lo1438 : CheckedMoment :=
  CheckedMoment.ofBessel lo1438b1 lo1438b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1438b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨49,by decide⟩
def hi1438b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨50,by decide⟩
def hi1438 : CheckedMoment :=
  CheckedMoment.ofBessel hi1438b1 hi1438b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1438 : meanBracketCheck (209/250) lo1438 hi1438=true := by decide +kernel
def bracket1438 : MeanBracket := meanBracketOfMoments (209/250) lo1438 hi1438 accepted1438
def lo1439b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨54,by decide⟩
def lo1439b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨55,by decide⟩
def lo1439 : CheckedMoment :=
  CheckedMoment.ofBessel lo1439b1 lo1439b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1439b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨59,by decide⟩
def hi1439b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨60,by decide⟩
def hi1439 : CheckedMoment :=
  CheckedMoment.ofBessel hi1439b1 hi1439b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1439 : meanBracketCheck (8361/10000) lo1439 hi1439=true := by decide +kernel
def bracket1439 : MeanBracket := meanBracketOfMoments (8361/10000) lo1439 hi1439 accepted1439
#print axioms bracket1424
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0089
