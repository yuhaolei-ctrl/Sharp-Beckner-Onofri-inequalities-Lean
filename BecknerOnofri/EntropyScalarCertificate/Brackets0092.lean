module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0230
public import BecknerOnofri.EntropyScalarCertificate.Bessel0231
public import BecknerOnofri.EntropyScalarCertificate.Bessel0232

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0092
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1472b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨0,by decide⟩
def lo1472b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨1,by decide⟩
def lo1472 : CheckedMoment :=
  CheckedMoment.ofBessel lo1472b1 lo1472b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1472b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨5,by decide⟩
def hi1472b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨6,by decide⟩
def hi1472 : CheckedMoment :=
  CheckedMoment.ofBessel hi1472b1 hi1472b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1472 : meanBracketCheck (4197/5000) lo1472 hi1472=true := by decide +kernel
def bracket1472 : MeanBracket := meanBracketOfMoments (4197/5000) lo1472 hi1472 accepted1472
def lo1473b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨10,by decide⟩
def lo1473b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨11,by decide⟩
def lo1473 : CheckedMoment :=
  CheckedMoment.ofBessel lo1473b1 lo1473b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1473b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨15,by decide⟩
def hi1473b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨16,by decide⟩
def hi1473 : CheckedMoment :=
  CheckedMoment.ofBessel hi1473b1 hi1473b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1473 : meanBracketCheck (1679/2000) lo1473 hi1473=true := by decide +kernel
def bracket1473 : MeanBracket := meanBracketOfMoments (1679/2000) lo1473 hi1473 accepted1473
def lo1474b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨20,by decide⟩
def lo1474b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨21,by decide⟩
def lo1474 : CheckedMoment :=
  CheckedMoment.ofBessel lo1474b1 lo1474b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1474b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨25,by decide⟩
def hi1474b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨26,by decide⟩
def hi1474 : CheckedMoment :=
  CheckedMoment.ofBessel hi1474b1 hi1474b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1474 : meanBracketCheck (2099/2500) lo1474 hi1474=true := by decide +kernel
def bracket1474 : MeanBracket := meanBracketOfMoments (2099/2500) lo1474 hi1474 accepted1474
def lo1475b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨30,by decide⟩
def lo1475b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨31,by decide⟩
def lo1475 : CheckedMoment :=
  CheckedMoment.ofBessel lo1475b1 lo1475b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1475b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨35,by decide⟩
def hi1475b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨36,by decide⟩
def hi1475 : CheckedMoment :=
  CheckedMoment.ofBessel hi1475b1 hi1475b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1475 : meanBracketCheck (8397/10000) lo1475 hi1475=true := by decide +kernel
def bracket1475 : MeanBracket := meanBracketOfMoments (8397/10000) lo1475 hi1475 accepted1475
def lo1476b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨40,by decide⟩
def lo1476b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨41,by decide⟩
def lo1476 : CheckedMoment :=
  CheckedMoment.ofBessel lo1476b1 lo1476b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1476b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨45,by decide⟩
def hi1476b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨46,by decide⟩
def hi1476 : CheckedMoment :=
  CheckedMoment.ofBessel hi1476b1 hi1476b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1476 : meanBracketCheck (4199/5000) lo1476 hi1476=true := by decide +kernel
def bracket1476 : MeanBracket := meanBracketOfMoments (4199/5000) lo1476 hi1476 accepted1476
def lo1477b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨50,by decide⟩
def lo1477b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨51,by decide⟩
def lo1477 : CheckedMoment :=
  CheckedMoment.ofBessel lo1477b1 lo1477b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1477b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨55,by decide⟩
def hi1477b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨56,by decide⟩
def hi1477 : CheckedMoment :=
  CheckedMoment.ofBessel hi1477b1 hi1477b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1477 : meanBracketCheck (8399/10000) lo1477 hi1477=true := by decide +kernel
def bracket1477 : MeanBracket := meanBracketOfMoments (8399/10000) lo1477 hi1477 accepted1477
def lo1478b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨60,by decide⟩
def lo1478b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨61,by decide⟩
def lo1478 : CheckedMoment :=
  CheckedMoment.ofBessel lo1478b1 lo1478b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1478b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨1,by decide⟩
def hi1478b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨2,by decide⟩
def hi1478 : CheckedMoment :=
  CheckedMoment.ofBessel hi1478b1 hi1478b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1478 : meanBracketCheck (21/25) lo1478 hi1478=true := by decide +kernel
def bracket1478 : MeanBracket := meanBracketOfMoments (21/25) lo1478 hi1478 accepted1478
def lo1479b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨6,by decide⟩
def lo1479b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨7,by decide⟩
def lo1479 : CheckedMoment :=
  CheckedMoment.ofBessel lo1479b1 lo1479b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1479b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨11,by decide⟩
def hi1479b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨12,by decide⟩
def hi1479 : CheckedMoment :=
  CheckedMoment.ofBessel hi1479b1 hi1479b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1479 : meanBracketCheck (8401/10000) lo1479 hi1479=true := by decide +kernel
def bracket1479 : MeanBracket := meanBracketOfMoments (8401/10000) lo1479 hi1479 accepted1479
def lo1480b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨16,by decide⟩
def lo1480b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨17,by decide⟩
def lo1480 : CheckedMoment :=
  CheckedMoment.ofBessel lo1480b1 lo1480b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1480b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨21,by decide⟩
def hi1480b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨22,by decide⟩
def hi1480 : CheckedMoment :=
  CheckedMoment.ofBessel hi1480b1 hi1480b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1480 : meanBracketCheck (4201/5000) lo1480 hi1480=true := by decide +kernel
def bracket1480 : MeanBracket := meanBracketOfMoments (4201/5000) lo1480 hi1480 accepted1480
def lo1481b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨26,by decide⟩
def lo1481b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨27,by decide⟩
def lo1481 : CheckedMoment :=
  CheckedMoment.ofBessel lo1481b1 lo1481b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1481b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨31,by decide⟩
def hi1481b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨32,by decide⟩
def hi1481 : CheckedMoment :=
  CheckedMoment.ofBessel hi1481b1 hi1481b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1481 : meanBracketCheck (8403/10000) lo1481 hi1481=true := by decide +kernel
def bracket1481 : MeanBracket := meanBracketOfMoments (8403/10000) lo1481 hi1481 accepted1481
def lo1482b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨36,by decide⟩
def lo1482b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨37,by decide⟩
def lo1482 : CheckedMoment :=
  CheckedMoment.ofBessel lo1482b1 lo1482b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1482b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨41,by decide⟩
def hi1482b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨42,by decide⟩
def hi1482 : CheckedMoment :=
  CheckedMoment.ofBessel hi1482b1 hi1482b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1482 : meanBracketCheck (2101/2500) lo1482 hi1482=true := by decide +kernel
def bracket1482 : MeanBracket := meanBracketOfMoments (2101/2500) lo1482 hi1482 accepted1482
def lo1483b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨46,by decide⟩
def lo1483b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨47,by decide⟩
def lo1483 : CheckedMoment :=
  CheckedMoment.ofBessel lo1483b1 lo1483b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1483b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨51,by decide⟩
def hi1483b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨52,by decide⟩
def hi1483 : CheckedMoment :=
  CheckedMoment.ofBessel hi1483b1 hi1483b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1483 : meanBracketCheck (1681/2000) lo1483 hi1483=true := by decide +kernel
def bracket1483 : MeanBracket := meanBracketOfMoments (1681/2000) lo1483 hi1483 accepted1483
def lo1484b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨56,by decide⟩
def lo1484b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨57,by decide⟩
def lo1484 : CheckedMoment :=
  CheckedMoment.ofBessel lo1484b1 lo1484b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1484b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨61,by decide⟩
def hi1484b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨62,by decide⟩
def hi1484 : CheckedMoment :=
  CheckedMoment.ofBessel hi1484b1 hi1484b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1484 : meanBracketCheck (4203/5000) lo1484 hi1484=true := by decide +kernel
def bracket1484 : MeanBracket := meanBracketOfMoments (4203/5000) lo1484 hi1484 accepted1484
def lo1485b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨2,by decide⟩
def lo1485b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨3,by decide⟩
def lo1485 : CheckedMoment :=
  CheckedMoment.ofBessel lo1485b1 lo1485b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1485b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨7,by decide⟩
def hi1485b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨8,by decide⟩
def hi1485 : CheckedMoment :=
  CheckedMoment.ofBessel hi1485b1 hi1485b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1485 : meanBracketCheck (8407/10000) lo1485 hi1485=true := by decide +kernel
def bracket1485 : MeanBracket := meanBracketOfMoments (8407/10000) lo1485 hi1485 accepted1485
def lo1486b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨12,by decide⟩
def lo1486b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨13,by decide⟩
def lo1486 : CheckedMoment :=
  CheckedMoment.ofBessel lo1486b1 lo1486b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1486b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨17,by decide⟩
def hi1486b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨18,by decide⟩
def hi1486 : CheckedMoment :=
  CheckedMoment.ofBessel hi1486b1 hi1486b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1486 : meanBracketCheck (1051/1250) lo1486 hi1486=true := by decide +kernel
def bracket1486 : MeanBracket := meanBracketOfMoments (1051/1250) lo1486 hi1486 accepted1486
def lo1487b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨22,by decide⟩
def lo1487b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨23,by decide⟩
def lo1487 : CheckedMoment :=
  CheckedMoment.ofBessel lo1487b1 lo1487b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1487b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨27,by decide⟩
def hi1487b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨28,by decide⟩
def hi1487 : CheckedMoment :=
  CheckedMoment.ofBessel hi1487b1 hi1487b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1487 : meanBracketCheck (8409/10000) lo1487 hi1487=true := by decide +kernel
def bracket1487 : MeanBracket := meanBracketOfMoments (8409/10000) lo1487 hi1487 accepted1487
#print axioms bracket1472
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0092
