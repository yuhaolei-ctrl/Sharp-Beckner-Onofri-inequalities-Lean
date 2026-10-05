module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0240
public import BecknerOnofri.EntropyScalarCertificate.Bessel0241
public import BecknerOnofri.EntropyScalarCertificate.Bessel0242

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0096
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1536b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨0,by decide⟩
def lo1536b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨1,by decide⟩
def lo1536 : CheckedMoment :=
  CheckedMoment.ofBessel lo1536b1 lo1536b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1536b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨5,by decide⟩
def hi1536b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨6,by decide⟩
def hi1536 : CheckedMoment :=
  CheckedMoment.ofBessel hi1536b1 hi1536b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1536 : meanBracketCheck (4229/5000) lo1536 hi1536=true := by decide +kernel
def bracket1536 : MeanBracket := meanBracketOfMoments (4229/5000) lo1536 hi1536 accepted1536
def lo1537b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨10,by decide⟩
def lo1537b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨11,by decide⟩
def lo1537 : CheckedMoment :=
  CheckedMoment.ofBessel lo1537b1 lo1537b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1537b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨15,by decide⟩
def hi1537b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨16,by decide⟩
def hi1537 : CheckedMoment :=
  CheckedMoment.ofBessel hi1537b1 hi1537b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1537 : meanBracketCheck (8459/10000) lo1537 hi1537=true := by decide +kernel
def bracket1537 : MeanBracket := meanBracketOfMoments (8459/10000) lo1537 hi1537 accepted1537
def lo1538b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨20,by decide⟩
def lo1538b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨21,by decide⟩
def lo1538 : CheckedMoment :=
  CheckedMoment.ofBessel lo1538b1 lo1538b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1538b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨25,by decide⟩
def hi1538b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨26,by decide⟩
def hi1538 : CheckedMoment :=
  CheckedMoment.ofBessel hi1538b1 hi1538b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1538 : meanBracketCheck (423/500) lo1538 hi1538=true := by decide +kernel
def bracket1538 : MeanBracket := meanBracketOfMoments (423/500) lo1538 hi1538 accepted1538
def lo1539b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨30,by decide⟩
def lo1539b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨31,by decide⟩
def lo1539 : CheckedMoment :=
  CheckedMoment.ofBessel lo1539b1 lo1539b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1539b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨35,by decide⟩
def hi1539b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨36,by decide⟩
def hi1539 : CheckedMoment :=
  CheckedMoment.ofBessel hi1539b1 hi1539b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1539 : meanBracketCheck (8461/10000) lo1539 hi1539=true := by decide +kernel
def bracket1539 : MeanBracket := meanBracketOfMoments (8461/10000) lo1539 hi1539 accepted1539
def lo1540b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨40,by decide⟩
def lo1540b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨41,by decide⟩
def lo1540 : CheckedMoment :=
  CheckedMoment.ofBessel lo1540b1 lo1540b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1540b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨45,by decide⟩
def hi1540b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨46,by decide⟩
def hi1540 : CheckedMoment :=
  CheckedMoment.ofBessel hi1540b1 hi1540b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1540 : meanBracketCheck (4231/5000) lo1540 hi1540=true := by decide +kernel
def bracket1540 : MeanBracket := meanBracketOfMoments (4231/5000) lo1540 hi1540 accepted1540
def lo1541b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨50,by decide⟩
def lo1541b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨51,by decide⟩
def lo1541 : CheckedMoment :=
  CheckedMoment.ofBessel lo1541b1 lo1541b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1541b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨55,by decide⟩
def hi1541b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨56,by decide⟩
def hi1541 : CheckedMoment :=
  CheckedMoment.ofBessel hi1541b1 hi1541b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1541 : meanBracketCheck (8463/10000) lo1541 hi1541=true := by decide +kernel
def bracket1541 : MeanBracket := meanBracketOfMoments (8463/10000) lo1541 hi1541 accepted1541
def lo1542b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨60,by decide⟩
def lo1542b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨61,by decide⟩
def lo1542 : CheckedMoment :=
  CheckedMoment.ofBessel lo1542b1 lo1542b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1542b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨1,by decide⟩
def hi1542b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨2,by decide⟩
def hi1542 : CheckedMoment :=
  CheckedMoment.ofBessel hi1542b1 hi1542b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1542 : meanBracketCheck (529/625) lo1542 hi1542=true := by decide +kernel
def bracket1542 : MeanBracket := meanBracketOfMoments (529/625) lo1542 hi1542 accepted1542
def lo1543b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨6,by decide⟩
def lo1543b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨7,by decide⟩
def lo1543 : CheckedMoment :=
  CheckedMoment.ofBessel lo1543b1 lo1543b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1543b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨11,by decide⟩
def hi1543b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨12,by decide⟩
def hi1543 : CheckedMoment :=
  CheckedMoment.ofBessel hi1543b1 hi1543b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1543 : meanBracketCheck (1693/2000) lo1543 hi1543=true := by decide +kernel
def bracket1543 : MeanBracket := meanBracketOfMoments (1693/2000) lo1543 hi1543 accepted1543
def lo1544b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨16,by decide⟩
def lo1544b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨17,by decide⟩
def lo1544 : CheckedMoment :=
  CheckedMoment.ofBessel lo1544b1 lo1544b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1544b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨21,by decide⟩
def hi1544b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨22,by decide⟩
def hi1544 : CheckedMoment :=
  CheckedMoment.ofBessel hi1544b1 hi1544b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1544 : meanBracketCheck (4233/5000) lo1544 hi1544=true := by decide +kernel
def bracket1544 : MeanBracket := meanBracketOfMoments (4233/5000) lo1544 hi1544 accepted1544
def lo1545b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨26,by decide⟩
def lo1545b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨27,by decide⟩
def lo1545 : CheckedMoment :=
  CheckedMoment.ofBessel lo1545b1 lo1545b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1545b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨31,by decide⟩
def hi1545b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨32,by decide⟩
def hi1545 : CheckedMoment :=
  CheckedMoment.ofBessel hi1545b1 hi1545b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1545 : meanBracketCheck (8467/10000) lo1545 hi1545=true := by decide +kernel
def bracket1545 : MeanBracket := meanBracketOfMoments (8467/10000) lo1545 hi1545 accepted1545
def lo1546b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨36,by decide⟩
def lo1546b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨37,by decide⟩
def lo1546 : CheckedMoment :=
  CheckedMoment.ofBessel lo1546b1 lo1546b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1546b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨41,by decide⟩
def hi1546b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨42,by decide⟩
def hi1546 : CheckedMoment :=
  CheckedMoment.ofBessel hi1546b1 hi1546b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1546 : meanBracketCheck (2117/2500) lo1546 hi1546=true := by decide +kernel
def bracket1546 : MeanBracket := meanBracketOfMoments (2117/2500) lo1546 hi1546 accepted1546
def lo1547b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨46,by decide⟩
def lo1547b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨47,by decide⟩
def lo1547 : CheckedMoment :=
  CheckedMoment.ofBessel lo1547b1 lo1547b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1547b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨51,by decide⟩
def hi1547b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨52,by decide⟩
def hi1547 : CheckedMoment :=
  CheckedMoment.ofBessel hi1547b1 hi1547b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1547 : meanBracketCheck (8469/10000) lo1547 hi1547=true := by decide +kernel
def bracket1547 : MeanBracket := meanBracketOfMoments (8469/10000) lo1547 hi1547 accepted1547
def lo1548b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨56,by decide⟩
def lo1548b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨57,by decide⟩
def lo1548 : CheckedMoment :=
  CheckedMoment.ofBessel lo1548b1 lo1548b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1548b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨61,by decide⟩
def hi1548b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨62,by decide⟩
def hi1548 : CheckedMoment :=
  CheckedMoment.ofBessel hi1548b1 hi1548b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1548 : meanBracketCheck (847/1000) lo1548 hi1548=true := by decide +kernel
def bracket1548 : MeanBracket := meanBracketOfMoments (847/1000) lo1548 hi1548 accepted1548
def lo1549b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨2,by decide⟩
def lo1549b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨3,by decide⟩
def lo1549 : CheckedMoment :=
  CheckedMoment.ofBessel lo1549b1 lo1549b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1549b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨7,by decide⟩
def hi1549b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨8,by decide⟩
def hi1549 : CheckedMoment :=
  CheckedMoment.ofBessel hi1549b1 hi1549b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1549 : meanBracketCheck (8471/10000) lo1549 hi1549=true := by decide +kernel
def bracket1549 : MeanBracket := meanBracketOfMoments (8471/10000) lo1549 hi1549 accepted1549
def lo1550b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨12,by decide⟩
def lo1550b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨13,by decide⟩
def lo1550 : CheckedMoment :=
  CheckedMoment.ofBessel lo1550b1 lo1550b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1550b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨17,by decide⟩
def hi1550b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨18,by decide⟩
def hi1550 : CheckedMoment :=
  CheckedMoment.ofBessel hi1550b1 hi1550b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1550 : meanBracketCheck (1059/1250) lo1550 hi1550=true := by decide +kernel
def bracket1550 : MeanBracket := meanBracketOfMoments (1059/1250) lo1550 hi1550 accepted1550
def lo1551b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨22,by decide⟩
def lo1551b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨23,by decide⟩
def lo1551 : CheckedMoment :=
  CheckedMoment.ofBessel lo1551b1 lo1551b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1551b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨27,by decide⟩
def hi1551b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨28,by decide⟩
def hi1551 : CheckedMoment :=
  CheckedMoment.ofBessel hi1551b1 hi1551b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1551 : meanBracketCheck (8473/10000) lo1551 hi1551=true := by decide +kernel
def bracket1551 : MeanBracket := meanBracketOfMoments (8473/10000) lo1551 hi1551 accepted1551
#print axioms bracket1536
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0096
