import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0250
import BecknerOnofri.EntropyScalarCertificate.Bessel0251
import BecknerOnofri.EntropyScalarCertificate.Bessel0252
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0100
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1600b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨0,by decide⟩
def lo1600b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨1,by decide⟩
def lo1600 : CheckedMoment :=
  CheckedMoment.ofBessel lo1600b1 lo1600b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1600b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨5,by decide⟩
def hi1600b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨6,by decide⟩
def hi1600 : CheckedMoment :=
  CheckedMoment.ofBessel hi1600b1 hi1600b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1600 : meanBracketCheck (4261/5000) lo1600 hi1600=true := by decide +kernel
def bracket1600 : MeanBracket := meanBracketOfMoments (4261/5000) lo1600 hi1600 accepted1600
def lo1601b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨10,by decide⟩
def lo1601b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨11,by decide⟩
def lo1601 : CheckedMoment :=
  CheckedMoment.ofBessel lo1601b1 lo1601b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1601b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨15,by decide⟩
def hi1601b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨16,by decide⟩
def hi1601 : CheckedMoment :=
  CheckedMoment.ofBessel hi1601b1 hi1601b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1601 : meanBracketCheck (8523/10000) lo1601 hi1601=true := by decide +kernel
def bracket1601 : MeanBracket := meanBracketOfMoments (8523/10000) lo1601 hi1601 accepted1601
def lo1602b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨20,by decide⟩
def lo1602b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨21,by decide⟩
def lo1602 : CheckedMoment :=
  CheckedMoment.ofBessel lo1602b1 lo1602b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1602b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨25,by decide⟩
def hi1602b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨26,by decide⟩
def hi1602 : CheckedMoment :=
  CheckedMoment.ofBessel hi1602b1 hi1602b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1602 : meanBracketCheck (2131/2500) lo1602 hi1602=true := by decide +kernel
def bracket1602 : MeanBracket := meanBracketOfMoments (2131/2500) lo1602 hi1602 accepted1602
def lo1603b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨30,by decide⟩
def lo1603b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨31,by decide⟩
def lo1603 : CheckedMoment :=
  CheckedMoment.ofBessel lo1603b1 lo1603b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1603b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨35,by decide⟩
def hi1603b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨36,by decide⟩
def hi1603 : CheckedMoment :=
  CheckedMoment.ofBessel hi1603b1 hi1603b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1603 : meanBracketCheck (341/400) lo1603 hi1603=true := by decide +kernel
def bracket1603 : MeanBracket := meanBracketOfMoments (341/400) lo1603 hi1603 accepted1603
def lo1604b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨40,by decide⟩
def lo1604b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨41,by decide⟩
def lo1604 : CheckedMoment :=
  CheckedMoment.ofBessel lo1604b1 lo1604b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1604b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨45,by decide⟩
def hi1604b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨46,by decide⟩
def hi1604 : CheckedMoment :=
  CheckedMoment.ofBessel hi1604b1 hi1604b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1604 : meanBracketCheck (4263/5000) lo1604 hi1604=true := by decide +kernel
def bracket1604 : MeanBracket := meanBracketOfMoments (4263/5000) lo1604 hi1604 accepted1604
def lo1605b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨50,by decide⟩
def lo1605b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨51,by decide⟩
def lo1605 : CheckedMoment :=
  CheckedMoment.ofBessel lo1605b1 lo1605b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1605b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨55,by decide⟩
def hi1605b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨56,by decide⟩
def hi1605 : CheckedMoment :=
  CheckedMoment.ofBessel hi1605b1 hi1605b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1605 : meanBracketCheck (8527/10000) lo1605 hi1605=true := by decide +kernel
def bracket1605 : MeanBracket := meanBracketOfMoments (8527/10000) lo1605 hi1605 accepted1605
def lo1606b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨60,by decide⟩
def lo1606b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨61,by decide⟩
def lo1606 : CheckedMoment :=
  CheckedMoment.ofBessel lo1606b1 lo1606b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1606b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨1,by decide⟩
def hi1606b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨2,by decide⟩
def hi1606 : CheckedMoment :=
  CheckedMoment.ofBessel hi1606b1 hi1606b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1606 : meanBracketCheck (533/625) lo1606 hi1606=true := by decide +kernel
def bracket1606 : MeanBracket := meanBracketOfMoments (533/625) lo1606 hi1606 accepted1606
def lo1607b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨6,by decide⟩
def lo1607b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨7,by decide⟩
def lo1607 : CheckedMoment :=
  CheckedMoment.ofBessel lo1607b1 lo1607b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1607b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨11,by decide⟩
def hi1607b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨12,by decide⟩
def hi1607 : CheckedMoment :=
  CheckedMoment.ofBessel hi1607b1 hi1607b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1607 : meanBracketCheck (8529/10000) lo1607 hi1607=true := by decide +kernel
def bracket1607 : MeanBracket := meanBracketOfMoments (8529/10000) lo1607 hi1607 accepted1607
def lo1608b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨16,by decide⟩
def lo1608b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨17,by decide⟩
def lo1608 : CheckedMoment :=
  CheckedMoment.ofBessel lo1608b1 lo1608b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1608b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨21,by decide⟩
def hi1608b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨22,by decide⟩
def hi1608 : CheckedMoment :=
  CheckedMoment.ofBessel hi1608b1 hi1608b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1608 : meanBracketCheck (853/1000) lo1608 hi1608=true := by decide +kernel
def bracket1608 : MeanBracket := meanBracketOfMoments (853/1000) lo1608 hi1608 accepted1608
def lo1609b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨26,by decide⟩
def lo1609b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨27,by decide⟩
def lo1609 : CheckedMoment :=
  CheckedMoment.ofBessel lo1609b1 lo1609b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1609b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨31,by decide⟩
def hi1609b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨32,by decide⟩
def hi1609 : CheckedMoment :=
  CheckedMoment.ofBessel hi1609b1 hi1609b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1609 : meanBracketCheck (8531/10000) lo1609 hi1609=true := by decide +kernel
def bracket1609 : MeanBracket := meanBracketOfMoments (8531/10000) lo1609 hi1609 accepted1609
def lo1610b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨36,by decide⟩
def lo1610b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨37,by decide⟩
def lo1610 : CheckedMoment :=
  CheckedMoment.ofBessel lo1610b1 lo1610b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1610b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨41,by decide⟩
def hi1610b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨42,by decide⟩
def hi1610 : CheckedMoment :=
  CheckedMoment.ofBessel hi1610b1 hi1610b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1610 : meanBracketCheck (2133/2500) lo1610 hi1610=true := by decide +kernel
def bracket1610 : MeanBracket := meanBracketOfMoments (2133/2500) lo1610 hi1610 accepted1610
def lo1611b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨46,by decide⟩
def lo1611b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨47,by decide⟩
def lo1611 : CheckedMoment :=
  CheckedMoment.ofBessel lo1611b1 lo1611b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1611b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨51,by decide⟩
def hi1611b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨52,by decide⟩
def hi1611 : CheckedMoment :=
  CheckedMoment.ofBessel hi1611b1 hi1611b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1611 : meanBracketCheck (8533/10000) lo1611 hi1611=true := by decide +kernel
def bracket1611 : MeanBracket := meanBracketOfMoments (8533/10000) lo1611 hi1611 accepted1611
def lo1612b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨56,by decide⟩
def lo1612b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨57,by decide⟩
def lo1612 : CheckedMoment :=
  CheckedMoment.ofBessel lo1612b1 lo1612b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1612b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨61,by decide⟩
def hi1612b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0251.rows BesselBatch0251.accepted ⟨62,by decide⟩
def hi1612 : CheckedMoment :=
  CheckedMoment.ofBessel hi1612b1 hi1612b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1612 : meanBracketCheck (4267/5000) lo1612 hi1612=true := by decide +kernel
def bracket1612 : MeanBracket := meanBracketOfMoments (4267/5000) lo1612 hi1612 accepted1612
def lo1613b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨2,by decide⟩
def lo1613b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨3,by decide⟩
def lo1613 : CheckedMoment :=
  CheckedMoment.ofBessel lo1613b1 lo1613b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1613b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨7,by decide⟩
def hi1613b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨8,by decide⟩
def hi1613 : CheckedMoment :=
  CheckedMoment.ofBessel hi1613b1 hi1613b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1613 : meanBracketCheck (1707/2000) lo1613 hi1613=true := by decide +kernel
def bracket1613 : MeanBracket := meanBracketOfMoments (1707/2000) lo1613 hi1613 accepted1613
def lo1614b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨12,by decide⟩
def lo1614b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨13,by decide⟩
def lo1614 : CheckedMoment :=
  CheckedMoment.ofBessel lo1614b1 lo1614b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1614b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨17,by decide⟩
def hi1614b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨18,by decide⟩
def hi1614 : CheckedMoment :=
  CheckedMoment.ofBessel hi1614b1 hi1614b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1614 : meanBracketCheck (1067/1250) lo1614 hi1614=true := by decide +kernel
def bracket1614 : MeanBracket := meanBracketOfMoments (1067/1250) lo1614 hi1614 accepted1614
def lo1615b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨22,by decide⟩
def lo1615b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨23,by decide⟩
def lo1615 : CheckedMoment :=
  CheckedMoment.ofBessel lo1615b1 lo1615b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1615b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨27,by decide⟩
def hi1615b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨28,by decide⟩
def hi1615 : CheckedMoment :=
  CheckedMoment.ofBessel hi1615b1 hi1615b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1615 : meanBracketCheck (8537/10000) lo1615 hi1615=true := by decide +kernel
def bracket1615 : MeanBracket := meanBracketOfMoments (8537/10000) lo1615 hi1615 accepted1615
#print axioms bracket1600
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0100
