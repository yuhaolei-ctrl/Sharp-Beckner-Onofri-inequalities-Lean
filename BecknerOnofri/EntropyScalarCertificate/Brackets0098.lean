import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0245
import BecknerOnofri.EntropyScalarCertificate.Bessel0246
import BecknerOnofri.EntropyScalarCertificate.Bessel0247
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0098
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1568b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨0,by decide⟩
def lo1568b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨1,by decide⟩
def lo1568 : CheckedMoment :=
  CheckedMoment.ofBessel lo1568b1 lo1568b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1568b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨5,by decide⟩
def hi1568b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨6,by decide⟩
def hi1568 : CheckedMoment :=
  CheckedMoment.ofBessel hi1568b1 hi1568b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1568 : meanBracketCheck (849/1000) lo1568 hi1568=true := by decide +kernel
def bracket1568 : MeanBracket := meanBracketOfMoments (849/1000) lo1568 hi1568 accepted1568
def lo1569b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨10,by decide⟩
def lo1569b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨11,by decide⟩
def lo1569 : CheckedMoment :=
  CheckedMoment.ofBessel lo1569b1 lo1569b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1569b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨15,by decide⟩
def hi1569b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨16,by decide⟩
def hi1569 : CheckedMoment :=
  CheckedMoment.ofBessel hi1569b1 hi1569b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1569 : meanBracketCheck (8491/10000) lo1569 hi1569=true := by decide +kernel
def bracket1569 : MeanBracket := meanBracketOfMoments (8491/10000) lo1569 hi1569 accepted1569
def lo1570b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨20,by decide⟩
def lo1570b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨21,by decide⟩
def lo1570 : CheckedMoment :=
  CheckedMoment.ofBessel lo1570b1 lo1570b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1570b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨25,by decide⟩
def hi1570b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨26,by decide⟩
def hi1570 : CheckedMoment :=
  CheckedMoment.ofBessel hi1570b1 hi1570b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1570 : meanBracketCheck (2123/2500) lo1570 hi1570=true := by decide +kernel
def bracket1570 : MeanBracket := meanBracketOfMoments (2123/2500) lo1570 hi1570 accepted1570
def lo1571b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨30,by decide⟩
def lo1571b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨31,by decide⟩
def lo1571 : CheckedMoment :=
  CheckedMoment.ofBessel lo1571b1 lo1571b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1571b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨35,by decide⟩
def hi1571b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨36,by decide⟩
def hi1571 : CheckedMoment :=
  CheckedMoment.ofBessel hi1571b1 hi1571b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1571 : meanBracketCheck (8493/10000) lo1571 hi1571=true := by decide +kernel
def bracket1571 : MeanBracket := meanBracketOfMoments (8493/10000) lo1571 hi1571 accepted1571
def lo1572b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨40,by decide⟩
def lo1572b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨41,by decide⟩
def lo1572 : CheckedMoment :=
  CheckedMoment.ofBessel lo1572b1 lo1572b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1572b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨45,by decide⟩
def hi1572b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨46,by decide⟩
def hi1572 : CheckedMoment :=
  CheckedMoment.ofBessel hi1572b1 hi1572b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1572 : meanBracketCheck (4247/5000) lo1572 hi1572=true := by decide +kernel
def bracket1572 : MeanBracket := meanBracketOfMoments (4247/5000) lo1572 hi1572 accepted1572
def lo1573b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨50,by decide⟩
def lo1573b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨51,by decide⟩
def lo1573 : CheckedMoment :=
  CheckedMoment.ofBessel lo1573b1 lo1573b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1573b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨55,by decide⟩
def hi1573b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨56,by decide⟩
def hi1573 : CheckedMoment :=
  CheckedMoment.ofBessel hi1573b1 hi1573b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1573 : meanBracketCheck (1699/2000) lo1573 hi1573=true := by decide +kernel
def bracket1573 : MeanBracket := meanBracketOfMoments (1699/2000) lo1573 hi1573 accepted1573
def lo1574b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨60,by decide⟩
def lo1574b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨61,by decide⟩
def lo1574 : CheckedMoment :=
  CheckedMoment.ofBessel lo1574b1 lo1574b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1574b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨1,by decide⟩
def hi1574b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨2,by decide⟩
def hi1574 : CheckedMoment :=
  CheckedMoment.ofBessel hi1574b1 hi1574b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1574 : meanBracketCheck (531/625) lo1574 hi1574=true := by decide +kernel
def bracket1574 : MeanBracket := meanBracketOfMoments (531/625) lo1574 hi1574 accepted1574
def lo1575b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨6,by decide⟩
def lo1575b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨7,by decide⟩
def lo1575 : CheckedMoment :=
  CheckedMoment.ofBessel lo1575b1 lo1575b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1575b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨11,by decide⟩
def hi1575b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨12,by decide⟩
def hi1575 : CheckedMoment :=
  CheckedMoment.ofBessel hi1575b1 hi1575b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1575 : meanBracketCheck (8497/10000) lo1575 hi1575=true := by decide +kernel
def bracket1575 : MeanBracket := meanBracketOfMoments (8497/10000) lo1575 hi1575 accepted1575
def lo1576b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨16,by decide⟩
def lo1576b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨17,by decide⟩
def lo1576 : CheckedMoment :=
  CheckedMoment.ofBessel lo1576b1 lo1576b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1576b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨21,by decide⟩
def hi1576b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨22,by decide⟩
def hi1576 : CheckedMoment :=
  CheckedMoment.ofBessel hi1576b1 hi1576b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1576 : meanBracketCheck (4249/5000) lo1576 hi1576=true := by decide +kernel
def bracket1576 : MeanBracket := meanBracketOfMoments (4249/5000) lo1576 hi1576 accepted1576
def lo1577b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨26,by decide⟩
def lo1577b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨27,by decide⟩
def lo1577 : CheckedMoment :=
  CheckedMoment.ofBessel lo1577b1 lo1577b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1577b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨31,by decide⟩
def hi1577b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨32,by decide⟩
def hi1577 : CheckedMoment :=
  CheckedMoment.ofBessel hi1577b1 hi1577b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1577 : meanBracketCheck (8499/10000) lo1577 hi1577=true := by decide +kernel
def bracket1577 : MeanBracket := meanBracketOfMoments (8499/10000) lo1577 hi1577 accepted1577
def lo1578b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨36,by decide⟩
def lo1578b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨37,by decide⟩
def lo1578 : CheckedMoment :=
  CheckedMoment.ofBessel lo1578b1 lo1578b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1578b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨41,by decide⟩
def hi1578b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨42,by decide⟩
def hi1578 : CheckedMoment :=
  CheckedMoment.ofBessel hi1578b1 hi1578b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1578 : meanBracketCheck (17/20) lo1578 hi1578=true := by decide +kernel
def bracket1578 : MeanBracket := meanBracketOfMoments (17/20) lo1578 hi1578 accepted1578
def lo1579b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨46,by decide⟩
def lo1579b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨47,by decide⟩
def lo1579 : CheckedMoment :=
  CheckedMoment.ofBessel lo1579b1 lo1579b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1579b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨51,by decide⟩
def hi1579b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨52,by decide⟩
def hi1579 : CheckedMoment :=
  CheckedMoment.ofBessel hi1579b1 hi1579b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1579 : meanBracketCheck (8501/10000) lo1579 hi1579=true := by decide +kernel
def bracket1579 : MeanBracket := meanBracketOfMoments (8501/10000) lo1579 hi1579 accepted1579
def lo1580b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨56,by decide⟩
def lo1580b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨57,by decide⟩
def lo1580 : CheckedMoment :=
  CheckedMoment.ofBessel lo1580b1 lo1580b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1580b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨61,by decide⟩
def hi1580b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨62,by decide⟩
def hi1580 : CheckedMoment :=
  CheckedMoment.ofBessel hi1580b1 hi1580b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1580 : meanBracketCheck (4251/5000) lo1580 hi1580=true := by decide +kernel
def bracket1580 : MeanBracket := meanBracketOfMoments (4251/5000) lo1580 hi1580 accepted1580
def lo1581b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨2,by decide⟩
def lo1581b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨3,by decide⟩
def lo1581 : CheckedMoment :=
  CheckedMoment.ofBessel lo1581b1 lo1581b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1581b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨7,by decide⟩
def hi1581b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨8,by decide⟩
def hi1581 : CheckedMoment :=
  CheckedMoment.ofBessel hi1581b1 hi1581b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1581 : meanBracketCheck (8503/10000) lo1581 hi1581=true := by decide +kernel
def bracket1581 : MeanBracket := meanBracketOfMoments (8503/10000) lo1581 hi1581 accepted1581
def lo1582b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨12,by decide⟩
def lo1582b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨13,by decide⟩
def lo1582 : CheckedMoment :=
  CheckedMoment.ofBessel lo1582b1 lo1582b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1582b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨17,by decide⟩
def hi1582b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨18,by decide⟩
def hi1582 : CheckedMoment :=
  CheckedMoment.ofBessel hi1582b1 hi1582b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1582 : meanBracketCheck (1063/1250) lo1582 hi1582=true := by decide +kernel
def bracket1582 : MeanBracket := meanBracketOfMoments (1063/1250) lo1582 hi1582 accepted1582
def lo1583b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨22,by decide⟩
def lo1583b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨23,by decide⟩
def lo1583 : CheckedMoment :=
  CheckedMoment.ofBessel lo1583b1 lo1583b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1583b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨27,by decide⟩
def hi1583b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨28,by decide⟩
def hi1583 : CheckedMoment :=
  CheckedMoment.ofBessel hi1583b1 hi1583b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1583 : meanBracketCheck (1701/2000) lo1583 hi1583=true := by decide +kernel
def bracket1583 : MeanBracket := meanBracketOfMoments (1701/2000) lo1583 hi1583 accepted1583
#print axioms bracket1568
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0098
