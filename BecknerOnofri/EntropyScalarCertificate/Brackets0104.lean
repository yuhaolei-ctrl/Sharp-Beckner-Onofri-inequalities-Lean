module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0260
public import BecknerOnofri.EntropyScalarCertificate.Bessel0261
public import BecknerOnofri.EntropyScalarCertificate.Bessel0262

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0104
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1664b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨0,by decide⟩
def lo1664b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨1,by decide⟩
def lo1664 : CheckedMoment :=
  CheckedMoment.ofBessel lo1664b1 lo1664b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1664b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨5,by decide⟩
def hi1664b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨6,by decide⟩
def hi1664 : CheckedMoment :=
  CheckedMoment.ofBessel hi1664b1 hi1664b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1664 : meanBracketCheck (4293/5000) lo1664 hi1664=true := by decide +kernel
def bracket1664 : MeanBracket := meanBracketOfMoments (4293/5000) lo1664 hi1664 accepted1664
def lo1665b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨10,by decide⟩
def lo1665b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨11,by decide⟩
def lo1665 : CheckedMoment :=
  CheckedMoment.ofBessel lo1665b1 lo1665b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1665b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨15,by decide⟩
def hi1665b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨16,by decide⟩
def hi1665 : CheckedMoment :=
  CheckedMoment.ofBessel hi1665b1 hi1665b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1665 : meanBracketCheck (8587/10000) lo1665 hi1665=true := by decide +kernel
def bracket1665 : MeanBracket := meanBracketOfMoments (8587/10000) lo1665 hi1665 accepted1665
def lo1666b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨20,by decide⟩
def lo1666b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨21,by decide⟩
def lo1666 : CheckedMoment :=
  CheckedMoment.ofBessel lo1666b1 lo1666b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1666b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨25,by decide⟩
def hi1666b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨26,by decide⟩
def hi1666 : CheckedMoment :=
  CheckedMoment.ofBessel hi1666b1 hi1666b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1666 : meanBracketCheck (2147/2500) lo1666 hi1666=true := by decide +kernel
def bracket1666 : MeanBracket := meanBracketOfMoments (2147/2500) lo1666 hi1666 accepted1666
def lo1667b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨30,by decide⟩
def lo1667b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨31,by decide⟩
def lo1667 : CheckedMoment :=
  CheckedMoment.ofBessel lo1667b1 lo1667b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1667b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨35,by decide⟩
def hi1667b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨36,by decide⟩
def hi1667 : CheckedMoment :=
  CheckedMoment.ofBessel hi1667b1 hi1667b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1667 : meanBracketCheck (8589/10000) lo1667 hi1667=true := by decide +kernel
def bracket1667 : MeanBracket := meanBracketOfMoments (8589/10000) lo1667 hi1667 accepted1667
def lo1668b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨40,by decide⟩
def lo1668b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨41,by decide⟩
def lo1668 : CheckedMoment :=
  CheckedMoment.ofBessel lo1668b1 lo1668b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1668b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨45,by decide⟩
def hi1668b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨46,by decide⟩
def hi1668 : CheckedMoment :=
  CheckedMoment.ofBessel hi1668b1 hi1668b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1668 : meanBracketCheck (859/1000) lo1668 hi1668=true := by decide +kernel
def bracket1668 : MeanBracket := meanBracketOfMoments (859/1000) lo1668 hi1668 accepted1668
def lo1669b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨50,by decide⟩
def lo1669b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨51,by decide⟩
def lo1669 : CheckedMoment :=
  CheckedMoment.ofBessel lo1669b1 lo1669b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1669b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨55,by decide⟩
def hi1669b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨56,by decide⟩
def hi1669 : CheckedMoment :=
  CheckedMoment.ofBessel hi1669b1 hi1669b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1669 : meanBracketCheck (8591/10000) lo1669 hi1669=true := by decide +kernel
def bracket1669 : MeanBracket := meanBracketOfMoments (8591/10000) lo1669 hi1669 accepted1669
def lo1670b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨60,by decide⟩
def lo1670b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨61,by decide⟩
def lo1670 : CheckedMoment :=
  CheckedMoment.ofBessel lo1670b1 lo1670b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1670b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨1,by decide⟩
def hi1670b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨2,by decide⟩
def hi1670 : CheckedMoment :=
  CheckedMoment.ofBessel hi1670b1 hi1670b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1670 : meanBracketCheck (537/625) lo1670 hi1670=true := by decide +kernel
def bracket1670 : MeanBracket := meanBracketOfMoments (537/625) lo1670 hi1670 accepted1670
def lo1671b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨6,by decide⟩
def lo1671b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨7,by decide⟩
def lo1671 : CheckedMoment :=
  CheckedMoment.ofBessel lo1671b1 lo1671b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1671b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨11,by decide⟩
def hi1671b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨12,by decide⟩
def hi1671 : CheckedMoment :=
  CheckedMoment.ofBessel hi1671b1 hi1671b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1671 : meanBracketCheck (8593/10000) lo1671 hi1671=true := by decide +kernel
def bracket1671 : MeanBracket := meanBracketOfMoments (8593/10000) lo1671 hi1671 accepted1671
def lo1672b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨16,by decide⟩
def lo1672b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨17,by decide⟩
def lo1672 : CheckedMoment :=
  CheckedMoment.ofBessel lo1672b1 lo1672b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1672b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨21,by decide⟩
def hi1672b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨22,by decide⟩
def hi1672 : CheckedMoment :=
  CheckedMoment.ofBessel hi1672b1 hi1672b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1672 : meanBracketCheck (4297/5000) lo1672 hi1672=true := by decide +kernel
def bracket1672 : MeanBracket := meanBracketOfMoments (4297/5000) lo1672 hi1672 accepted1672
def lo1673b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨26,by decide⟩
def lo1673b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨27,by decide⟩
def lo1673 : CheckedMoment :=
  CheckedMoment.ofBessel lo1673b1 lo1673b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1673b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨31,by decide⟩
def hi1673b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨32,by decide⟩
def hi1673 : CheckedMoment :=
  CheckedMoment.ofBessel hi1673b1 hi1673b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1673 : meanBracketCheck (1719/2000) lo1673 hi1673=true := by decide +kernel
def bracket1673 : MeanBracket := meanBracketOfMoments (1719/2000) lo1673 hi1673 accepted1673
def lo1674b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨36,by decide⟩
def lo1674b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨37,by decide⟩
def lo1674 : CheckedMoment :=
  CheckedMoment.ofBessel lo1674b1 lo1674b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1674b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨41,by decide⟩
def hi1674b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨42,by decide⟩
def hi1674 : CheckedMoment :=
  CheckedMoment.ofBessel hi1674b1 hi1674b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1674 : meanBracketCheck (2149/2500) lo1674 hi1674=true := by decide +kernel
def bracket1674 : MeanBracket := meanBracketOfMoments (2149/2500) lo1674 hi1674 accepted1674
def lo1675b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨46,by decide⟩
def lo1675b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨47,by decide⟩
def lo1675 : CheckedMoment :=
  CheckedMoment.ofBessel lo1675b1 lo1675b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1675b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨51,by decide⟩
def hi1675b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨52,by decide⟩
def hi1675 : CheckedMoment :=
  CheckedMoment.ofBessel hi1675b1 hi1675b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1675 : meanBracketCheck (8597/10000) lo1675 hi1675=true := by decide +kernel
def bracket1675 : MeanBracket := meanBracketOfMoments (8597/10000) lo1675 hi1675 accepted1675
def lo1676b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨56,by decide⟩
def lo1676b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨57,by decide⟩
def lo1676 : CheckedMoment :=
  CheckedMoment.ofBessel lo1676b1 lo1676b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1676b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨61,by decide⟩
def hi1676b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨62,by decide⟩
def hi1676 : CheckedMoment :=
  CheckedMoment.ofBessel hi1676b1 hi1676b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1676 : meanBracketCheck (4299/5000) lo1676 hi1676=true := by decide +kernel
def bracket1676 : MeanBracket := meanBracketOfMoments (4299/5000) lo1676 hi1676 accepted1676
def lo1677b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨2,by decide⟩
def lo1677b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨3,by decide⟩
def lo1677 : CheckedMoment :=
  CheckedMoment.ofBessel lo1677b1 lo1677b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1677b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨7,by decide⟩
def hi1677b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨8,by decide⟩
def hi1677 : CheckedMoment :=
  CheckedMoment.ofBessel hi1677b1 hi1677b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1677 : meanBracketCheck (8599/10000) lo1677 hi1677=true := by decide +kernel
def bracket1677 : MeanBracket := meanBracketOfMoments (8599/10000) lo1677 hi1677 accepted1677
def lo1678b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨12,by decide⟩
def lo1678b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨13,by decide⟩
def lo1678 : CheckedMoment :=
  CheckedMoment.ofBessel lo1678b1 lo1678b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1678b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨17,by decide⟩
def hi1678b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨18,by decide⟩
def hi1678 : CheckedMoment :=
  CheckedMoment.ofBessel hi1678b1 hi1678b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1678 : meanBracketCheck (43/50) lo1678 hi1678=true := by decide +kernel
def bracket1678 : MeanBracket := meanBracketOfMoments (43/50) lo1678 hi1678 accepted1678
def lo1679b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨22,by decide⟩
def lo1679b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨23,by decide⟩
def lo1679 : CheckedMoment :=
  CheckedMoment.ofBessel lo1679b1 lo1679b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1679b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨27,by decide⟩
def hi1679b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨28,by decide⟩
def hi1679 : CheckedMoment :=
  CheckedMoment.ofBessel hi1679b1 hi1679b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1679 : meanBracketCheck (8601/10000) lo1679 hi1679=true := by decide +kernel
def bracket1679 : MeanBracket := meanBracketOfMoments (8601/10000) lo1679 hi1679 accepted1679
#print axioms bracket1664
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0104
