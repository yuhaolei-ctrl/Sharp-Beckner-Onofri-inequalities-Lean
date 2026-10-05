module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0255
public import BecknerOnofri.EntropyScalarCertificate.Bessel0256
public import BecknerOnofri.EntropyScalarCertificate.Bessel0257

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0102
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1632b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨0,by decide⟩
def lo1632b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨1,by decide⟩
def lo1632 : CheckedMoment :=
  CheckedMoment.ofBessel lo1632b1 lo1632b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1632b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨5,by decide⟩
def hi1632b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨6,by decide⟩
def hi1632 : CheckedMoment :=
  CheckedMoment.ofBessel hi1632b1 hi1632b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1632 : meanBracketCheck (4277/5000) lo1632 hi1632=true := by decide +kernel
def bracket1632 : MeanBracket := meanBracketOfMoments (4277/5000) lo1632 hi1632 accepted1632
def lo1633b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨10,by decide⟩
def lo1633b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨11,by decide⟩
def lo1633 : CheckedMoment :=
  CheckedMoment.ofBessel lo1633b1 lo1633b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1633b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨15,by decide⟩
def hi1633b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨16,by decide⟩
def hi1633 : CheckedMoment :=
  CheckedMoment.ofBessel hi1633b1 hi1633b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1633 : meanBracketCheck (1711/2000) lo1633 hi1633=true := by decide +kernel
def bracket1633 : MeanBracket := meanBracketOfMoments (1711/2000) lo1633 hi1633 accepted1633
def lo1634b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨20,by decide⟩
def lo1634b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨21,by decide⟩
def lo1634 : CheckedMoment :=
  CheckedMoment.ofBessel lo1634b1 lo1634b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1634b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨25,by decide⟩
def hi1634b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨26,by decide⟩
def hi1634 : CheckedMoment :=
  CheckedMoment.ofBessel hi1634b1 hi1634b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1634 : meanBracketCheck (2139/2500) lo1634 hi1634=true := by decide +kernel
def bracket1634 : MeanBracket := meanBracketOfMoments (2139/2500) lo1634 hi1634 accepted1634
def lo1635b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨30,by decide⟩
def lo1635b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨31,by decide⟩
def lo1635 : CheckedMoment :=
  CheckedMoment.ofBessel lo1635b1 lo1635b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1635b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨35,by decide⟩
def hi1635b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨36,by decide⟩
def hi1635 : CheckedMoment :=
  CheckedMoment.ofBessel hi1635b1 hi1635b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1635 : meanBracketCheck (8557/10000) lo1635 hi1635=true := by decide +kernel
def bracket1635 : MeanBracket := meanBracketOfMoments (8557/10000) lo1635 hi1635 accepted1635
def lo1636b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨40,by decide⟩
def lo1636b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨41,by decide⟩
def lo1636 : CheckedMoment :=
  CheckedMoment.ofBessel lo1636b1 lo1636b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1636b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨45,by decide⟩
def hi1636b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨46,by decide⟩
def hi1636 : CheckedMoment :=
  CheckedMoment.ofBessel hi1636b1 hi1636b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1636 : meanBracketCheck (4279/5000) lo1636 hi1636=true := by decide +kernel
def bracket1636 : MeanBracket := meanBracketOfMoments (4279/5000) lo1636 hi1636 accepted1636
def lo1637b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨50,by decide⟩
def lo1637b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨51,by decide⟩
def lo1637 : CheckedMoment :=
  CheckedMoment.ofBessel lo1637b1 lo1637b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1637b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨55,by decide⟩
def hi1637b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨56,by decide⟩
def hi1637 : CheckedMoment :=
  CheckedMoment.ofBessel hi1637b1 hi1637b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1637 : meanBracketCheck (8559/10000) lo1637 hi1637=true := by decide +kernel
def bracket1637 : MeanBracket := meanBracketOfMoments (8559/10000) lo1637 hi1637 accepted1637
def lo1638b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨60,by decide⟩
def lo1638b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨61,by decide⟩
def lo1638 : CheckedMoment :=
  CheckedMoment.ofBessel lo1638b1 lo1638b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1638b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨1,by decide⟩
def hi1638b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨2,by decide⟩
def hi1638 : CheckedMoment :=
  CheckedMoment.ofBessel hi1638b1 hi1638b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1638 : meanBracketCheck (107/125) lo1638 hi1638=true := by decide +kernel
def bracket1638 : MeanBracket := meanBracketOfMoments (107/125) lo1638 hi1638 accepted1638
def lo1639b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨6,by decide⟩
def lo1639b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨7,by decide⟩
def lo1639 : CheckedMoment :=
  CheckedMoment.ofBessel lo1639b1 lo1639b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1639b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨11,by decide⟩
def hi1639b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨12,by decide⟩
def hi1639 : CheckedMoment :=
  CheckedMoment.ofBessel hi1639b1 hi1639b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1639 : meanBracketCheck (8561/10000) lo1639 hi1639=true := by decide +kernel
def bracket1639 : MeanBracket := meanBracketOfMoments (8561/10000) lo1639 hi1639 accepted1639
def lo1640b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨16,by decide⟩
def lo1640b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨17,by decide⟩
def lo1640 : CheckedMoment :=
  CheckedMoment.ofBessel lo1640b1 lo1640b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1640b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨21,by decide⟩
def hi1640b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨22,by decide⟩
def hi1640 : CheckedMoment :=
  CheckedMoment.ofBessel hi1640b1 hi1640b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1640 : meanBracketCheck (4281/5000) lo1640 hi1640=true := by decide +kernel
def bracket1640 : MeanBracket := meanBracketOfMoments (4281/5000) lo1640 hi1640 accepted1640
def lo1641b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨26,by decide⟩
def lo1641b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨27,by decide⟩
def lo1641 : CheckedMoment :=
  CheckedMoment.ofBessel lo1641b1 lo1641b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1641b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨31,by decide⟩
def hi1641b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨32,by decide⟩
def hi1641 : CheckedMoment :=
  CheckedMoment.ofBessel hi1641b1 hi1641b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1641 : meanBracketCheck (8563/10000) lo1641 hi1641=true := by decide +kernel
def bracket1641 : MeanBracket := meanBracketOfMoments (8563/10000) lo1641 hi1641 accepted1641
def lo1642b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨36,by decide⟩
def lo1642b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨37,by decide⟩
def lo1642 : CheckedMoment :=
  CheckedMoment.ofBessel lo1642b1 lo1642b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1642b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨41,by decide⟩
def hi1642b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨42,by decide⟩
def hi1642 : CheckedMoment :=
  CheckedMoment.ofBessel hi1642b1 hi1642b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1642 : meanBracketCheck (2141/2500) lo1642 hi1642=true := by decide +kernel
def bracket1642 : MeanBracket := meanBracketOfMoments (2141/2500) lo1642 hi1642 accepted1642
def lo1643b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨46,by decide⟩
def lo1643b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨47,by decide⟩
def lo1643 : CheckedMoment :=
  CheckedMoment.ofBessel lo1643b1 lo1643b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1643b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨51,by decide⟩
def hi1643b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨52,by decide⟩
def hi1643 : CheckedMoment :=
  CheckedMoment.ofBessel hi1643b1 hi1643b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1643 : meanBracketCheck (1713/2000) lo1643 hi1643=true := by decide +kernel
def bracket1643 : MeanBracket := meanBracketOfMoments (1713/2000) lo1643 hi1643 accepted1643
def lo1644b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨56,by decide⟩
def lo1644b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨57,by decide⟩
def lo1644 : CheckedMoment :=
  CheckedMoment.ofBessel lo1644b1 lo1644b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1644b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨61,by decide⟩
def hi1644b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨62,by decide⟩
def hi1644 : CheckedMoment :=
  CheckedMoment.ofBessel hi1644b1 hi1644b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1644 : meanBracketCheck (4283/5000) lo1644 hi1644=true := by decide +kernel
def bracket1644 : MeanBracket := meanBracketOfMoments (4283/5000) lo1644 hi1644 accepted1644
def lo1645b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨2,by decide⟩
def lo1645b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨3,by decide⟩
def lo1645 : CheckedMoment :=
  CheckedMoment.ofBessel lo1645b1 lo1645b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1645b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨7,by decide⟩
def hi1645b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨8,by decide⟩
def hi1645 : CheckedMoment :=
  CheckedMoment.ofBessel hi1645b1 hi1645b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1645 : meanBracketCheck (8567/10000) lo1645 hi1645=true := by decide +kernel
def bracket1645 : MeanBracket := meanBracketOfMoments (8567/10000) lo1645 hi1645 accepted1645
def lo1646b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨12,by decide⟩
def lo1646b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨13,by decide⟩
def lo1646 : CheckedMoment :=
  CheckedMoment.ofBessel lo1646b1 lo1646b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1646b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨17,by decide⟩
def hi1646b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨18,by decide⟩
def hi1646 : CheckedMoment :=
  CheckedMoment.ofBessel hi1646b1 hi1646b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1646 : meanBracketCheck (1071/1250) lo1646 hi1646=true := by decide +kernel
def bracket1646 : MeanBracket := meanBracketOfMoments (1071/1250) lo1646 hi1646 accepted1646
def lo1647b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨22,by decide⟩
def lo1647b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨23,by decide⟩
def lo1647 : CheckedMoment :=
  CheckedMoment.ofBessel lo1647b1 lo1647b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1647b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨27,by decide⟩
def hi1647b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨28,by decide⟩
def hi1647 : CheckedMoment :=
  CheckedMoment.ofBessel hi1647b1 hi1647b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1647 : meanBracketCheck (8569/10000) lo1647 hi1647=true := by decide +kernel
def bracket1647 : MeanBracket := meanBracketOfMoments (8569/10000) lo1647 hi1647 accepted1647
#print axioms bracket1632
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0102
