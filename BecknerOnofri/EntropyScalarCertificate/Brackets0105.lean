module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0262
public import BecknerOnofri.EntropyScalarCertificate.Bessel0263
public import BecknerOnofri.EntropyScalarCertificate.Bessel0264

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0105
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1680b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨32,by decide⟩
def lo1680b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨33,by decide⟩
def lo1680 : CheckedMoment :=
  CheckedMoment.ofBessel lo1680b1 lo1680b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1680b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨37,by decide⟩
def hi1680b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨38,by decide⟩
def hi1680 : CheckedMoment :=
  CheckedMoment.ofBessel hi1680b1 hi1680b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1680 : meanBracketCheck (4301/5000) lo1680 hi1680=true := by decide +kernel
def bracket1680 : MeanBracket := meanBracketOfMoments (4301/5000) lo1680 hi1680 accepted1680
def lo1681b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨42,by decide⟩
def lo1681b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨43,by decide⟩
def lo1681 : CheckedMoment :=
  CheckedMoment.ofBessel lo1681b1 lo1681b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1681b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨47,by decide⟩
def hi1681b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨48,by decide⟩
def hi1681 : CheckedMoment :=
  CheckedMoment.ofBessel hi1681b1 hi1681b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1681 : meanBracketCheck (8603/10000) lo1681 hi1681=true := by decide +kernel
def bracket1681 : MeanBracket := meanBracketOfMoments (8603/10000) lo1681 hi1681 accepted1681
def lo1682b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨52,by decide⟩
def lo1682b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨53,by decide⟩
def lo1682 : CheckedMoment :=
  CheckedMoment.ofBessel lo1682b1 lo1682b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1682b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨57,by decide⟩
def hi1682b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨58,by decide⟩
def hi1682 : CheckedMoment :=
  CheckedMoment.ofBessel hi1682b1 hi1682b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1682 : meanBracketCheck (2151/2500) lo1682 hi1682=true := by decide +kernel
def bracket1682 : MeanBracket := meanBracketOfMoments (2151/2500) lo1682 hi1682 accepted1682
def lo1683b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨62,by decide⟩
def lo1683b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨63,by decide⟩
def lo1683 : CheckedMoment :=
  CheckedMoment.ofBessel lo1683b1 lo1683b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1683b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨3,by decide⟩
def hi1683b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨4,by decide⟩
def hi1683 : CheckedMoment :=
  CheckedMoment.ofBessel hi1683b1 hi1683b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1683 : meanBracketCheck (1721/2000) lo1683 hi1683=true := by decide +kernel
def bracket1683 : MeanBracket := meanBracketOfMoments (1721/2000) lo1683 hi1683 accepted1683
def lo1684b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨8,by decide⟩
def lo1684b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨9,by decide⟩
def lo1684 : CheckedMoment :=
  CheckedMoment.ofBessel lo1684b1 lo1684b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1684b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨13,by decide⟩
def hi1684b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨14,by decide⟩
def hi1684 : CheckedMoment :=
  CheckedMoment.ofBessel hi1684b1 hi1684b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1684 : meanBracketCheck (4303/5000) lo1684 hi1684=true := by decide +kernel
def bracket1684 : MeanBracket := meanBracketOfMoments (4303/5000) lo1684 hi1684 accepted1684
def lo1685b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨18,by decide⟩
def lo1685b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨19,by decide⟩
def lo1685 : CheckedMoment :=
  CheckedMoment.ofBessel lo1685b1 lo1685b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1685b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨23,by decide⟩
def hi1685b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨24,by decide⟩
def hi1685 : CheckedMoment :=
  CheckedMoment.ofBessel hi1685b1 hi1685b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1685 : meanBracketCheck (8607/10000) lo1685 hi1685=true := by decide +kernel
def bracket1685 : MeanBracket := meanBracketOfMoments (8607/10000) lo1685 hi1685 accepted1685
def lo1686b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨28,by decide⟩
def lo1686b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨29,by decide⟩
def lo1686 : CheckedMoment :=
  CheckedMoment.ofBessel lo1686b1 lo1686b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1686b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨33,by decide⟩
def hi1686b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨34,by decide⟩
def hi1686 : CheckedMoment :=
  CheckedMoment.ofBessel hi1686b1 hi1686b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1686 : meanBracketCheck (538/625) lo1686 hi1686=true := by decide +kernel
def bracket1686 : MeanBracket := meanBracketOfMoments (538/625) lo1686 hi1686 accepted1686
def lo1687b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨38,by decide⟩
def lo1687b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨39,by decide⟩
def lo1687 : CheckedMoment :=
  CheckedMoment.ofBessel lo1687b1 lo1687b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1687b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨43,by decide⟩
def hi1687b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨44,by decide⟩
def hi1687 : CheckedMoment :=
  CheckedMoment.ofBessel hi1687b1 hi1687b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1687 : meanBracketCheck (8609/10000) lo1687 hi1687=true := by decide +kernel
def bracket1687 : MeanBracket := meanBracketOfMoments (8609/10000) lo1687 hi1687 accepted1687
def lo1688b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨48,by decide⟩
def lo1688b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨49,by decide⟩
def lo1688 : CheckedMoment :=
  CheckedMoment.ofBessel lo1688b1 lo1688b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1688b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨53,by decide⟩
def hi1688b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨54,by decide⟩
def hi1688 : CheckedMoment :=
  CheckedMoment.ofBessel hi1688b1 hi1688b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1688 : meanBracketCheck (861/1000) lo1688 hi1688=true := by decide +kernel
def bracket1688 : MeanBracket := meanBracketOfMoments (861/1000) lo1688 hi1688 accepted1688
def lo1689b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨58,by decide⟩
def lo1689b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨59,by decide⟩
def lo1689 : CheckedMoment :=
  CheckedMoment.ofBessel lo1689b1 lo1689b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1689b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨63,by decide⟩
def hi1689b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨0,by decide⟩
def hi1689 : CheckedMoment :=
  CheckedMoment.ofBessel hi1689b1 hi1689b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1689 : meanBracketCheck (8611/10000) lo1689 hi1689=true := by decide +kernel
def bracket1689 : MeanBracket := meanBracketOfMoments (8611/10000) lo1689 hi1689 accepted1689
def lo1690b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨4,by decide⟩
def lo1690b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨5,by decide⟩
def lo1690 : CheckedMoment :=
  CheckedMoment.ofBessel lo1690b1 lo1690b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1690b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨9,by decide⟩
def hi1690b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨10,by decide⟩
def hi1690 : CheckedMoment :=
  CheckedMoment.ofBessel hi1690b1 hi1690b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1690 : meanBracketCheck (2153/2500) lo1690 hi1690=true := by decide +kernel
def bracket1690 : MeanBracket := meanBracketOfMoments (2153/2500) lo1690 hi1690 accepted1690
def lo1691b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨14,by decide⟩
def lo1691b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨15,by decide⟩
def lo1691 : CheckedMoment :=
  CheckedMoment.ofBessel lo1691b1 lo1691b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1691b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨19,by decide⟩
def hi1691b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨20,by decide⟩
def hi1691 : CheckedMoment :=
  CheckedMoment.ofBessel hi1691b1 hi1691b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1691 : meanBracketCheck (8613/10000) lo1691 hi1691=true := by decide +kernel
def bracket1691 : MeanBracket := meanBracketOfMoments (8613/10000) lo1691 hi1691 accepted1691
def lo1692b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨24,by decide⟩
def lo1692b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨25,by decide⟩
def lo1692 : CheckedMoment :=
  CheckedMoment.ofBessel lo1692b1 lo1692b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1692b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨29,by decide⟩
def hi1692b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨30,by decide⟩
def hi1692 : CheckedMoment :=
  CheckedMoment.ofBessel hi1692b1 hi1692b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1692 : meanBracketCheck (4307/5000) lo1692 hi1692=true := by decide +kernel
def bracket1692 : MeanBracket := meanBracketOfMoments (4307/5000) lo1692 hi1692 accepted1692
def lo1693b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨34,by decide⟩
def lo1693b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨35,by decide⟩
def lo1693 : CheckedMoment :=
  CheckedMoment.ofBessel lo1693b1 lo1693b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1693b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨39,by decide⟩
def hi1693b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨40,by decide⟩
def hi1693 : CheckedMoment :=
  CheckedMoment.ofBessel hi1693b1 hi1693b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1693 : meanBracketCheck (1723/2000) lo1693 hi1693=true := by decide +kernel
def bracket1693 : MeanBracket := meanBracketOfMoments (1723/2000) lo1693 hi1693 accepted1693
def lo1694b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨44,by decide⟩
def lo1694b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨45,by decide⟩
def lo1694 : CheckedMoment :=
  CheckedMoment.ofBessel lo1694b1 lo1694b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1694b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨49,by decide⟩
def hi1694b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨50,by decide⟩
def hi1694 : CheckedMoment :=
  CheckedMoment.ofBessel hi1694b1 hi1694b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1694 : meanBracketCheck (1077/1250) lo1694 hi1694=true := by decide +kernel
def bracket1694 : MeanBracket := meanBracketOfMoments (1077/1250) lo1694 hi1694 accepted1694
def lo1695b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨54,by decide⟩
def lo1695b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨55,by decide⟩
def lo1695 : CheckedMoment :=
  CheckedMoment.ofBessel lo1695b1 lo1695b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1695b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨59,by decide⟩
def hi1695b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨60,by decide⟩
def hi1695 : CheckedMoment :=
  CheckedMoment.ofBessel hi1695b1 hi1695b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1695 : meanBracketCheck (8617/10000) lo1695 hi1695=true := by decide +kernel
def bracket1695 : MeanBracket := meanBracketOfMoments (8617/10000) lo1695 hi1695 accepted1695
#print axioms bracket1680
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0105
