module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0267
public import BecknerOnofri.EntropyScalarCertificate.Bessel0268
public import BecknerOnofri.EntropyScalarCertificate.Bessel0269

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0107
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1712b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨32,by decide⟩
def lo1712b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨33,by decide⟩
def lo1712 : CheckedMoment :=
  CheckedMoment.ofBessel lo1712b1 lo1712b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1712b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨37,by decide⟩
def hi1712b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨38,by decide⟩
def hi1712 : CheckedMoment :=
  CheckedMoment.ofBessel hi1712b1 hi1712b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1712 : meanBracketCheck (4317/5000) lo1712 hi1712=true := by decide +kernel
def bracket1712 : MeanBracket := meanBracketOfMoments (4317/5000) lo1712 hi1712 accepted1712
def lo1713b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨42,by decide⟩
def lo1713b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨43,by decide⟩
def lo1713 : CheckedMoment :=
  CheckedMoment.ofBessel lo1713b1 lo1713b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1713b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨47,by decide⟩
def hi1713b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨48,by decide⟩
def hi1713 : CheckedMoment :=
  CheckedMoment.ofBessel hi1713b1 hi1713b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1713 : meanBracketCheck (1727/2000) lo1713 hi1713=true := by decide +kernel
def bracket1713 : MeanBracket := meanBracketOfMoments (1727/2000) lo1713 hi1713 accepted1713
def lo1714b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨52,by decide⟩
def lo1714b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨53,by decide⟩
def lo1714 : CheckedMoment :=
  CheckedMoment.ofBessel lo1714b1 lo1714b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1714b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨57,by decide⟩
def hi1714b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨58,by decide⟩
def hi1714 : CheckedMoment :=
  CheckedMoment.ofBessel hi1714b1 hi1714b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1714 : meanBracketCheck (2159/2500) lo1714 hi1714=true := by decide +kernel
def bracket1714 : MeanBracket := meanBracketOfMoments (2159/2500) lo1714 hi1714 accepted1714
def lo1715b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨62,by decide⟩
def lo1715b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨63,by decide⟩
def lo1715 : CheckedMoment :=
  CheckedMoment.ofBessel lo1715b1 lo1715b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1715b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨3,by decide⟩
def hi1715b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨4,by decide⟩
def hi1715 : CheckedMoment :=
  CheckedMoment.ofBessel hi1715b1 hi1715b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1715 : meanBracketCheck (8637/10000) lo1715 hi1715=true := by decide +kernel
def bracket1715 : MeanBracket := meanBracketOfMoments (8637/10000) lo1715 hi1715 accepted1715
def lo1716b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨8,by decide⟩
def lo1716b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨9,by decide⟩
def lo1716 : CheckedMoment :=
  CheckedMoment.ofBessel lo1716b1 lo1716b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1716b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨13,by decide⟩
def hi1716b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨14,by decide⟩
def hi1716 : CheckedMoment :=
  CheckedMoment.ofBessel hi1716b1 hi1716b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1716 : meanBracketCheck (4319/5000) lo1716 hi1716=true := by decide +kernel
def bracket1716 : MeanBracket := meanBracketOfMoments (4319/5000) lo1716 hi1716 accepted1716
def lo1717b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨18,by decide⟩
def lo1717b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨19,by decide⟩
def lo1717 : CheckedMoment :=
  CheckedMoment.ofBessel lo1717b1 lo1717b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1717b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨23,by decide⟩
def hi1717b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨24,by decide⟩
def hi1717 : CheckedMoment :=
  CheckedMoment.ofBessel hi1717b1 hi1717b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1717 : meanBracketCheck (8639/10000) lo1717 hi1717=true := by decide +kernel
def bracket1717 : MeanBracket := meanBracketOfMoments (8639/10000) lo1717 hi1717 accepted1717
def lo1718b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨28,by decide⟩
def lo1718b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨29,by decide⟩
def lo1718 : CheckedMoment :=
  CheckedMoment.ofBessel lo1718b1 lo1718b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1718b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨33,by decide⟩
def hi1718b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨34,by decide⟩
def hi1718 : CheckedMoment :=
  CheckedMoment.ofBessel hi1718b1 hi1718b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1718 : meanBracketCheck (108/125) lo1718 hi1718=true := by decide +kernel
def bracket1718 : MeanBracket := meanBracketOfMoments (108/125) lo1718 hi1718 accepted1718
def lo1719b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨38,by decide⟩
def lo1719b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨39,by decide⟩
def lo1719 : CheckedMoment :=
  CheckedMoment.ofBessel lo1719b1 lo1719b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1719b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨43,by decide⟩
def hi1719b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨44,by decide⟩
def hi1719 : CheckedMoment :=
  CheckedMoment.ofBessel hi1719b1 hi1719b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1719 : meanBracketCheck (8641/10000) lo1719 hi1719=true := by decide +kernel
def bracket1719 : MeanBracket := meanBracketOfMoments (8641/10000) lo1719 hi1719 accepted1719
def lo1720b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨48,by decide⟩
def lo1720b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨49,by decide⟩
def lo1720 : CheckedMoment :=
  CheckedMoment.ofBessel lo1720b1 lo1720b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1720b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨53,by decide⟩
def hi1720b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨54,by decide⟩
def hi1720 : CheckedMoment :=
  CheckedMoment.ofBessel hi1720b1 hi1720b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1720 : meanBracketCheck (4321/5000) lo1720 hi1720=true := by decide +kernel
def bracket1720 : MeanBracket := meanBracketOfMoments (4321/5000) lo1720 hi1720 accepted1720
def lo1721b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨58,by decide⟩
def lo1721b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨59,by decide⟩
def lo1721 : CheckedMoment :=
  CheckedMoment.ofBessel lo1721b1 lo1721b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1721b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨63,by decide⟩
def hi1721b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨0,by decide⟩
def hi1721 : CheckedMoment :=
  CheckedMoment.ofBessel hi1721b1 hi1721b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1721 : meanBracketCheck (8643/10000) lo1721 hi1721=true := by decide +kernel
def bracket1721 : MeanBracket := meanBracketOfMoments (8643/10000) lo1721 hi1721 accepted1721
def lo1722b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨4,by decide⟩
def lo1722b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨5,by decide⟩
def lo1722 : CheckedMoment :=
  CheckedMoment.ofBessel lo1722b1 lo1722b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1722b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨9,by decide⟩
def hi1722b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨10,by decide⟩
def hi1722 : CheckedMoment :=
  CheckedMoment.ofBessel hi1722b1 hi1722b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1722 : meanBracketCheck (2161/2500) lo1722 hi1722=true := by decide +kernel
def bracket1722 : MeanBracket := meanBracketOfMoments (2161/2500) lo1722 hi1722 accepted1722
def lo1723b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨14,by decide⟩
def lo1723b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨15,by decide⟩
def lo1723 : CheckedMoment :=
  CheckedMoment.ofBessel lo1723b1 lo1723b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1723b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨19,by decide⟩
def hi1723b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨20,by decide⟩
def hi1723 : CheckedMoment :=
  CheckedMoment.ofBessel hi1723b1 hi1723b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1723 : meanBracketCheck (1729/2000) lo1723 hi1723=true := by decide +kernel
def bracket1723 : MeanBracket := meanBracketOfMoments (1729/2000) lo1723 hi1723 accepted1723
def lo1724b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨24,by decide⟩
def lo1724b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨25,by decide⟩
def lo1724 : CheckedMoment :=
  CheckedMoment.ofBessel lo1724b1 lo1724b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1724b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨29,by decide⟩
def hi1724b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨30,by decide⟩
def hi1724 : CheckedMoment :=
  CheckedMoment.ofBessel hi1724b1 hi1724b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1724 : meanBracketCheck (4323/5000) lo1724 hi1724=true := by decide +kernel
def bracket1724 : MeanBracket := meanBracketOfMoments (4323/5000) lo1724 hi1724 accepted1724
def lo1725b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨34,by decide⟩
def lo1725b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨35,by decide⟩
def lo1725 : CheckedMoment :=
  CheckedMoment.ofBessel lo1725b1 lo1725b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1725b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨39,by decide⟩
def hi1725b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨40,by decide⟩
def hi1725 : CheckedMoment :=
  CheckedMoment.ofBessel hi1725b1 hi1725b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1725 : meanBracketCheck (8647/10000) lo1725 hi1725=true := by decide +kernel
def bracket1725 : MeanBracket := meanBracketOfMoments (8647/10000) lo1725 hi1725 accepted1725
def lo1726b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨44,by decide⟩
def lo1726b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨45,by decide⟩
def lo1726 : CheckedMoment :=
  CheckedMoment.ofBessel lo1726b1 lo1726b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1726b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨49,by decide⟩
def hi1726b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨50,by decide⟩
def hi1726 : CheckedMoment :=
  CheckedMoment.ofBessel hi1726b1 hi1726b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1726 : meanBracketCheck (1081/1250) lo1726 hi1726=true := by decide +kernel
def bracket1726 : MeanBracket := meanBracketOfMoments (1081/1250) lo1726 hi1726 accepted1726
def lo1727b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨54,by decide⟩
def lo1727b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨55,by decide⟩
def lo1727 : CheckedMoment :=
  CheckedMoment.ofBessel lo1727b1 lo1727b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1727b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨59,by decide⟩
def hi1727b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨60,by decide⟩
def hi1727 : CheckedMoment :=
  CheckedMoment.ofBessel hi1727b1 hi1727b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1727 : meanBracketCheck (8649/10000) lo1727 hi1727=true := by decide +kernel
def bracket1727 : MeanBracket := meanBracketOfMoments (8649/10000) lo1727 hi1727 accepted1727
#print axioms bracket1712
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0107
