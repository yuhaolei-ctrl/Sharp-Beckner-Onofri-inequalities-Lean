module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0270
public import BecknerOnofri.EntropyScalarCertificate.Bessel0271
public import BecknerOnofri.EntropyScalarCertificate.Bessel0272

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0108
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1728b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨0,by decide⟩
def lo1728b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨1,by decide⟩
def lo1728 : CheckedMoment :=
  CheckedMoment.ofBessel lo1728b1 lo1728b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1728b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨5,by decide⟩
def hi1728b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨6,by decide⟩
def hi1728 : CheckedMoment :=
  CheckedMoment.ofBessel hi1728b1 hi1728b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1728 : meanBracketCheck (173/200) lo1728 hi1728=true := by decide +kernel
def bracket1728 : MeanBracket := meanBracketOfMoments (173/200) lo1728 hi1728 accepted1728
def lo1729b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨10,by decide⟩
def lo1729b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨11,by decide⟩
def lo1729 : CheckedMoment :=
  CheckedMoment.ofBessel lo1729b1 lo1729b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1729b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨15,by decide⟩
def hi1729b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨16,by decide⟩
def hi1729 : CheckedMoment :=
  CheckedMoment.ofBessel hi1729b1 hi1729b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1729 : meanBracketCheck (8651/10000) lo1729 hi1729=true := by decide +kernel
def bracket1729 : MeanBracket := meanBracketOfMoments (8651/10000) lo1729 hi1729 accepted1729
def lo1730b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨20,by decide⟩
def lo1730b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨21,by decide⟩
def lo1730 : CheckedMoment :=
  CheckedMoment.ofBessel lo1730b1 lo1730b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1730b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨25,by decide⟩
def hi1730b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨26,by decide⟩
def hi1730 : CheckedMoment :=
  CheckedMoment.ofBessel hi1730b1 hi1730b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1730 : meanBracketCheck (2163/2500) lo1730 hi1730=true := by decide +kernel
def bracket1730 : MeanBracket := meanBracketOfMoments (2163/2500) lo1730 hi1730 accepted1730
def lo1731b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨30,by decide⟩
def lo1731b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨31,by decide⟩
def lo1731 : CheckedMoment :=
  CheckedMoment.ofBessel lo1731b1 lo1731b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1731b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨35,by decide⟩
def hi1731b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨36,by decide⟩
def hi1731 : CheckedMoment :=
  CheckedMoment.ofBessel hi1731b1 hi1731b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1731 : meanBracketCheck (8653/10000) lo1731 hi1731=true := by decide +kernel
def bracket1731 : MeanBracket := meanBracketOfMoments (8653/10000) lo1731 hi1731 accepted1731
def lo1732b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨40,by decide⟩
def lo1732b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨41,by decide⟩
def lo1732 : CheckedMoment :=
  CheckedMoment.ofBessel lo1732b1 lo1732b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1732b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨45,by decide⟩
def hi1732b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨46,by decide⟩
def hi1732 : CheckedMoment :=
  CheckedMoment.ofBessel hi1732b1 hi1732b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1732 : meanBracketCheck (4327/5000) lo1732 hi1732=true := by decide +kernel
def bracket1732 : MeanBracket := meanBracketOfMoments (4327/5000) lo1732 hi1732 accepted1732
def lo1733b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨50,by decide⟩
def lo1733b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨51,by decide⟩
def lo1733 : CheckedMoment :=
  CheckedMoment.ofBessel lo1733b1 lo1733b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1733b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨55,by decide⟩
def hi1733b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨56,by decide⟩
def hi1733 : CheckedMoment :=
  CheckedMoment.ofBessel hi1733b1 hi1733b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1733 : meanBracketCheck (1731/2000) lo1733 hi1733=true := by decide +kernel
def bracket1733 : MeanBracket := meanBracketOfMoments (1731/2000) lo1733 hi1733 accepted1733
def lo1734b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨60,by decide⟩
def lo1734b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨61,by decide⟩
def lo1734 : CheckedMoment :=
  CheckedMoment.ofBessel lo1734b1 lo1734b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1734b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨1,by decide⟩
def hi1734b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨2,by decide⟩
def hi1734 : CheckedMoment :=
  CheckedMoment.ofBessel hi1734b1 hi1734b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1734 : meanBracketCheck (541/625) lo1734 hi1734=true := by decide +kernel
def bracket1734 : MeanBracket := meanBracketOfMoments (541/625) lo1734 hi1734 accepted1734
def lo1735b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨6,by decide⟩
def lo1735b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨7,by decide⟩
def lo1735 : CheckedMoment :=
  CheckedMoment.ofBessel lo1735b1 lo1735b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1735b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨11,by decide⟩
def hi1735b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨12,by decide⟩
def hi1735 : CheckedMoment :=
  CheckedMoment.ofBessel hi1735b1 hi1735b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1735 : meanBracketCheck (8657/10000) lo1735 hi1735=true := by decide +kernel
def bracket1735 : MeanBracket := meanBracketOfMoments (8657/10000) lo1735 hi1735 accepted1735
def lo1736b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨16,by decide⟩
def lo1736b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨17,by decide⟩
def lo1736 : CheckedMoment :=
  CheckedMoment.ofBessel lo1736b1 lo1736b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1736b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨21,by decide⟩
def hi1736b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨22,by decide⟩
def hi1736 : CheckedMoment :=
  CheckedMoment.ofBessel hi1736b1 hi1736b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1736 : meanBracketCheck (4329/5000) lo1736 hi1736=true := by decide +kernel
def bracket1736 : MeanBracket := meanBracketOfMoments (4329/5000) lo1736 hi1736 accepted1736
def lo1737b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨26,by decide⟩
def lo1737b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨27,by decide⟩
def lo1737 : CheckedMoment :=
  CheckedMoment.ofBessel lo1737b1 lo1737b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1737b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨31,by decide⟩
def hi1737b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨32,by decide⟩
def hi1737 : CheckedMoment :=
  CheckedMoment.ofBessel hi1737b1 hi1737b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1737 : meanBracketCheck (8659/10000) lo1737 hi1737=true := by decide +kernel
def bracket1737 : MeanBracket := meanBracketOfMoments (8659/10000) lo1737 hi1737 accepted1737
def lo1738b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨36,by decide⟩
def lo1738b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨37,by decide⟩
def lo1738 : CheckedMoment :=
  CheckedMoment.ofBessel lo1738b1 lo1738b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1738b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨41,by decide⟩
def hi1738b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨42,by decide⟩
def hi1738 : CheckedMoment :=
  CheckedMoment.ofBessel hi1738b1 hi1738b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1738 : meanBracketCheck (433/500) lo1738 hi1738=true := by decide +kernel
def bracket1738 : MeanBracket := meanBracketOfMoments (433/500) lo1738 hi1738 accepted1738
def lo1739b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨46,by decide⟩
def lo1739b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨47,by decide⟩
def lo1739 : CheckedMoment :=
  CheckedMoment.ofBessel lo1739b1 lo1739b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1739b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨51,by decide⟩
def hi1739b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨52,by decide⟩
def hi1739 : CheckedMoment :=
  CheckedMoment.ofBessel hi1739b1 hi1739b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1739 : meanBracketCheck (8661/10000) lo1739 hi1739=true := by decide +kernel
def bracket1739 : MeanBracket := meanBracketOfMoments (8661/10000) lo1739 hi1739 accepted1739
def lo1740b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨56,by decide⟩
def lo1740b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨57,by decide⟩
def lo1740 : CheckedMoment :=
  CheckedMoment.ofBessel lo1740b1 lo1740b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1740b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨61,by decide⟩
def hi1740b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨62,by decide⟩
def hi1740 : CheckedMoment :=
  CheckedMoment.ofBessel hi1740b1 hi1740b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1740 : meanBracketCheck (4331/5000) lo1740 hi1740=true := by decide +kernel
def bracket1740 : MeanBracket := meanBracketOfMoments (4331/5000) lo1740 hi1740 accepted1740
def lo1741b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨2,by decide⟩
def lo1741b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨3,by decide⟩
def lo1741 : CheckedMoment :=
  CheckedMoment.ofBessel lo1741b1 lo1741b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1741b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨7,by decide⟩
def hi1741b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨8,by decide⟩
def hi1741 : CheckedMoment :=
  CheckedMoment.ofBessel hi1741b1 hi1741b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1741 : meanBracketCheck (8663/10000) lo1741 hi1741=true := by decide +kernel
def bracket1741 : MeanBracket := meanBracketOfMoments (8663/10000) lo1741 hi1741 accepted1741
def lo1742b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨12,by decide⟩
def lo1742b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨13,by decide⟩
def lo1742 : CheckedMoment :=
  CheckedMoment.ofBessel lo1742b1 lo1742b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1742b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨17,by decide⟩
def hi1742b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨18,by decide⟩
def hi1742 : CheckedMoment :=
  CheckedMoment.ofBessel hi1742b1 hi1742b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1742 : meanBracketCheck (1083/1250) lo1742 hi1742=true := by decide +kernel
def bracket1742 : MeanBracket := meanBracketOfMoments (1083/1250) lo1742 hi1742 accepted1742
def lo1743b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨22,by decide⟩
def lo1743b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨23,by decide⟩
def lo1743 : CheckedMoment :=
  CheckedMoment.ofBessel lo1743b1 lo1743b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1743b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨27,by decide⟩
def hi1743b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨28,by decide⟩
def hi1743 : CheckedMoment :=
  CheckedMoment.ofBessel hi1743b1 hi1743b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1743 : meanBracketCheck (1733/2000) lo1743 hi1743=true := by decide +kernel
def bracket1743 : MeanBracket := meanBracketOfMoments (1733/2000) lo1743 hi1743 accepted1743
#print axioms bracket1728
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0108
