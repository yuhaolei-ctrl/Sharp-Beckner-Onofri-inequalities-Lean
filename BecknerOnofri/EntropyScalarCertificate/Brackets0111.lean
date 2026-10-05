import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0277
import BecknerOnofri.EntropyScalarCertificate.Bessel0278
import BecknerOnofri.EntropyScalarCertificate.Bessel0279
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0111
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1776b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨32,by decide⟩
def lo1776b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨33,by decide⟩
def lo1776 : CheckedMoment :=
  CheckedMoment.ofBessel lo1776b1 lo1776b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1776b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨37,by decide⟩
def hi1776b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨38,by decide⟩
def hi1776 : CheckedMoment :=
  CheckedMoment.ofBessel hi1776b1 hi1776b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1776 : meanBracketCheck (4349/5000) lo1776 hi1776=true := by decide +kernel
def bracket1776 : MeanBracket := meanBracketOfMoments (4349/5000) lo1776 hi1776 accepted1776
def lo1777b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨42,by decide⟩
def lo1777b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨43,by decide⟩
def lo1777 : CheckedMoment :=
  CheckedMoment.ofBessel lo1777b1 lo1777b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1777b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨47,by decide⟩
def hi1777b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨48,by decide⟩
def hi1777 : CheckedMoment :=
  CheckedMoment.ofBessel hi1777b1 hi1777b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1777 : meanBracketCheck (8699/10000) lo1777 hi1777=true := by decide +kernel
def bracket1777 : MeanBracket := meanBracketOfMoments (8699/10000) lo1777 hi1777 accepted1777
def lo1778b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨52,by decide⟩
def lo1778b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨53,by decide⟩
def lo1778 : CheckedMoment :=
  CheckedMoment.ofBessel lo1778b1 lo1778b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1778b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨57,by decide⟩
def hi1778b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨58,by decide⟩
def hi1778 : CheckedMoment :=
  CheckedMoment.ofBessel hi1778b1 hi1778b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1778 : meanBracketCheck (87/100) lo1778 hi1778=true := by decide +kernel
def bracket1778 : MeanBracket := meanBracketOfMoments (87/100) lo1778 hi1778 accepted1778
def lo1779b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨62,by decide⟩
def lo1779b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨63,by decide⟩
def lo1779 : CheckedMoment :=
  CheckedMoment.ofBessel lo1779b1 lo1779b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1779b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨3,by decide⟩
def hi1779b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨4,by decide⟩
def hi1779 : CheckedMoment :=
  CheckedMoment.ofBessel hi1779b1 hi1779b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1779 : meanBracketCheck (8701/10000) lo1779 hi1779=true := by decide +kernel
def bracket1779 : MeanBracket := meanBracketOfMoments (8701/10000) lo1779 hi1779 accepted1779
def lo1780b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨8,by decide⟩
def lo1780b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨9,by decide⟩
def lo1780 : CheckedMoment :=
  CheckedMoment.ofBessel lo1780b1 lo1780b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1780b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨13,by decide⟩
def hi1780b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨14,by decide⟩
def hi1780 : CheckedMoment :=
  CheckedMoment.ofBessel hi1780b1 hi1780b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1780 : meanBracketCheck (4351/5000) lo1780 hi1780=true := by decide +kernel
def bracket1780 : MeanBracket := meanBracketOfMoments (4351/5000) lo1780 hi1780 accepted1780
def lo1781b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨18,by decide⟩
def lo1781b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨19,by decide⟩
def lo1781 : CheckedMoment :=
  CheckedMoment.ofBessel lo1781b1 lo1781b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1781b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨23,by decide⟩
def hi1781b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨24,by decide⟩
def hi1781 : CheckedMoment :=
  CheckedMoment.ofBessel hi1781b1 hi1781b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1781 : meanBracketCheck (8703/10000) lo1781 hi1781=true := by decide +kernel
def bracket1781 : MeanBracket := meanBracketOfMoments (8703/10000) lo1781 hi1781 accepted1781
def lo1782b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨28,by decide⟩
def lo1782b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨29,by decide⟩
def lo1782 : CheckedMoment :=
  CheckedMoment.ofBessel lo1782b1 lo1782b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1782b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨33,by decide⟩
def hi1782b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨34,by decide⟩
def hi1782 : CheckedMoment :=
  CheckedMoment.ofBessel hi1782b1 hi1782b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1782 : meanBracketCheck (544/625) lo1782 hi1782=true := by decide +kernel
def bracket1782 : MeanBracket := meanBracketOfMoments (544/625) lo1782 hi1782 accepted1782
def lo1783b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨38,by decide⟩
def lo1783b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨39,by decide⟩
def lo1783 : CheckedMoment :=
  CheckedMoment.ofBessel lo1783b1 lo1783b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1783b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨43,by decide⟩
def hi1783b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨44,by decide⟩
def hi1783 : CheckedMoment :=
  CheckedMoment.ofBessel hi1783b1 hi1783b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1783 : meanBracketCheck (1741/2000) lo1783 hi1783=true := by decide +kernel
def bracket1783 : MeanBracket := meanBracketOfMoments (1741/2000) lo1783 hi1783 accepted1783
def lo1784b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨48,by decide⟩
def lo1784b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨49,by decide⟩
def lo1784 : CheckedMoment :=
  CheckedMoment.ofBessel lo1784b1 lo1784b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1784b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨53,by decide⟩
def hi1784b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨54,by decide⟩
def hi1784 : CheckedMoment :=
  CheckedMoment.ofBessel hi1784b1 hi1784b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1784 : meanBracketCheck (4353/5000) lo1784 hi1784=true := by decide +kernel
def bracket1784 : MeanBracket := meanBracketOfMoments (4353/5000) lo1784 hi1784 accepted1784
def lo1785b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨58,by decide⟩
def lo1785b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨59,by decide⟩
def lo1785 : CheckedMoment :=
  CheckedMoment.ofBessel lo1785b1 lo1785b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1785b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨63,by decide⟩
def hi1785b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨0,by decide⟩
def hi1785 : CheckedMoment :=
  CheckedMoment.ofBessel hi1785b1 hi1785b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1785 : meanBracketCheck (8707/10000) lo1785 hi1785=true := by decide +kernel
def bracket1785 : MeanBracket := meanBracketOfMoments (8707/10000) lo1785 hi1785 accepted1785
def lo1786b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨4,by decide⟩
def lo1786b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨5,by decide⟩
def lo1786 : CheckedMoment :=
  CheckedMoment.ofBessel lo1786b1 lo1786b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1786b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨9,by decide⟩
def hi1786b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨10,by decide⟩
def hi1786 : CheckedMoment :=
  CheckedMoment.ofBessel hi1786b1 hi1786b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1786 : meanBracketCheck (2177/2500) lo1786 hi1786=true := by decide +kernel
def bracket1786 : MeanBracket := meanBracketOfMoments (2177/2500) lo1786 hi1786 accepted1786
def lo1787b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨14,by decide⟩
def lo1787b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨15,by decide⟩
def lo1787 : CheckedMoment :=
  CheckedMoment.ofBessel lo1787b1 lo1787b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1787b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨19,by decide⟩
def hi1787b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨20,by decide⟩
def hi1787 : CheckedMoment :=
  CheckedMoment.ofBessel hi1787b1 hi1787b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1787 : meanBracketCheck (8709/10000) lo1787 hi1787=true := by decide +kernel
def bracket1787 : MeanBracket := meanBracketOfMoments (8709/10000) lo1787 hi1787 accepted1787
def lo1788b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨24,by decide⟩
def lo1788b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨25,by decide⟩
def lo1788 : CheckedMoment :=
  CheckedMoment.ofBessel lo1788b1 lo1788b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1788b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨29,by decide⟩
def hi1788b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨30,by decide⟩
def hi1788 : CheckedMoment :=
  CheckedMoment.ofBessel hi1788b1 hi1788b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1788 : meanBracketCheck (871/1000) lo1788 hi1788=true := by decide +kernel
def bracket1788 : MeanBracket := meanBracketOfMoments (871/1000) lo1788 hi1788 accepted1788
def lo1789b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨34,by decide⟩
def lo1789b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨35,by decide⟩
def lo1789 : CheckedMoment :=
  CheckedMoment.ofBessel lo1789b1 lo1789b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1789b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨39,by decide⟩
def hi1789b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨40,by decide⟩
def hi1789 : CheckedMoment :=
  CheckedMoment.ofBessel hi1789b1 hi1789b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1789 : meanBracketCheck (8711/10000) lo1789 hi1789=true := by decide +kernel
def bracket1789 : MeanBracket := meanBracketOfMoments (8711/10000) lo1789 hi1789 accepted1789
def lo1790b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨44,by decide⟩
def lo1790b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨45,by decide⟩
def lo1790 : CheckedMoment :=
  CheckedMoment.ofBessel lo1790b1 lo1790b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1790b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨49,by decide⟩
def hi1790b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨50,by decide⟩
def hi1790 : CheckedMoment :=
  CheckedMoment.ofBessel hi1790b1 hi1790b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1790 : meanBracketCheck (1089/1250) lo1790 hi1790=true := by decide +kernel
def bracket1790 : MeanBracket := meanBracketOfMoments (1089/1250) lo1790 hi1790 accepted1790
def lo1791b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨54,by decide⟩
def lo1791b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨55,by decide⟩
def lo1791 : CheckedMoment :=
  CheckedMoment.ofBessel lo1791b1 lo1791b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1791b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨59,by decide⟩
def hi1791b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0279.rows BesselBatch0279.accepted ⟨60,by decide⟩
def hi1791 : CheckedMoment :=
  CheckedMoment.ofBessel hi1791b1 hi1791b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1791 : meanBracketCheck (8713/10000) lo1791 hi1791=true := by decide +kernel
def bracket1791 : MeanBracket := meanBracketOfMoments (8713/10000) lo1791 hi1791 accepted1791
#print axioms bracket1776
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0111
