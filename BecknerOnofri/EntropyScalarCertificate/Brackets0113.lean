import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0282
import BecknerOnofri.EntropyScalarCertificate.Bessel0283
import BecknerOnofri.EntropyScalarCertificate.Bessel0284
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0113
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1808b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨32,by decide⟩
def lo1808b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨33,by decide⟩
def lo1808 : CheckedMoment :=
  CheckedMoment.ofBessel lo1808b1 lo1808b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1808b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨37,by decide⟩
def hi1808b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨38,by decide⟩
def hi1808 : CheckedMoment :=
  CheckedMoment.ofBessel hi1808b1 hi1808b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1808 : meanBracketCheck (873/1000) lo1808 hi1808=true := by decide +kernel
def bracket1808 : MeanBracket := meanBracketOfMoments (873/1000) lo1808 hi1808 accepted1808
def lo1809b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨42,by decide⟩
def lo1809b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨43,by decide⟩
def lo1809 : CheckedMoment :=
  CheckedMoment.ofBessel lo1809b1 lo1809b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1809b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨47,by decide⟩
def hi1809b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨48,by decide⟩
def hi1809 : CheckedMoment :=
  CheckedMoment.ofBessel hi1809b1 hi1809b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1809 : meanBracketCheck (8731/10000) lo1809 hi1809=true := by decide +kernel
def bracket1809 : MeanBracket := meanBracketOfMoments (8731/10000) lo1809 hi1809 accepted1809
def lo1810b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨52,by decide⟩
def lo1810b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨53,by decide⟩
def lo1810 : CheckedMoment :=
  CheckedMoment.ofBessel lo1810b1 lo1810b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1810b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨57,by decide⟩
def hi1810b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨58,by decide⟩
def hi1810 : CheckedMoment :=
  CheckedMoment.ofBessel hi1810b1 hi1810b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1810 : meanBracketCheck (2183/2500) lo1810 hi1810=true := by decide +kernel
def bracket1810 : MeanBracket := meanBracketOfMoments (2183/2500) lo1810 hi1810 accepted1810
def lo1811b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨62,by decide⟩
def lo1811b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0282.rows BesselBatch0282.accepted ⟨63,by decide⟩
def lo1811 : CheckedMoment :=
  CheckedMoment.ofBessel lo1811b1 lo1811b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1811b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨3,by decide⟩
def hi1811b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨4,by decide⟩
def hi1811 : CheckedMoment :=
  CheckedMoment.ofBessel hi1811b1 hi1811b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1811 : meanBracketCheck (8733/10000) lo1811 hi1811=true := by decide +kernel
def bracket1811 : MeanBracket := meanBracketOfMoments (8733/10000) lo1811 hi1811 accepted1811
def lo1812b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨8,by decide⟩
def lo1812b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨9,by decide⟩
def lo1812 : CheckedMoment :=
  CheckedMoment.ofBessel lo1812b1 lo1812b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1812b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨13,by decide⟩
def hi1812b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨14,by decide⟩
def hi1812 : CheckedMoment :=
  CheckedMoment.ofBessel hi1812b1 hi1812b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1812 : meanBracketCheck (4367/5000) lo1812 hi1812=true := by decide +kernel
def bracket1812 : MeanBracket := meanBracketOfMoments (4367/5000) lo1812 hi1812 accepted1812
def lo1813b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨18,by decide⟩
def lo1813b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨19,by decide⟩
def lo1813 : CheckedMoment :=
  CheckedMoment.ofBessel lo1813b1 lo1813b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1813b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨23,by decide⟩
def hi1813b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨24,by decide⟩
def hi1813 : CheckedMoment :=
  CheckedMoment.ofBessel hi1813b1 hi1813b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1813 : meanBracketCheck (1747/2000) lo1813 hi1813=true := by decide +kernel
def bracket1813 : MeanBracket := meanBracketOfMoments (1747/2000) lo1813 hi1813 accepted1813
def lo1814b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨28,by decide⟩
def lo1814b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨29,by decide⟩
def lo1814 : CheckedMoment :=
  CheckedMoment.ofBessel lo1814b1 lo1814b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1814b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨33,by decide⟩
def hi1814b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨34,by decide⟩
def hi1814 : CheckedMoment :=
  CheckedMoment.ofBessel hi1814b1 hi1814b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1814 : meanBracketCheck (546/625) lo1814 hi1814=true := by decide +kernel
def bracket1814 : MeanBracket := meanBracketOfMoments (546/625) lo1814 hi1814 accepted1814
def lo1815b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨38,by decide⟩
def lo1815b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨39,by decide⟩
def lo1815 : CheckedMoment :=
  CheckedMoment.ofBessel lo1815b1 lo1815b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1815b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨43,by decide⟩
def hi1815b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨44,by decide⟩
def hi1815 : CheckedMoment :=
  CheckedMoment.ofBessel hi1815b1 hi1815b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1815 : meanBracketCheck (8737/10000) lo1815 hi1815=true := by decide +kernel
def bracket1815 : MeanBracket := meanBracketOfMoments (8737/10000) lo1815 hi1815 accepted1815
def lo1816b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨48,by decide⟩
def lo1816b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨49,by decide⟩
def lo1816 : CheckedMoment :=
  CheckedMoment.ofBessel lo1816b1 lo1816b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1816b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨53,by decide⟩
def hi1816b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨54,by decide⟩
def hi1816 : CheckedMoment :=
  CheckedMoment.ofBessel hi1816b1 hi1816b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1816 : meanBracketCheck (4369/5000) lo1816 hi1816=true := by decide +kernel
def bracket1816 : MeanBracket := meanBracketOfMoments (4369/5000) lo1816 hi1816 accepted1816
def lo1817b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨58,by decide⟩
def lo1817b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨59,by decide⟩
def lo1817 : CheckedMoment :=
  CheckedMoment.ofBessel lo1817b1 lo1817b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1817b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨63,by decide⟩
def hi1817b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨0,by decide⟩
def hi1817 : CheckedMoment :=
  CheckedMoment.ofBessel hi1817b1 hi1817b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1817 : meanBracketCheck (8739/10000) lo1817 hi1817=true := by decide +kernel
def bracket1817 : MeanBracket := meanBracketOfMoments (8739/10000) lo1817 hi1817 accepted1817
def lo1818b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨4,by decide⟩
def lo1818b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨5,by decide⟩
def lo1818 : CheckedMoment :=
  CheckedMoment.ofBessel lo1818b1 lo1818b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1818b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨9,by decide⟩
def hi1818b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨10,by decide⟩
def hi1818 : CheckedMoment :=
  CheckedMoment.ofBessel hi1818b1 hi1818b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1818 : meanBracketCheck (437/500) lo1818 hi1818=true := by decide +kernel
def bracket1818 : MeanBracket := meanBracketOfMoments (437/500) lo1818 hi1818 accepted1818
def lo1819b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨14,by decide⟩
def lo1819b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨15,by decide⟩
def lo1819 : CheckedMoment :=
  CheckedMoment.ofBessel lo1819b1 lo1819b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1819b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨19,by decide⟩
def hi1819b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨20,by decide⟩
def hi1819 : CheckedMoment :=
  CheckedMoment.ofBessel hi1819b1 hi1819b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1819 : meanBracketCheck (8741/10000) lo1819 hi1819=true := by decide +kernel
def bracket1819 : MeanBracket := meanBracketOfMoments (8741/10000) lo1819 hi1819 accepted1819
def lo1820b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨24,by decide⟩
def lo1820b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨25,by decide⟩
def lo1820 : CheckedMoment :=
  CheckedMoment.ofBessel lo1820b1 lo1820b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1820b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨29,by decide⟩
def hi1820b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨30,by decide⟩
def hi1820 : CheckedMoment :=
  CheckedMoment.ofBessel hi1820b1 hi1820b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1820 : meanBracketCheck (4371/5000) lo1820 hi1820=true := by decide +kernel
def bracket1820 : MeanBracket := meanBracketOfMoments (4371/5000) lo1820 hi1820 accepted1820
def lo1821b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨34,by decide⟩
def lo1821b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨35,by decide⟩
def lo1821 : CheckedMoment :=
  CheckedMoment.ofBessel lo1821b1 lo1821b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1821b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨39,by decide⟩
def hi1821b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨40,by decide⟩
def hi1821 : CheckedMoment :=
  CheckedMoment.ofBessel hi1821b1 hi1821b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1821 : meanBracketCheck (8743/10000) lo1821 hi1821=true := by decide +kernel
def bracket1821 : MeanBracket := meanBracketOfMoments (8743/10000) lo1821 hi1821 accepted1821
def lo1822b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨44,by decide⟩
def lo1822b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨45,by decide⟩
def lo1822 : CheckedMoment :=
  CheckedMoment.ofBessel lo1822b1 lo1822b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1822b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨49,by decide⟩
def hi1822b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨50,by decide⟩
def hi1822 : CheckedMoment :=
  CheckedMoment.ofBessel hi1822b1 hi1822b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1822 : meanBracketCheck (1093/1250) lo1822 hi1822=true := by decide +kernel
def bracket1822 : MeanBracket := meanBracketOfMoments (1093/1250) lo1822 hi1822 accepted1822
def lo1823b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨54,by decide⟩
def lo1823b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨55,by decide⟩
def lo1823 : CheckedMoment :=
  CheckedMoment.ofBessel lo1823b1 lo1823b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1823b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨59,by decide⟩
def hi1823b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨60,by decide⟩
def hi1823 : CheckedMoment :=
  CheckedMoment.ofBessel hi1823b1 hi1823b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1823 : meanBracketCheck (1749/2000) lo1823 hi1823=true := by decide +kernel
def bracket1823 : MeanBracket := meanBracketOfMoments (1749/2000) lo1823 hi1823 accepted1823
#print axioms bracket1808
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0113
