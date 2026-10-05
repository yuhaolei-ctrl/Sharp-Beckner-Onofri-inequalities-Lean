module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0285
public import BecknerOnofri.EntropyScalarCertificate.Bessel0286
public import BecknerOnofri.EntropyScalarCertificate.Bessel0287

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0114
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1824b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨0,by decide⟩
def lo1824b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨1,by decide⟩
def lo1824 : CheckedMoment :=
  CheckedMoment.ofBessel lo1824b1 lo1824b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1824b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨5,by decide⟩
def hi1824b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨6,by decide⟩
def hi1824 : CheckedMoment :=
  CheckedMoment.ofBessel hi1824b1 hi1824b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1824 : meanBracketCheck (4373/5000) lo1824 hi1824=true := by decide +kernel
def bracket1824 : MeanBracket := meanBracketOfMoments (4373/5000) lo1824 hi1824 accepted1824
def lo1825b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨10,by decide⟩
def lo1825b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨11,by decide⟩
def lo1825 : CheckedMoment :=
  CheckedMoment.ofBessel lo1825b1 lo1825b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1825b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨15,by decide⟩
def hi1825b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨16,by decide⟩
def hi1825 : CheckedMoment :=
  CheckedMoment.ofBessel hi1825b1 hi1825b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1825 : meanBracketCheck (8747/10000) lo1825 hi1825=true := by decide +kernel
def bracket1825 : MeanBracket := meanBracketOfMoments (8747/10000) lo1825 hi1825 accepted1825
def lo1826b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨20,by decide⟩
def lo1826b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨21,by decide⟩
def lo1826 : CheckedMoment :=
  CheckedMoment.ofBessel lo1826b1 lo1826b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1826b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨25,by decide⟩
def hi1826b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨26,by decide⟩
def hi1826 : CheckedMoment :=
  CheckedMoment.ofBessel hi1826b1 hi1826b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1826 : meanBracketCheck (2187/2500) lo1826 hi1826=true := by decide +kernel
def bracket1826 : MeanBracket := meanBracketOfMoments (2187/2500) lo1826 hi1826 accepted1826
def lo1827b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨30,by decide⟩
def lo1827b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨31,by decide⟩
def lo1827 : CheckedMoment :=
  CheckedMoment.ofBessel lo1827b1 lo1827b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1827b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨35,by decide⟩
def hi1827b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨36,by decide⟩
def hi1827 : CheckedMoment :=
  CheckedMoment.ofBessel hi1827b1 hi1827b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1827 : meanBracketCheck (8749/10000) lo1827 hi1827=true := by decide +kernel
def bracket1827 : MeanBracket := meanBracketOfMoments (8749/10000) lo1827 hi1827 accepted1827
def lo1828b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨40,by decide⟩
def lo1828b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨41,by decide⟩
def lo1828 : CheckedMoment :=
  CheckedMoment.ofBessel lo1828b1 lo1828b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1828b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨45,by decide⟩
def hi1828b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨46,by decide⟩
def hi1828 : CheckedMoment :=
  CheckedMoment.ofBessel hi1828b1 hi1828b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1828 : meanBracketCheck (7/8) lo1828 hi1828=true := by decide +kernel
def bracket1828 : MeanBracket := meanBracketOfMoments (7/8) lo1828 hi1828 accepted1828
def lo1829b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨50,by decide⟩
def lo1829b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨51,by decide⟩
def lo1829 : CheckedMoment :=
  CheckedMoment.ofBessel lo1829b1 lo1829b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1829b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨55,by decide⟩
def hi1829b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨56,by decide⟩
def hi1829 : CheckedMoment :=
  CheckedMoment.ofBessel hi1829b1 hi1829b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1829 : meanBracketCheck (1751/2000) lo1829 hi1829=true := by decide +kernel
def bracket1829 : MeanBracket := meanBracketOfMoments (1751/2000) lo1829 hi1829 accepted1829
def lo1830b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨60,by decide⟩
def lo1830b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨61,by decide⟩
def lo1830 : CheckedMoment :=
  CheckedMoment.ofBessel lo1830b1 lo1830b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1830b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨1,by decide⟩
def hi1830b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨2,by decide⟩
def hi1830 : CheckedMoment :=
  CheckedMoment.ofBessel hi1830b1 hi1830b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1830 : meanBracketCheck (219/250) lo1830 hi1830=true := by decide +kernel
def bracket1830 : MeanBracket := meanBracketOfMoments (219/250) lo1830 hi1830 accepted1830
def lo1831b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨6,by decide⟩
def lo1831b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨7,by decide⟩
def lo1831 : CheckedMoment :=
  CheckedMoment.ofBessel lo1831b1 lo1831b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1831b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨11,by decide⟩
def hi1831b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨12,by decide⟩
def hi1831 : CheckedMoment :=
  CheckedMoment.ofBessel hi1831b1 hi1831b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1831 : meanBracketCheck (1753/2000) lo1831 hi1831=true := by decide +kernel
def bracket1831 : MeanBracket := meanBracketOfMoments (1753/2000) lo1831 hi1831 accepted1831
def lo1832b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨16,by decide⟩
def lo1832b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨17,by decide⟩
def lo1832 : CheckedMoment :=
  CheckedMoment.ofBessel lo1832b1 lo1832b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1832b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨21,by decide⟩
def hi1832b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨22,by decide⟩
def hi1832 : CheckedMoment :=
  CheckedMoment.ofBessel hi1832b1 hi1832b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1832 : meanBracketCheck (877/1000) lo1832 hi1832=true := by decide +kernel
def bracket1832 : MeanBracket := meanBracketOfMoments (877/1000) lo1832 hi1832 accepted1832
def lo1833b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨26,by decide⟩
def lo1833b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨27,by decide⟩
def lo1833 : CheckedMoment :=
  CheckedMoment.ofBessel lo1833b1 lo1833b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1833b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨31,by decide⟩
def hi1833b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨32,by decide⟩
def hi1833 : CheckedMoment :=
  CheckedMoment.ofBessel hi1833b1 hi1833b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1833 : meanBracketCheck (351/400) lo1833 hi1833=true := by decide +kernel
def bracket1833 : MeanBracket := meanBracketOfMoments (351/400) lo1833 hi1833 accepted1833
def lo1834b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨36,by decide⟩
def lo1834b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨37,by decide⟩
def lo1834 : CheckedMoment :=
  CheckedMoment.ofBessel lo1834b1 lo1834b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1834b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨41,by decide⟩
def hi1834b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨42,by decide⟩
def hi1834 : CheckedMoment :=
  CheckedMoment.ofBessel hi1834b1 hi1834b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1834 : meanBracketCheck (439/500) lo1834 hi1834=true := by decide +kernel
def bracket1834 : MeanBracket := meanBracketOfMoments (439/500) lo1834 hi1834 accepted1834
def lo1835b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨46,by decide⟩
def lo1835b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨47,by decide⟩
def lo1835 : CheckedMoment :=
  CheckedMoment.ofBessel lo1835b1 lo1835b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1835b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨51,by decide⟩
def hi1835b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨52,by decide⟩
def hi1835 : CheckedMoment :=
  CheckedMoment.ofBessel hi1835b1 hi1835b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1835 : meanBracketCheck (1757/2000) lo1835 hi1835=true := by decide +kernel
def bracket1835 : MeanBracket := meanBracketOfMoments (1757/2000) lo1835 hi1835 accepted1835
def lo1836b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨56,by decide⟩
def lo1836b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨57,by decide⟩
def lo1836 : CheckedMoment :=
  CheckedMoment.ofBessel lo1836b1 lo1836b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1836b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨61,by decide⟩
def hi1836b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨62,by decide⟩
def hi1836 : CheckedMoment :=
  CheckedMoment.ofBessel hi1836b1 hi1836b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1836 : meanBracketCheck (879/1000) lo1836 hi1836=true := by decide +kernel
def bracket1836 : MeanBracket := meanBracketOfMoments (879/1000) lo1836 hi1836 accepted1836
def lo1837b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨2,by decide⟩
def lo1837b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨3,by decide⟩
def lo1837 : CheckedMoment :=
  CheckedMoment.ofBessel lo1837b1 lo1837b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1837b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨7,by decide⟩
def hi1837b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨8,by decide⟩
def hi1837 : CheckedMoment :=
  CheckedMoment.ofBessel hi1837b1 hi1837b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1837 : meanBracketCheck (1759/2000) lo1837 hi1837=true := by decide +kernel
def bracket1837 : MeanBracket := meanBracketOfMoments (1759/2000) lo1837 hi1837 accepted1837
def lo1838b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨12,by decide⟩
def lo1838b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨13,by decide⟩
def lo1838 : CheckedMoment :=
  CheckedMoment.ofBessel lo1838b1 lo1838b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1838b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨17,by decide⟩
def hi1838b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨18,by decide⟩
def hi1838 : CheckedMoment :=
  CheckedMoment.ofBessel hi1838b1 hi1838b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1838 : meanBracketCheck (22/25) lo1838 hi1838=true := by decide +kernel
def bracket1838 : MeanBracket := meanBracketOfMoments (22/25) lo1838 hi1838 accepted1838
def lo1839b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨22,by decide⟩
def lo1839b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨23,by decide⟩
def lo1839 : CheckedMoment :=
  CheckedMoment.ofBessel lo1839b1 lo1839b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1839b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨27,by decide⟩
def hi1839b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨28,by decide⟩
def hi1839 : CheckedMoment :=
  CheckedMoment.ofBessel hi1839b1 hi1839b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1839 : meanBracketCheck (1761/2000) lo1839 hi1839=true := by decide +kernel
def bracket1839 : MeanBracket := meanBracketOfMoments (1761/2000) lo1839 hi1839 accepted1839
#print axioms bracket1824
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0114
