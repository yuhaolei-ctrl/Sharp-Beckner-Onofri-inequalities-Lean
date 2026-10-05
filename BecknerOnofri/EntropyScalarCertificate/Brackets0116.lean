import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0290
import BecknerOnofri.EntropyScalarCertificate.Bessel0291
import BecknerOnofri.EntropyScalarCertificate.Bessel0292
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0116
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1856b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨0,by decide⟩
def lo1856b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨1,by decide⟩
def lo1856 : CheckedMoment :=
  CheckedMoment.ofBessel lo1856b1 lo1856b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1856b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨5,by decide⟩
def hi1856b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨6,by decide⟩
def hi1856 : CheckedMoment :=
  CheckedMoment.ofBessel hi1856b1 hi1856b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1856 : meanBracketCheck (889/1000) lo1856 hi1856=true := by decide +kernel
def bracket1856 : MeanBracket := meanBracketOfMoments (889/1000) lo1856 hi1856 accepted1856
def lo1857b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨10,by decide⟩
def lo1857b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨11,by decide⟩
def lo1857 : CheckedMoment :=
  CheckedMoment.ofBessel lo1857b1 lo1857b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1857b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨15,by decide⟩
def hi1857b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨16,by decide⟩
def hi1857 : CheckedMoment :=
  CheckedMoment.ofBessel hi1857b1 hi1857b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1857 : meanBracketCheck (1779/2000) lo1857 hi1857=true := by decide +kernel
def bracket1857 : MeanBracket := meanBracketOfMoments (1779/2000) lo1857 hi1857 accepted1857
def lo1858b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨20,by decide⟩
def lo1858b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨21,by decide⟩
def lo1858 : CheckedMoment :=
  CheckedMoment.ofBessel lo1858b1 lo1858b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1858b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨25,by decide⟩
def hi1858b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨26,by decide⟩
def hi1858 : CheckedMoment :=
  CheckedMoment.ofBessel hi1858b1 hi1858b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1858 : meanBracketCheck (89/100) lo1858 hi1858=true := by decide +kernel
def bracket1858 : MeanBracket := meanBracketOfMoments (89/100) lo1858 hi1858 accepted1858
def lo1859b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨30,by decide⟩
def lo1859b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨31,by decide⟩
def lo1859 : CheckedMoment :=
  CheckedMoment.ofBessel lo1859b1 lo1859b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1859b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨35,by decide⟩
def hi1859b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨36,by decide⟩
def hi1859 : CheckedMoment :=
  CheckedMoment.ofBessel hi1859b1 hi1859b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1859 : meanBracketCheck (1781/2000) lo1859 hi1859=true := by decide +kernel
def bracket1859 : MeanBracket := meanBracketOfMoments (1781/2000) lo1859 hi1859 accepted1859
def lo1860b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨40,by decide⟩
def lo1860b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨41,by decide⟩
def lo1860 : CheckedMoment :=
  CheckedMoment.ofBessel lo1860b1 lo1860b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1860b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨45,by decide⟩
def hi1860b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨46,by decide⟩
def hi1860 : CheckedMoment :=
  CheckedMoment.ofBessel hi1860b1 hi1860b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1860 : meanBracketCheck (891/1000) lo1860 hi1860=true := by decide +kernel
def bracket1860 : MeanBracket := meanBracketOfMoments (891/1000) lo1860 hi1860 accepted1860
def lo1861b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨50,by decide⟩
def lo1861b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨51,by decide⟩
def lo1861 : CheckedMoment :=
  CheckedMoment.ofBessel lo1861b1 lo1861b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1861b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨55,by decide⟩
def hi1861b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨56,by decide⟩
def hi1861 : CheckedMoment :=
  CheckedMoment.ofBessel hi1861b1 hi1861b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1861 : meanBracketCheck (1783/2000) lo1861 hi1861=true := by decide +kernel
def bracket1861 : MeanBracket := meanBracketOfMoments (1783/2000) lo1861 hi1861 accepted1861
def lo1862b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨60,by decide⟩
def lo1862b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨61,by decide⟩
def lo1862 : CheckedMoment :=
  CheckedMoment.ofBessel lo1862b1 lo1862b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1862b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨1,by decide⟩
def hi1862b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨2,by decide⟩
def hi1862 : CheckedMoment :=
  CheckedMoment.ofBessel hi1862b1 hi1862b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1862 : meanBracketCheck (223/250) lo1862 hi1862=true := by decide +kernel
def bracket1862 : MeanBracket := meanBracketOfMoments (223/250) lo1862 hi1862 accepted1862
def lo1863b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨6,by decide⟩
def lo1863b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨7,by decide⟩
def lo1863 : CheckedMoment :=
  CheckedMoment.ofBessel lo1863b1 lo1863b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1863b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨11,by decide⟩
def hi1863b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨12,by decide⟩
def hi1863 : CheckedMoment :=
  CheckedMoment.ofBessel hi1863b1 hi1863b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1863 : meanBracketCheck (357/400) lo1863 hi1863=true := by decide +kernel
def bracket1863 : MeanBracket := meanBracketOfMoments (357/400) lo1863 hi1863 accepted1863
def lo1864b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨16,by decide⟩
def lo1864b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨17,by decide⟩
def lo1864 : CheckedMoment :=
  CheckedMoment.ofBessel lo1864b1 lo1864b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1864b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨21,by decide⟩
def hi1864b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨22,by decide⟩
def hi1864 : CheckedMoment :=
  CheckedMoment.ofBessel hi1864b1 hi1864b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1864 : meanBracketCheck (893/1000) lo1864 hi1864=true := by decide +kernel
def bracket1864 : MeanBracket := meanBracketOfMoments (893/1000) lo1864 hi1864 accepted1864
def lo1865b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨26,by decide⟩
def lo1865b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨27,by decide⟩
def lo1865 : CheckedMoment :=
  CheckedMoment.ofBessel lo1865b1 lo1865b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1865b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨31,by decide⟩
def hi1865b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨32,by decide⟩
def hi1865 : CheckedMoment :=
  CheckedMoment.ofBessel hi1865b1 hi1865b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1865 : meanBracketCheck (1787/2000) lo1865 hi1865=true := by decide +kernel
def bracket1865 : MeanBracket := meanBracketOfMoments (1787/2000) lo1865 hi1865 accepted1865
def lo1866b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨36,by decide⟩
def lo1866b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨37,by decide⟩
def lo1866 : CheckedMoment :=
  CheckedMoment.ofBessel lo1866b1 lo1866b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1866b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨41,by decide⟩
def hi1866b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨42,by decide⟩
def hi1866 : CheckedMoment :=
  CheckedMoment.ofBessel hi1866b1 hi1866b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1866 : meanBracketCheck (447/500) lo1866 hi1866=true := by decide +kernel
def bracket1866 : MeanBracket := meanBracketOfMoments (447/500) lo1866 hi1866 accepted1866
def lo1867b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨46,by decide⟩
def lo1867b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨47,by decide⟩
def lo1867 : CheckedMoment :=
  CheckedMoment.ofBessel lo1867b1 lo1867b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1867b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨51,by decide⟩
def hi1867b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨52,by decide⟩
def hi1867 : CheckedMoment :=
  CheckedMoment.ofBessel hi1867b1 hi1867b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1867 : meanBracketCheck (1789/2000) lo1867 hi1867=true := by decide +kernel
def bracket1867 : MeanBracket := meanBracketOfMoments (1789/2000) lo1867 hi1867 accepted1867
def lo1868b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨56,by decide⟩
def lo1868b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨57,by decide⟩
def lo1868 : CheckedMoment :=
  CheckedMoment.ofBessel lo1868b1 lo1868b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1868b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨61,by decide⟩
def hi1868b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨62,by decide⟩
def hi1868 : CheckedMoment :=
  CheckedMoment.ofBessel hi1868b1 hi1868b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1868 : meanBracketCheck (179/200) lo1868 hi1868=true := by decide +kernel
def bracket1868 : MeanBracket := meanBracketOfMoments (179/200) lo1868 hi1868 accepted1868
def lo1869b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨2,by decide⟩
def lo1869b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨3,by decide⟩
def lo1869 : CheckedMoment :=
  CheckedMoment.ofBessel lo1869b1 lo1869b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1869b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨7,by decide⟩
def hi1869b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨8,by decide⟩
def hi1869 : CheckedMoment :=
  CheckedMoment.ofBessel hi1869b1 hi1869b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1869 : meanBracketCheck (1791/2000) lo1869 hi1869=true := by decide +kernel
def bracket1869 : MeanBracket := meanBracketOfMoments (1791/2000) lo1869 hi1869 accepted1869
def lo1870b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨12,by decide⟩
def lo1870b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨13,by decide⟩
def lo1870 : CheckedMoment :=
  CheckedMoment.ofBessel lo1870b1 lo1870b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1870b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨17,by decide⟩
def hi1870b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨18,by decide⟩
def hi1870 : CheckedMoment :=
  CheckedMoment.ofBessel hi1870b1 hi1870b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1870 : meanBracketCheck (112/125) lo1870 hi1870=true := by decide +kernel
def bracket1870 : MeanBracket := meanBracketOfMoments (112/125) lo1870 hi1870 accepted1870
def lo1871b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨22,by decide⟩
def lo1871b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨23,by decide⟩
def lo1871 : CheckedMoment :=
  CheckedMoment.ofBessel lo1871b1 lo1871b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1871b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨27,by decide⟩
def hi1871b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨28,by decide⟩
def hi1871 : CheckedMoment :=
  CheckedMoment.ofBessel hi1871b1 hi1871b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1871 : meanBracketCheck (1793/2000) lo1871 hi1871=true := by decide +kernel
def bracket1871 : MeanBracket := meanBracketOfMoments (1793/2000) lo1871 hi1871 accepted1871
#print axioms bracket1856
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0116
