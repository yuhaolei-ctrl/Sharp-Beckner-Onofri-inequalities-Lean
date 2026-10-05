module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0287
public import BecknerOnofri.EntropyScalarCertificate.Bessel0288
public import BecknerOnofri.EntropyScalarCertificate.Bessel0289

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0115
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1840b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨32,by decide⟩
def lo1840b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨33,by decide⟩
def lo1840 : CheckedMoment :=
  CheckedMoment.ofBessel lo1840b1 lo1840b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1840b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨37,by decide⟩
def hi1840b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨38,by decide⟩
def hi1840 : CheckedMoment :=
  CheckedMoment.ofBessel hi1840b1 hi1840b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1840 : meanBracketCheck (881/1000) lo1840 hi1840=true := by decide +kernel
def bracket1840 : MeanBracket := meanBracketOfMoments (881/1000) lo1840 hi1840 accepted1840
def lo1841b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨42,by decide⟩
def lo1841b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨43,by decide⟩
def lo1841 : CheckedMoment :=
  CheckedMoment.ofBessel lo1841b1 lo1841b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1841b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨47,by decide⟩
def hi1841b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨48,by decide⟩
def hi1841 : CheckedMoment :=
  CheckedMoment.ofBessel hi1841b1 hi1841b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1841 : meanBracketCheck (1763/2000) lo1841 hi1841=true := by decide +kernel
def bracket1841 : MeanBracket := meanBracketOfMoments (1763/2000) lo1841 hi1841 accepted1841
def lo1842b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨52,by decide⟩
def lo1842b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨53,by decide⟩
def lo1842 : CheckedMoment :=
  CheckedMoment.ofBessel lo1842b1 lo1842b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1842b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨57,by decide⟩
def hi1842b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨58,by decide⟩
def hi1842 : CheckedMoment :=
  CheckedMoment.ofBessel hi1842b1 hi1842b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1842 : meanBracketCheck (441/500) lo1842 hi1842=true := by decide +kernel
def bracket1842 : MeanBracket := meanBracketOfMoments (441/500) lo1842 hi1842 accepted1842
def lo1843b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨62,by decide⟩
def lo1843b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨63,by decide⟩
def lo1843 : CheckedMoment :=
  CheckedMoment.ofBessel lo1843b1 lo1843b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1843b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨3,by decide⟩
def hi1843b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨4,by decide⟩
def hi1843 : CheckedMoment :=
  CheckedMoment.ofBessel hi1843b1 hi1843b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1843 : meanBracketCheck (353/400) lo1843 hi1843=true := by decide +kernel
def bracket1843 : MeanBracket := meanBracketOfMoments (353/400) lo1843 hi1843 accepted1843
def lo1844b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨8,by decide⟩
def lo1844b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨9,by decide⟩
def lo1844 : CheckedMoment :=
  CheckedMoment.ofBessel lo1844b1 lo1844b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1844b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨13,by decide⟩
def hi1844b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨14,by decide⟩
def hi1844 : CheckedMoment :=
  CheckedMoment.ofBessel hi1844b1 hi1844b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1844 : meanBracketCheck (883/1000) lo1844 hi1844=true := by decide +kernel
def bracket1844 : MeanBracket := meanBracketOfMoments (883/1000) lo1844 hi1844 accepted1844
def lo1845b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨18,by decide⟩
def lo1845b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨19,by decide⟩
def lo1845 : CheckedMoment :=
  CheckedMoment.ofBessel lo1845b1 lo1845b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1845b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨23,by decide⟩
def hi1845b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨24,by decide⟩
def hi1845 : CheckedMoment :=
  CheckedMoment.ofBessel hi1845b1 hi1845b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1845 : meanBracketCheck (1767/2000) lo1845 hi1845=true := by decide +kernel
def bracket1845 : MeanBracket := meanBracketOfMoments (1767/2000) lo1845 hi1845 accepted1845
def lo1846b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨28,by decide⟩
def lo1846b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨29,by decide⟩
def lo1846 : CheckedMoment :=
  CheckedMoment.ofBessel lo1846b1 lo1846b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1846b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨33,by decide⟩
def hi1846b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨34,by decide⟩
def hi1846 : CheckedMoment :=
  CheckedMoment.ofBessel hi1846b1 hi1846b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1846 : meanBracketCheck (221/250) lo1846 hi1846=true := by decide +kernel
def bracket1846 : MeanBracket := meanBracketOfMoments (221/250) lo1846 hi1846 accepted1846
def lo1847b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨38,by decide⟩
def lo1847b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨39,by decide⟩
def lo1847 : CheckedMoment :=
  CheckedMoment.ofBessel lo1847b1 lo1847b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1847b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨43,by decide⟩
def hi1847b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨44,by decide⟩
def hi1847 : CheckedMoment :=
  CheckedMoment.ofBessel hi1847b1 hi1847b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1847 : meanBracketCheck (1769/2000) lo1847 hi1847=true := by decide +kernel
def bracket1847 : MeanBracket := meanBracketOfMoments (1769/2000) lo1847 hi1847 accepted1847
def lo1848b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨48,by decide⟩
def lo1848b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨49,by decide⟩
def lo1848 : CheckedMoment :=
  CheckedMoment.ofBessel lo1848b1 lo1848b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1848b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨53,by decide⟩
def hi1848b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨54,by decide⟩
def hi1848 : CheckedMoment :=
  CheckedMoment.ofBessel hi1848b1 hi1848b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1848 : meanBracketCheck (177/200) lo1848 hi1848=true := by decide +kernel
def bracket1848 : MeanBracket := meanBracketOfMoments (177/200) lo1848 hi1848 accepted1848
def lo1849b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨58,by decide⟩
def lo1849b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨59,by decide⟩
def lo1849 : CheckedMoment :=
  CheckedMoment.ofBessel lo1849b1 lo1849b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1849b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨63,by decide⟩
def hi1849b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨0,by decide⟩
def hi1849 : CheckedMoment :=
  CheckedMoment.ofBessel hi1849b1 hi1849b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1849 : meanBracketCheck (1771/2000) lo1849 hi1849=true := by decide +kernel
def bracket1849 : MeanBracket := meanBracketOfMoments (1771/2000) lo1849 hi1849 accepted1849
def lo1850b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨4,by decide⟩
def lo1850b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨5,by decide⟩
def lo1850 : CheckedMoment :=
  CheckedMoment.ofBessel lo1850b1 lo1850b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1850b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨9,by decide⟩
def hi1850b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨10,by decide⟩
def hi1850 : CheckedMoment :=
  CheckedMoment.ofBessel hi1850b1 hi1850b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1850 : meanBracketCheck (443/500) lo1850 hi1850=true := by decide +kernel
def bracket1850 : MeanBracket := meanBracketOfMoments (443/500) lo1850 hi1850 accepted1850
def lo1851b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨14,by decide⟩
def lo1851b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨15,by decide⟩
def lo1851 : CheckedMoment :=
  CheckedMoment.ofBessel lo1851b1 lo1851b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1851b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨19,by decide⟩
def hi1851b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨20,by decide⟩
def hi1851 : CheckedMoment :=
  CheckedMoment.ofBessel hi1851b1 hi1851b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1851 : meanBracketCheck (1773/2000) lo1851 hi1851=true := by decide +kernel
def bracket1851 : MeanBracket := meanBracketOfMoments (1773/2000) lo1851 hi1851 accepted1851
def lo1852b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨24,by decide⟩
def lo1852b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨25,by decide⟩
def lo1852 : CheckedMoment :=
  CheckedMoment.ofBessel lo1852b1 lo1852b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1852b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨29,by decide⟩
def hi1852b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨30,by decide⟩
def hi1852 : CheckedMoment :=
  CheckedMoment.ofBessel hi1852b1 hi1852b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1852 : meanBracketCheck (887/1000) lo1852 hi1852=true := by decide +kernel
def bracket1852 : MeanBracket := meanBracketOfMoments (887/1000) lo1852 hi1852 accepted1852
def lo1853b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨34,by decide⟩
def lo1853b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨35,by decide⟩
def lo1853 : CheckedMoment :=
  CheckedMoment.ofBessel lo1853b1 lo1853b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1853b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨39,by decide⟩
def hi1853b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨40,by decide⟩
def hi1853 : CheckedMoment :=
  CheckedMoment.ofBessel hi1853b1 hi1853b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1853 : meanBracketCheck (71/80) lo1853 hi1853=true := by decide +kernel
def bracket1853 : MeanBracket := meanBracketOfMoments (71/80) lo1853 hi1853 accepted1853
def lo1854b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨44,by decide⟩
def lo1854b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨45,by decide⟩
def lo1854 : CheckedMoment :=
  CheckedMoment.ofBessel lo1854b1 lo1854b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1854b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨49,by decide⟩
def hi1854b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨50,by decide⟩
def hi1854 : CheckedMoment :=
  CheckedMoment.ofBessel hi1854b1 hi1854b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1854 : meanBracketCheck (111/125) lo1854 hi1854=true := by decide +kernel
def bracket1854 : MeanBracket := meanBracketOfMoments (111/125) lo1854 hi1854 accepted1854
def lo1855b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨54,by decide⟩
def lo1855b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨55,by decide⟩
def lo1855 : CheckedMoment :=
  CheckedMoment.ofBessel lo1855b1 lo1855b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1855b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨59,by decide⟩
def hi1855b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨60,by decide⟩
def hi1855 : CheckedMoment :=
  CheckedMoment.ofBessel hi1855b1 hi1855b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1855 : meanBracketCheck (1777/2000) lo1855 hi1855=true := by decide +kernel
def bracket1855 : MeanBracket := meanBracketOfMoments (1777/2000) lo1855 hi1855 accepted1855
#print axioms bracket1840
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0115
