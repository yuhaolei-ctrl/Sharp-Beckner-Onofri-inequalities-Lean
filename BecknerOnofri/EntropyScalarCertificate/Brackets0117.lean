module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0292
public import BecknerOnofri.EntropyScalarCertificate.Bessel0293
public import BecknerOnofri.EntropyScalarCertificate.Bessel0294

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0117
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1872b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨32,by decide⟩
def lo1872b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨33,by decide⟩
def lo1872 : CheckedMoment :=
  CheckedMoment.ofBessel lo1872b1 lo1872b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1872b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨37,by decide⟩
def hi1872b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨38,by decide⟩
def hi1872 : CheckedMoment :=
  CheckedMoment.ofBessel hi1872b1 hi1872b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1872 : meanBracketCheck (897/1000) lo1872 hi1872=true := by decide +kernel
def bracket1872 : MeanBracket := meanBracketOfMoments (897/1000) lo1872 hi1872 accepted1872
def lo1873b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨42,by decide⟩
def lo1873b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨43,by decide⟩
def lo1873 : CheckedMoment :=
  CheckedMoment.ofBessel lo1873b1 lo1873b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1873b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨47,by decide⟩
def hi1873b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨48,by decide⟩
def hi1873 : CheckedMoment :=
  CheckedMoment.ofBessel hi1873b1 hi1873b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1873 : meanBracketCheck (359/400) lo1873 hi1873=true := by decide +kernel
def bracket1873 : MeanBracket := meanBracketOfMoments (359/400) lo1873 hi1873 accepted1873
def lo1874b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨52,by decide⟩
def lo1874b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨53,by decide⟩
def lo1874 : CheckedMoment :=
  CheckedMoment.ofBessel lo1874b1 lo1874b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1874b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨57,by decide⟩
def hi1874b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨58,by decide⟩
def hi1874 : CheckedMoment :=
  CheckedMoment.ofBessel hi1874b1 hi1874b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1874 : meanBracketCheck (449/500) lo1874 hi1874=true := by decide +kernel
def bracket1874 : MeanBracket := meanBracketOfMoments (449/500) lo1874 hi1874 accepted1874
def lo1875b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨62,by decide⟩
def lo1875b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨63,by decide⟩
def lo1875 : CheckedMoment :=
  CheckedMoment.ofBessel lo1875b1 lo1875b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1875b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨3,by decide⟩
def hi1875b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨4,by decide⟩
def hi1875 : CheckedMoment :=
  CheckedMoment.ofBessel hi1875b1 hi1875b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1875 : meanBracketCheck (1797/2000) lo1875 hi1875=true := by decide +kernel
def bracket1875 : MeanBracket := meanBracketOfMoments (1797/2000) lo1875 hi1875 accepted1875
def lo1876b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨8,by decide⟩
def lo1876b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨9,by decide⟩
def lo1876 : CheckedMoment :=
  CheckedMoment.ofBessel lo1876b1 lo1876b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1876b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨13,by decide⟩
def hi1876b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨14,by decide⟩
def hi1876 : CheckedMoment :=
  CheckedMoment.ofBessel hi1876b1 hi1876b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1876 : meanBracketCheck (899/1000) lo1876 hi1876=true := by decide +kernel
def bracket1876 : MeanBracket := meanBracketOfMoments (899/1000) lo1876 hi1876 accepted1876
def lo1877b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨18,by decide⟩
def lo1877b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨19,by decide⟩
def lo1877 : CheckedMoment :=
  CheckedMoment.ofBessel lo1877b1 lo1877b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1877b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨23,by decide⟩
def hi1877b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨24,by decide⟩
def hi1877 : CheckedMoment :=
  CheckedMoment.ofBessel hi1877b1 hi1877b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1877 : meanBracketCheck (1799/2000) lo1877 hi1877=true := by decide +kernel
def bracket1877 : MeanBracket := meanBracketOfMoments (1799/2000) lo1877 hi1877 accepted1877
def lo1878b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨28,by decide⟩
def lo1878b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨29,by decide⟩
def lo1878 : CheckedMoment :=
  CheckedMoment.ofBessel lo1878b1 lo1878b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1878b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨33,by decide⟩
def hi1878b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨34,by decide⟩
def hi1878 : CheckedMoment :=
  CheckedMoment.ofBessel hi1878b1 hi1878b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1878 : meanBracketCheck (9/10) lo1878 hi1878=true := by decide +kernel
def bracket1878 : MeanBracket := meanBracketOfMoments (9/10) lo1878 hi1878 accepted1878
def lo1879b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨38,by decide⟩
def lo1879b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨39,by decide⟩
def lo1879 : CheckedMoment :=
  CheckedMoment.ofBessel lo1879b1 lo1879b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1879b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨43,by decide⟩
def hi1879b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨44,by decide⟩
def hi1879 : CheckedMoment :=
  CheckedMoment.ofBessel hi1879b1 hi1879b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1879 : meanBracketCheck (1801/2000) lo1879 hi1879=true := by decide +kernel
def bracket1879 : MeanBracket := meanBracketOfMoments (1801/2000) lo1879 hi1879 accepted1879
def lo1880b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨48,by decide⟩
def lo1880b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨49,by decide⟩
def lo1880 : CheckedMoment :=
  CheckedMoment.ofBessel lo1880b1 lo1880b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1880b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨53,by decide⟩
def hi1880b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨54,by decide⟩
def hi1880 : CheckedMoment :=
  CheckedMoment.ofBessel hi1880b1 hi1880b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1880 : meanBracketCheck (901/1000) lo1880 hi1880=true := by decide +kernel
def bracket1880 : MeanBracket := meanBracketOfMoments (901/1000) lo1880 hi1880 accepted1880
def lo1881b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨58,by decide⟩
def lo1881b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨59,by decide⟩
def lo1881 : CheckedMoment :=
  CheckedMoment.ofBessel lo1881b1 lo1881b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1881b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨63,by decide⟩
def hi1881b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨0,by decide⟩
def hi1881 : CheckedMoment :=
  CheckedMoment.ofBessel hi1881b1 hi1881b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1881 : meanBracketCheck (1803/2000) lo1881 hi1881=true := by decide +kernel
def bracket1881 : MeanBracket := meanBracketOfMoments (1803/2000) lo1881 hi1881 accepted1881
def lo1882b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨4,by decide⟩
def lo1882b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨5,by decide⟩
def lo1882 : CheckedMoment :=
  CheckedMoment.ofBessel lo1882b1 lo1882b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1882b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨9,by decide⟩
def hi1882b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨10,by decide⟩
def hi1882 : CheckedMoment :=
  CheckedMoment.ofBessel hi1882b1 hi1882b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1882 : meanBracketCheck (451/500) lo1882 hi1882=true := by decide +kernel
def bracket1882 : MeanBracket := meanBracketOfMoments (451/500) lo1882 hi1882 accepted1882
def lo1883b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨14,by decide⟩
def lo1883b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨15,by decide⟩
def lo1883 : CheckedMoment :=
  CheckedMoment.ofBessel lo1883b1 lo1883b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1883b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨19,by decide⟩
def hi1883b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨20,by decide⟩
def hi1883 : CheckedMoment :=
  CheckedMoment.ofBessel hi1883b1 hi1883b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1883 : meanBracketCheck (361/400) lo1883 hi1883=true := by decide +kernel
def bracket1883 : MeanBracket := meanBracketOfMoments (361/400) lo1883 hi1883 accepted1883
def lo1884b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨24,by decide⟩
def lo1884b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨25,by decide⟩
def lo1884 : CheckedMoment :=
  CheckedMoment.ofBessel lo1884b1 lo1884b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1884b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨29,by decide⟩
def hi1884b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨30,by decide⟩
def hi1884 : CheckedMoment :=
  CheckedMoment.ofBessel hi1884b1 hi1884b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1884 : meanBracketCheck (903/1000) lo1884 hi1884=true := by decide +kernel
def bracket1884 : MeanBracket := meanBracketOfMoments (903/1000) lo1884 hi1884 accepted1884
def lo1885b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨34,by decide⟩
def lo1885b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨35,by decide⟩
def lo1885 : CheckedMoment :=
  CheckedMoment.ofBessel lo1885b1 lo1885b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1885b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨39,by decide⟩
def hi1885b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨40,by decide⟩
def hi1885 : CheckedMoment :=
  CheckedMoment.ofBessel hi1885b1 hi1885b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1885 : meanBracketCheck (1807/2000) lo1885 hi1885=true := by decide +kernel
def bracket1885 : MeanBracket := meanBracketOfMoments (1807/2000) lo1885 hi1885 accepted1885
def lo1886b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨44,by decide⟩
def lo1886b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨45,by decide⟩
def lo1886 : CheckedMoment :=
  CheckedMoment.ofBessel lo1886b1 lo1886b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1886b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨49,by decide⟩
def hi1886b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨50,by decide⟩
def hi1886 : CheckedMoment :=
  CheckedMoment.ofBessel hi1886b1 hi1886b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1886 : meanBracketCheck (113/125) lo1886 hi1886=true := by decide +kernel
def bracket1886 : MeanBracket := meanBracketOfMoments (113/125) lo1886 hi1886 accepted1886
def lo1887b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨54,by decide⟩
def lo1887b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨55,by decide⟩
def lo1887 : CheckedMoment :=
  CheckedMoment.ofBessel lo1887b1 lo1887b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1887b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨59,by decide⟩
def hi1887b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨60,by decide⟩
def hi1887 : CheckedMoment :=
  CheckedMoment.ofBessel hi1887b1 hi1887b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1887 : meanBracketCheck (1809/2000) lo1887 hi1887=true := by decide +kernel
def bracket1887 : MeanBracket := meanBracketOfMoments (1809/2000) lo1887 hi1887 accepted1887
#print axioms bracket1872
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0117
