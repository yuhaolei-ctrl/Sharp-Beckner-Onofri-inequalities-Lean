module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0297
public import BecknerOnofri.EntropyScalarCertificate.Bessel0298
public import BecknerOnofri.EntropyScalarCertificate.Bessel0299

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0119
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1904b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨32,by decide⟩
def lo1904b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨33,by decide⟩
def lo1904 : CheckedMoment :=
  CheckedMoment.ofBessel lo1904b1 lo1904b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1904b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨37,by decide⟩
def hi1904b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨38,by decide⟩
def hi1904 : CheckedMoment :=
  CheckedMoment.ofBessel hi1904b1 hi1904b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1904 : meanBracketCheck (913/1000) lo1904 hi1904=true := by decide +kernel
def bracket1904 : MeanBracket := meanBracketOfMoments (913/1000) lo1904 hi1904 accepted1904
def lo1905b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨42,by decide⟩
def lo1905b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨43,by decide⟩
def lo1905 : CheckedMoment :=
  CheckedMoment.ofBessel lo1905b1 lo1905b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1905b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨47,by decide⟩
def hi1905b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨48,by decide⟩
def hi1905 : CheckedMoment :=
  CheckedMoment.ofBessel hi1905b1 hi1905b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1905 : meanBracketCheck (1827/2000) lo1905 hi1905=true := by decide +kernel
def bracket1905 : MeanBracket := meanBracketOfMoments (1827/2000) lo1905 hi1905 accepted1905
def lo1906b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨52,by decide⟩
def lo1906b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨53,by decide⟩
def lo1906 : CheckedMoment :=
  CheckedMoment.ofBessel lo1906b1 lo1906b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1906b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨57,by decide⟩
def hi1906b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨58,by decide⟩
def hi1906 : CheckedMoment :=
  CheckedMoment.ofBessel hi1906b1 hi1906b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1906 : meanBracketCheck (457/500) lo1906 hi1906=true := by decide +kernel
def bracket1906 : MeanBracket := meanBracketOfMoments (457/500) lo1906 hi1906 accepted1906
def lo1907b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨62,by decide⟩
def lo1907b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨63,by decide⟩
def lo1907 : CheckedMoment :=
  CheckedMoment.ofBessel lo1907b1 lo1907b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1907b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨3,by decide⟩
def hi1907b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨4,by decide⟩
def hi1907 : CheckedMoment :=
  CheckedMoment.ofBessel hi1907b1 hi1907b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1907 : meanBracketCheck (1829/2000) lo1907 hi1907=true := by decide +kernel
def bracket1907 : MeanBracket := meanBracketOfMoments (1829/2000) lo1907 hi1907 accepted1907
def lo1908b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨8,by decide⟩
def lo1908b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨9,by decide⟩
def lo1908 : CheckedMoment :=
  CheckedMoment.ofBessel lo1908b1 lo1908b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1908b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨13,by decide⟩
def hi1908b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨14,by decide⟩
def hi1908 : CheckedMoment :=
  CheckedMoment.ofBessel hi1908b1 hi1908b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1908 : meanBracketCheck (183/200) lo1908 hi1908=true := by decide +kernel
def bracket1908 : MeanBracket := meanBracketOfMoments (183/200) lo1908 hi1908 accepted1908
def lo1909b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨18,by decide⟩
def lo1909b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨19,by decide⟩
def lo1909 : CheckedMoment :=
  CheckedMoment.ofBessel lo1909b1 lo1909b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1909b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨23,by decide⟩
def hi1909b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨24,by decide⟩
def hi1909 : CheckedMoment :=
  CheckedMoment.ofBessel hi1909b1 hi1909b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1909 : meanBracketCheck (1831/2000) lo1909 hi1909=true := by decide +kernel
def bracket1909 : MeanBracket := meanBracketOfMoments (1831/2000) lo1909 hi1909 accepted1909
def lo1910b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨28,by decide⟩
def lo1910b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨29,by decide⟩
def lo1910 : CheckedMoment :=
  CheckedMoment.ofBessel lo1910b1 lo1910b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1910b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨33,by decide⟩
def hi1910b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨34,by decide⟩
def hi1910 : CheckedMoment :=
  CheckedMoment.ofBessel hi1910b1 hi1910b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1910 : meanBracketCheck (229/250) lo1910 hi1910=true := by decide +kernel
def bracket1910 : MeanBracket := meanBracketOfMoments (229/250) lo1910 hi1910 accepted1910
def lo1911b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨38,by decide⟩
def lo1911b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨39,by decide⟩
def lo1911 : CheckedMoment :=
  CheckedMoment.ofBessel lo1911b1 lo1911b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1911b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨43,by decide⟩
def hi1911b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨44,by decide⟩
def hi1911 : CheckedMoment :=
  CheckedMoment.ofBessel hi1911b1 hi1911b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1911 : meanBracketCheck (1833/2000) lo1911 hi1911=true := by decide +kernel
def bracket1911 : MeanBracket := meanBracketOfMoments (1833/2000) lo1911 hi1911 accepted1911
def lo1912b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨48,by decide⟩
def lo1912b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨49,by decide⟩
def lo1912 : CheckedMoment :=
  CheckedMoment.ofBessel lo1912b1 lo1912b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1912b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨53,by decide⟩
def hi1912b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨54,by decide⟩
def hi1912 : CheckedMoment :=
  CheckedMoment.ofBessel hi1912b1 hi1912b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1912 : meanBracketCheck (917/1000) lo1912 hi1912=true := by decide +kernel
def bracket1912 : MeanBracket := meanBracketOfMoments (917/1000) lo1912 hi1912 accepted1912
def lo1913b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨58,by decide⟩
def lo1913b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨59,by decide⟩
def lo1913 : CheckedMoment :=
  CheckedMoment.ofBessel lo1913b1 lo1913b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1913b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨63,by decide⟩
def hi1913b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨0,by decide⟩
def hi1913 : CheckedMoment :=
  CheckedMoment.ofBessel hi1913b1 hi1913b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1913 : meanBracketCheck (367/400) lo1913 hi1913=true := by decide +kernel
def bracket1913 : MeanBracket := meanBracketOfMoments (367/400) lo1913 hi1913 accepted1913
def lo1914b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨4,by decide⟩
def lo1914b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨5,by decide⟩
def lo1914 : CheckedMoment :=
  CheckedMoment.ofBessel lo1914b1 lo1914b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1914b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨9,by decide⟩
def hi1914b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨10,by decide⟩
def hi1914 : CheckedMoment :=
  CheckedMoment.ofBessel hi1914b1 hi1914b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1914 : meanBracketCheck (459/500) lo1914 hi1914=true := by decide +kernel
def bracket1914 : MeanBracket := meanBracketOfMoments (459/500) lo1914 hi1914 accepted1914
def lo1915b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨14,by decide⟩
def lo1915b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨15,by decide⟩
def lo1915 : CheckedMoment :=
  CheckedMoment.ofBessel lo1915b1 lo1915b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1915b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨19,by decide⟩
def hi1915b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨20,by decide⟩
def hi1915 : CheckedMoment :=
  CheckedMoment.ofBessel hi1915b1 hi1915b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1915 : meanBracketCheck (1837/2000) lo1915 hi1915=true := by decide +kernel
def bracket1915 : MeanBracket := meanBracketOfMoments (1837/2000) lo1915 hi1915 accepted1915
def lo1916b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨24,by decide⟩
def lo1916b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨25,by decide⟩
def lo1916 : CheckedMoment :=
  CheckedMoment.ofBessel lo1916b1 lo1916b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1916b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨29,by decide⟩
def hi1916b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨30,by decide⟩
def hi1916 : CheckedMoment :=
  CheckedMoment.ofBessel hi1916b1 hi1916b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1916 : meanBracketCheck (919/1000) lo1916 hi1916=true := by decide +kernel
def bracket1916 : MeanBracket := meanBracketOfMoments (919/1000) lo1916 hi1916 accepted1916
def lo1917b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨34,by decide⟩
def lo1917b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨35,by decide⟩
def lo1917 : CheckedMoment :=
  CheckedMoment.ofBessel lo1917b1 lo1917b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1917b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨39,by decide⟩
def hi1917b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨40,by decide⟩
def hi1917 : CheckedMoment :=
  CheckedMoment.ofBessel hi1917b1 hi1917b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1917 : meanBracketCheck (1839/2000) lo1917 hi1917=true := by decide +kernel
def bracket1917 : MeanBracket := meanBracketOfMoments (1839/2000) lo1917 hi1917 accepted1917
def lo1918b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨44,by decide⟩
def lo1918b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨45,by decide⟩
def lo1918 : CheckedMoment :=
  CheckedMoment.ofBessel lo1918b1 lo1918b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1918b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨49,by decide⟩
def hi1918b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨50,by decide⟩
def hi1918 : CheckedMoment :=
  CheckedMoment.ofBessel hi1918b1 hi1918b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1918 : meanBracketCheck (23/25) lo1918 hi1918=true := by decide +kernel
def bracket1918 : MeanBracket := meanBracketOfMoments (23/25) lo1918 hi1918 accepted1918
def lo1919b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨54,by decide⟩
def lo1919b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨55,by decide⟩
def lo1919 : CheckedMoment :=
  CheckedMoment.ofBessel lo1919b1 lo1919b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1919b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨59,by decide⟩
def hi1919b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨60,by decide⟩
def hi1919 : CheckedMoment :=
  CheckedMoment.ofBessel hi1919b1 hi1919b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1919 : meanBracketCheck (1841/2000) lo1919 hi1919=true := by decide +kernel
def bracket1919 : MeanBracket := meanBracketOfMoments (1841/2000) lo1919 hi1919 accepted1919
#print axioms bracket1904
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0119
