module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0295
public import BecknerOnofri.EntropyScalarCertificate.Bessel0296
public import BecknerOnofri.EntropyScalarCertificate.Bessel0297

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0118
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1888b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨0,by decide⟩
def lo1888b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨1,by decide⟩
def lo1888 : CheckedMoment :=
  CheckedMoment.ofBessel lo1888b1 lo1888b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1888b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨5,by decide⟩
def hi1888b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨6,by decide⟩
def hi1888 : CheckedMoment :=
  CheckedMoment.ofBessel hi1888b1 hi1888b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1888 : meanBracketCheck (181/200) lo1888 hi1888=true := by decide +kernel
def bracket1888 : MeanBracket := meanBracketOfMoments (181/200) lo1888 hi1888 accepted1888
def lo1889b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨10,by decide⟩
def lo1889b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨11,by decide⟩
def lo1889 : CheckedMoment :=
  CheckedMoment.ofBessel lo1889b1 lo1889b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1889b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨15,by decide⟩
def hi1889b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨16,by decide⟩
def hi1889 : CheckedMoment :=
  CheckedMoment.ofBessel hi1889b1 hi1889b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1889 : meanBracketCheck (1811/2000) lo1889 hi1889=true := by decide +kernel
def bracket1889 : MeanBracket := meanBracketOfMoments (1811/2000) lo1889 hi1889 accepted1889
def lo1890b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨20,by decide⟩
def lo1890b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨21,by decide⟩
def lo1890 : CheckedMoment :=
  CheckedMoment.ofBessel lo1890b1 lo1890b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1890b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨25,by decide⟩
def hi1890b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨26,by decide⟩
def hi1890 : CheckedMoment :=
  CheckedMoment.ofBessel hi1890b1 hi1890b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1890 : meanBracketCheck (453/500) lo1890 hi1890=true := by decide +kernel
def bracket1890 : MeanBracket := meanBracketOfMoments (453/500) lo1890 hi1890 accepted1890
def lo1891b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨30,by decide⟩
def lo1891b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨31,by decide⟩
def lo1891 : CheckedMoment :=
  CheckedMoment.ofBessel lo1891b1 lo1891b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1891b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨35,by decide⟩
def hi1891b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨36,by decide⟩
def hi1891 : CheckedMoment :=
  CheckedMoment.ofBessel hi1891b1 hi1891b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1891 : meanBracketCheck (1813/2000) lo1891 hi1891=true := by decide +kernel
def bracket1891 : MeanBracket := meanBracketOfMoments (1813/2000) lo1891 hi1891 accepted1891
def lo1892b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨40,by decide⟩
def lo1892b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨41,by decide⟩
def lo1892 : CheckedMoment :=
  CheckedMoment.ofBessel lo1892b1 lo1892b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1892b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨45,by decide⟩
def hi1892b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨46,by decide⟩
def hi1892 : CheckedMoment :=
  CheckedMoment.ofBessel hi1892b1 hi1892b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1892 : meanBracketCheck (907/1000) lo1892 hi1892=true := by decide +kernel
def bracket1892 : MeanBracket := meanBracketOfMoments (907/1000) lo1892 hi1892 accepted1892
def lo1893b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨50,by decide⟩
def lo1893b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨51,by decide⟩
def lo1893 : CheckedMoment :=
  CheckedMoment.ofBessel lo1893b1 lo1893b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1893b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨55,by decide⟩
def hi1893b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨56,by decide⟩
def hi1893 : CheckedMoment :=
  CheckedMoment.ofBessel hi1893b1 hi1893b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1893 : meanBracketCheck (363/400) lo1893 hi1893=true := by decide +kernel
def bracket1893 : MeanBracket := meanBracketOfMoments (363/400) lo1893 hi1893 accepted1893
def lo1894b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨60,by decide⟩
def lo1894b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨61,by decide⟩
def lo1894 : CheckedMoment :=
  CheckedMoment.ofBessel lo1894b1 lo1894b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1894b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨1,by decide⟩
def hi1894b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨2,by decide⟩
def hi1894 : CheckedMoment :=
  CheckedMoment.ofBessel hi1894b1 hi1894b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1894 : meanBracketCheck (227/250) lo1894 hi1894=true := by decide +kernel
def bracket1894 : MeanBracket := meanBracketOfMoments (227/250) lo1894 hi1894 accepted1894
def lo1895b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨6,by decide⟩
def lo1895b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨7,by decide⟩
def lo1895 : CheckedMoment :=
  CheckedMoment.ofBessel lo1895b1 lo1895b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1895b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨11,by decide⟩
def hi1895b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨12,by decide⟩
def hi1895 : CheckedMoment :=
  CheckedMoment.ofBessel hi1895b1 hi1895b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1895 : meanBracketCheck (1817/2000) lo1895 hi1895=true := by decide +kernel
def bracket1895 : MeanBracket := meanBracketOfMoments (1817/2000) lo1895 hi1895 accepted1895
def lo1896b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨16,by decide⟩
def lo1896b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨17,by decide⟩
def lo1896 : CheckedMoment :=
  CheckedMoment.ofBessel lo1896b1 lo1896b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1896b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨21,by decide⟩
def hi1896b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨22,by decide⟩
def hi1896 : CheckedMoment :=
  CheckedMoment.ofBessel hi1896b1 hi1896b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1896 : meanBracketCheck (909/1000) lo1896 hi1896=true := by decide +kernel
def bracket1896 : MeanBracket := meanBracketOfMoments (909/1000) lo1896 hi1896 accepted1896
def lo1897b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨26,by decide⟩
def lo1897b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨27,by decide⟩
def lo1897 : CheckedMoment :=
  CheckedMoment.ofBessel lo1897b1 lo1897b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1897b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨31,by decide⟩
def hi1897b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨32,by decide⟩
def hi1897 : CheckedMoment :=
  CheckedMoment.ofBessel hi1897b1 hi1897b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1897 : meanBracketCheck (1819/2000) lo1897 hi1897=true := by decide +kernel
def bracket1897 : MeanBracket := meanBracketOfMoments (1819/2000) lo1897 hi1897 accepted1897
def lo1898b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨36,by decide⟩
def lo1898b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨37,by decide⟩
def lo1898 : CheckedMoment :=
  CheckedMoment.ofBessel lo1898b1 lo1898b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1898b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨41,by decide⟩
def hi1898b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨42,by decide⟩
def hi1898 : CheckedMoment :=
  CheckedMoment.ofBessel hi1898b1 hi1898b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1898 : meanBracketCheck (91/100) lo1898 hi1898=true := by decide +kernel
def bracket1898 : MeanBracket := meanBracketOfMoments (91/100) lo1898 hi1898 accepted1898
def lo1899b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨46,by decide⟩
def lo1899b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨47,by decide⟩
def lo1899 : CheckedMoment :=
  CheckedMoment.ofBessel lo1899b1 lo1899b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1899b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨51,by decide⟩
def hi1899b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨52,by decide⟩
def hi1899 : CheckedMoment :=
  CheckedMoment.ofBessel hi1899b1 hi1899b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1899 : meanBracketCheck (1821/2000) lo1899 hi1899=true := by decide +kernel
def bracket1899 : MeanBracket := meanBracketOfMoments (1821/2000) lo1899 hi1899 accepted1899
def lo1900b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨56,by decide⟩
def lo1900b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨57,by decide⟩
def lo1900 : CheckedMoment :=
  CheckedMoment.ofBessel lo1900b1 lo1900b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1900b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨61,by decide⟩
def hi1900b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨62,by decide⟩
def hi1900 : CheckedMoment :=
  CheckedMoment.ofBessel hi1900b1 hi1900b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1900 : meanBracketCheck (911/1000) lo1900 hi1900=true := by decide +kernel
def bracket1900 : MeanBracket := meanBracketOfMoments (911/1000) lo1900 hi1900 accepted1900
def lo1901b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨2,by decide⟩
def lo1901b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨3,by decide⟩
def lo1901 : CheckedMoment :=
  CheckedMoment.ofBessel lo1901b1 lo1901b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1901b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨7,by decide⟩
def hi1901b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨8,by decide⟩
def hi1901 : CheckedMoment :=
  CheckedMoment.ofBessel hi1901b1 hi1901b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1901 : meanBracketCheck (1823/2000) lo1901 hi1901=true := by decide +kernel
def bracket1901 : MeanBracket := meanBracketOfMoments (1823/2000) lo1901 hi1901 accepted1901
def lo1902b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨12,by decide⟩
def lo1902b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨13,by decide⟩
def lo1902 : CheckedMoment :=
  CheckedMoment.ofBessel lo1902b1 lo1902b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1902b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨17,by decide⟩
def hi1902b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨18,by decide⟩
def hi1902 : CheckedMoment :=
  CheckedMoment.ofBessel hi1902b1 hi1902b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1902 : meanBracketCheck (114/125) lo1902 hi1902=true := by decide +kernel
def bracket1902 : MeanBracket := meanBracketOfMoments (114/125) lo1902 hi1902 accepted1902
def lo1903b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨22,by decide⟩
def lo1903b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨23,by decide⟩
def lo1903 : CheckedMoment :=
  CheckedMoment.ofBessel lo1903b1 lo1903b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1903b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨27,by decide⟩
def hi1903b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨28,by decide⟩
def hi1903 : CheckedMoment :=
  CheckedMoment.ofBessel hi1903b1 hi1903b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1903 : meanBracketCheck (73/80) lo1903 hi1903=true := by decide +kernel
def bracket1903 : MeanBracket := meanBracketOfMoments (73/80) lo1903 hi1903 accepted1903
#print axioms bracket1888
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0118
