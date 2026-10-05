import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0300
import BecknerOnofri.EntropyScalarCertificate.Bessel0301
import BecknerOnofri.EntropyScalarCertificate.Bessel0302
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0120
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1920b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨0,by decide⟩
def lo1920b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨1,by decide⟩
def lo1920 : CheckedMoment :=
  CheckedMoment.ofBessel lo1920b1 lo1920b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1920b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨5,by decide⟩
def hi1920b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨6,by decide⟩
def hi1920 : CheckedMoment :=
  CheckedMoment.ofBessel hi1920b1 hi1920b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1920 : meanBracketCheck (921/1000) lo1920 hi1920=true := by decide +kernel
def bracket1920 : MeanBracket := meanBracketOfMoments (921/1000) lo1920 hi1920 accepted1920
def lo1921b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨10,by decide⟩
def lo1921b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨11,by decide⟩
def lo1921 : CheckedMoment :=
  CheckedMoment.ofBessel lo1921b1 lo1921b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1921b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨15,by decide⟩
def hi1921b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨16,by decide⟩
def hi1921 : CheckedMoment :=
  CheckedMoment.ofBessel hi1921b1 hi1921b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1921 : meanBracketCheck (1843/2000) lo1921 hi1921=true := by decide +kernel
def bracket1921 : MeanBracket := meanBracketOfMoments (1843/2000) lo1921 hi1921 accepted1921
def lo1922b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨20,by decide⟩
def lo1922b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨21,by decide⟩
def lo1922 : CheckedMoment :=
  CheckedMoment.ofBessel lo1922b1 lo1922b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1922b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨25,by decide⟩
def hi1922b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨26,by decide⟩
def hi1922 : CheckedMoment :=
  CheckedMoment.ofBessel hi1922b1 hi1922b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1922 : meanBracketCheck (461/500) lo1922 hi1922=true := by decide +kernel
def bracket1922 : MeanBracket := meanBracketOfMoments (461/500) lo1922 hi1922 accepted1922
def lo1923b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨30,by decide⟩
def lo1923b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨31,by decide⟩
def lo1923 : CheckedMoment :=
  CheckedMoment.ofBessel lo1923b1 lo1923b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1923b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨35,by decide⟩
def hi1923b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨36,by decide⟩
def hi1923 : CheckedMoment :=
  CheckedMoment.ofBessel hi1923b1 hi1923b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1923 : meanBracketCheck (369/400) lo1923 hi1923=true := by decide +kernel
def bracket1923 : MeanBracket := meanBracketOfMoments (369/400) lo1923 hi1923 accepted1923
def lo1924b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨40,by decide⟩
def lo1924b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨41,by decide⟩
def lo1924 : CheckedMoment :=
  CheckedMoment.ofBessel lo1924b1 lo1924b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1924b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨45,by decide⟩
def hi1924b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨46,by decide⟩
def hi1924 : CheckedMoment :=
  CheckedMoment.ofBessel hi1924b1 hi1924b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1924 : meanBracketCheck (923/1000) lo1924 hi1924=true := by decide +kernel
def bracket1924 : MeanBracket := meanBracketOfMoments (923/1000) lo1924 hi1924 accepted1924
def lo1925b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨50,by decide⟩
def lo1925b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨51,by decide⟩
def lo1925 : CheckedMoment :=
  CheckedMoment.ofBessel lo1925b1 lo1925b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1925b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨55,by decide⟩
def hi1925b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨56,by decide⟩
def hi1925 : CheckedMoment :=
  CheckedMoment.ofBessel hi1925b1 hi1925b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1925 : meanBracketCheck (1847/2000) lo1925 hi1925=true := by decide +kernel
def bracket1925 : MeanBracket := meanBracketOfMoments (1847/2000) lo1925 hi1925 accepted1925
def lo1926b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨60,by decide⟩
def lo1926b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨61,by decide⟩
def lo1926 : CheckedMoment :=
  CheckedMoment.ofBessel lo1926b1 lo1926b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1926b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨1,by decide⟩
def hi1926b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨2,by decide⟩
def hi1926 : CheckedMoment :=
  CheckedMoment.ofBessel hi1926b1 hi1926b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1926 : meanBracketCheck (231/250) lo1926 hi1926=true := by decide +kernel
def bracket1926 : MeanBracket := meanBracketOfMoments (231/250) lo1926 hi1926 accepted1926
def lo1927b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨6,by decide⟩
def lo1927b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨7,by decide⟩
def lo1927 : CheckedMoment :=
  CheckedMoment.ofBessel lo1927b1 lo1927b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1927b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨11,by decide⟩
def hi1927b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨12,by decide⟩
def hi1927 : CheckedMoment :=
  CheckedMoment.ofBessel hi1927b1 hi1927b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1927 : meanBracketCheck (1849/2000) lo1927 hi1927=true := by decide +kernel
def bracket1927 : MeanBracket := meanBracketOfMoments (1849/2000) lo1927 hi1927 accepted1927
def lo1928b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨16,by decide⟩
def lo1928b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨17,by decide⟩
def lo1928 : CheckedMoment :=
  CheckedMoment.ofBessel lo1928b1 lo1928b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1928b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨21,by decide⟩
def hi1928b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨22,by decide⟩
def hi1928 : CheckedMoment :=
  CheckedMoment.ofBessel hi1928b1 hi1928b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1928 : meanBracketCheck (37/40) lo1928 hi1928=true := by decide +kernel
def bracket1928 : MeanBracket := meanBracketOfMoments (37/40) lo1928 hi1928 accepted1928
def lo1929b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨26,by decide⟩
def lo1929b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨27,by decide⟩
def lo1929 : CheckedMoment :=
  CheckedMoment.ofBessel lo1929b1 lo1929b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1929b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨31,by decide⟩
def hi1929b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨32,by decide⟩
def hi1929 : CheckedMoment :=
  CheckedMoment.ofBessel hi1929b1 hi1929b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1929 : meanBracketCheck (1851/2000) lo1929 hi1929=true := by decide +kernel
def bracket1929 : MeanBracket := meanBracketOfMoments (1851/2000) lo1929 hi1929 accepted1929
def lo1930b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨36,by decide⟩
def lo1930b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨37,by decide⟩
def lo1930 : CheckedMoment :=
  CheckedMoment.ofBessel lo1930b1 lo1930b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1930b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨41,by decide⟩
def hi1930b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨42,by decide⟩
def hi1930 : CheckedMoment :=
  CheckedMoment.ofBessel hi1930b1 hi1930b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1930 : meanBracketCheck (463/500) lo1930 hi1930=true := by decide +kernel
def bracket1930 : MeanBracket := meanBracketOfMoments (463/500) lo1930 hi1930 accepted1930
def lo1931b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨46,by decide⟩
def lo1931b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨47,by decide⟩
def lo1931 : CheckedMoment :=
  CheckedMoment.ofBessel lo1931b1 lo1931b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1931b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨51,by decide⟩
def hi1931b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨52,by decide⟩
def hi1931 : CheckedMoment :=
  CheckedMoment.ofBessel hi1931b1 hi1931b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1931 : meanBracketCheck (1853/2000) lo1931 hi1931=true := by decide +kernel
def bracket1931 : MeanBracket := meanBracketOfMoments (1853/2000) lo1931 hi1931 accepted1931
def lo1932b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨56,by decide⟩
def lo1932b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨57,by decide⟩
def lo1932 : CheckedMoment :=
  CheckedMoment.ofBessel lo1932b1 lo1932b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1932b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨61,by decide⟩
def hi1932b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨62,by decide⟩
def hi1932 : CheckedMoment :=
  CheckedMoment.ofBessel hi1932b1 hi1932b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1932 : meanBracketCheck (927/1000) lo1932 hi1932=true := by decide +kernel
def bracket1932 : MeanBracket := meanBracketOfMoments (927/1000) lo1932 hi1932 accepted1932
def lo1933b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨2,by decide⟩
def lo1933b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨3,by decide⟩
def lo1933 : CheckedMoment :=
  CheckedMoment.ofBessel lo1933b1 lo1933b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1933b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨7,by decide⟩
def hi1933b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨8,by decide⟩
def hi1933 : CheckedMoment :=
  CheckedMoment.ofBessel hi1933b1 hi1933b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1933 : meanBracketCheck (371/400) lo1933 hi1933=true := by decide +kernel
def bracket1933 : MeanBracket := meanBracketOfMoments (371/400) lo1933 hi1933 accepted1933
def lo1934b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨12,by decide⟩
def lo1934b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨13,by decide⟩
def lo1934 : CheckedMoment :=
  CheckedMoment.ofBessel lo1934b1 lo1934b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1934b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨17,by decide⟩
def hi1934b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨18,by decide⟩
def hi1934 : CheckedMoment :=
  CheckedMoment.ofBessel hi1934b1 hi1934b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1934 : meanBracketCheck (116/125) lo1934 hi1934=true := by decide +kernel
def bracket1934 : MeanBracket := meanBracketOfMoments (116/125) lo1934 hi1934 accepted1934
def lo1935b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨22,by decide⟩
def lo1935b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨23,by decide⟩
def lo1935 : CheckedMoment :=
  CheckedMoment.ofBessel lo1935b1 lo1935b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1935b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨27,by decide⟩
def hi1935b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨28,by decide⟩
def hi1935 : CheckedMoment :=
  CheckedMoment.ofBessel hi1935b1 hi1935b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1935 : meanBracketCheck (1857/2000) lo1935 hi1935=true := by decide +kernel
def bracket1935 : MeanBracket := meanBracketOfMoments (1857/2000) lo1935 hi1935 accepted1935
#print axioms bracket1920
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0120
