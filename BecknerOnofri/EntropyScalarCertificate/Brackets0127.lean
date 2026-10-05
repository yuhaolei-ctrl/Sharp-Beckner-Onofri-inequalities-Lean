import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0317
import BecknerOnofri.EntropyScalarCertificate.Bessel0318
import BecknerOnofri.EntropyScalarCertificate.Bessel0319
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0127
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2032b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨32,by decide⟩
def lo2032b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨33,by decide⟩
def lo2032 : CheckedMoment :=
  CheckedMoment.ofBessel lo2032b1 lo2032b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2032b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨37,by decide⟩
def hi2032b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨38,by decide⟩
def hi2032 : CheckedMoment :=
  CheckedMoment.ofBessel hi2032b1 hi2032b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2032 : meanBracketCheck (4777/5000) lo2032 hi2032=true := by decide +kernel
def bracket2032 : MeanBracket := meanBracketOfMoments (4777/5000) lo2032 hi2032 accepted2032
def lo2033b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨42,by decide⟩
def lo2033b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨43,by decide⟩
def lo2033 : CheckedMoment :=
  CheckedMoment.ofBessel lo2033b1 lo2033b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2033b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨47,by decide⟩
def hi2033b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨48,by decide⟩
def hi2033 : CheckedMoment :=
  CheckedMoment.ofBessel hi2033b1 hi2033b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2033 : meanBracketCheck (1911/2000) lo2033 hi2033=true := by decide +kernel
def bracket2033 : MeanBracket := meanBracketOfMoments (1911/2000) lo2033 hi2033 accepted2033
def lo2034b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨52,by decide⟩
def lo2034b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨53,by decide⟩
def lo2034 : CheckedMoment :=
  CheckedMoment.ofBessel lo2034b1 lo2034b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2034b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨57,by decide⟩
def hi2034b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨58,by decide⟩
def hi2034 : CheckedMoment :=
  CheckedMoment.ofBessel hi2034b1 hi2034b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2034 : meanBracketCheck (2389/2500) lo2034 hi2034=true := by decide +kernel
def bracket2034 : MeanBracket := meanBracketOfMoments (2389/2500) lo2034 hi2034 accepted2034
def lo2035b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨62,by decide⟩
def lo2035b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨63,by decide⟩
def lo2035 : CheckedMoment :=
  CheckedMoment.ofBessel lo2035b1 lo2035b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2035b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨3,by decide⟩
def hi2035b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨4,by decide⟩
def hi2035 : CheckedMoment :=
  CheckedMoment.ofBessel hi2035b1 hi2035b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2035 : meanBracketCheck (9557/10000) lo2035 hi2035=true := by decide +kernel
def bracket2035 : MeanBracket := meanBracketOfMoments (9557/10000) lo2035 hi2035 accepted2035
def lo2036b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨8,by decide⟩
def lo2036b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨9,by decide⟩
def lo2036 : CheckedMoment :=
  CheckedMoment.ofBessel lo2036b1 lo2036b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2036b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨13,by decide⟩
def hi2036b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨14,by decide⟩
def hi2036 : CheckedMoment :=
  CheckedMoment.ofBessel hi2036b1 hi2036b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2036 : meanBracketCheck (4779/5000) lo2036 hi2036=true := by decide +kernel
def bracket2036 : MeanBracket := meanBracketOfMoments (4779/5000) lo2036 hi2036 accepted2036
def lo2037b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨18,by decide⟩
def lo2037b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨19,by decide⟩
def lo2037 : CheckedMoment :=
  CheckedMoment.ofBessel lo2037b1 lo2037b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2037b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨23,by decide⟩
def hi2037b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨24,by decide⟩
def hi2037 : CheckedMoment :=
  CheckedMoment.ofBessel hi2037b1 hi2037b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2037 : meanBracketCheck (9559/10000) lo2037 hi2037=true := by decide +kernel
def bracket2037 : MeanBracket := meanBracketOfMoments (9559/10000) lo2037 hi2037 accepted2037
def lo2038b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨28,by decide⟩
def lo2038b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨29,by decide⟩
def lo2038 : CheckedMoment :=
  CheckedMoment.ofBessel lo2038b1 lo2038b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2038b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨33,by decide⟩
def hi2038b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨34,by decide⟩
def hi2038 : CheckedMoment :=
  CheckedMoment.ofBessel hi2038b1 hi2038b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2038 : meanBracketCheck (239/250) lo2038 hi2038=true := by decide +kernel
def bracket2038 : MeanBracket := meanBracketOfMoments (239/250) lo2038 hi2038 accepted2038
def lo2039b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨38,by decide⟩
def lo2039b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨39,by decide⟩
def lo2039 : CheckedMoment :=
  CheckedMoment.ofBessel lo2039b1 lo2039b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2039b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨43,by decide⟩
def hi2039b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨44,by decide⟩
def hi2039 : CheckedMoment :=
  CheckedMoment.ofBessel hi2039b1 hi2039b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2039 : meanBracketCheck (9561/10000) lo2039 hi2039=true := by decide +kernel
def bracket2039 : MeanBracket := meanBracketOfMoments (9561/10000) lo2039 hi2039 accepted2039
def lo2040b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨48,by decide⟩
def lo2040b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨49,by decide⟩
def lo2040 : CheckedMoment :=
  CheckedMoment.ofBessel lo2040b1 lo2040b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2040b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨53,by decide⟩
def hi2040b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨54,by decide⟩
def hi2040 : CheckedMoment :=
  CheckedMoment.ofBessel hi2040b1 hi2040b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2040 : meanBracketCheck (4781/5000) lo2040 hi2040=true := by decide +kernel
def bracket2040 : MeanBracket := meanBracketOfMoments (4781/5000) lo2040 hi2040 accepted2040
def lo2041b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨58,by decide⟩
def lo2041b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨59,by decide⟩
def lo2041 : CheckedMoment :=
  CheckedMoment.ofBessel lo2041b1 lo2041b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2041b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨63,by decide⟩
def hi2041b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨0,by decide⟩
def hi2041 : CheckedMoment :=
  CheckedMoment.ofBessel hi2041b1 hi2041b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2041 : meanBracketCheck (9563/10000) lo2041 hi2041=true := by decide +kernel
def bracket2041 : MeanBracket := meanBracketOfMoments (9563/10000) lo2041 hi2041 accepted2041
def lo2042b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨4,by decide⟩
def lo2042b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨5,by decide⟩
def lo2042 : CheckedMoment :=
  CheckedMoment.ofBessel lo2042b1 lo2042b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2042b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨9,by decide⟩
def hi2042b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨10,by decide⟩
def hi2042 : CheckedMoment :=
  CheckedMoment.ofBessel hi2042b1 hi2042b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2042 : meanBracketCheck (2391/2500) lo2042 hi2042=true := by decide +kernel
def bracket2042 : MeanBracket := meanBracketOfMoments (2391/2500) lo2042 hi2042 accepted2042
def lo2043b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨14,by decide⟩
def lo2043b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨15,by decide⟩
def lo2043 : CheckedMoment :=
  CheckedMoment.ofBessel lo2043b1 lo2043b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2043b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨19,by decide⟩
def hi2043b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨20,by decide⟩
def hi2043 : CheckedMoment :=
  CheckedMoment.ofBessel hi2043b1 hi2043b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2043 : meanBracketCheck (1913/2000) lo2043 hi2043=true := by decide +kernel
def bracket2043 : MeanBracket := meanBracketOfMoments (1913/2000) lo2043 hi2043 accepted2043
def lo2044b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨24,by decide⟩
def lo2044b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨25,by decide⟩
def lo2044 : CheckedMoment :=
  CheckedMoment.ofBessel lo2044b1 lo2044b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2044b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨29,by decide⟩
def hi2044b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨30,by decide⟩
def hi2044 : CheckedMoment :=
  CheckedMoment.ofBessel hi2044b1 hi2044b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2044 : meanBracketCheck (4783/5000) lo2044 hi2044=true := by decide +kernel
def bracket2044 : MeanBracket := meanBracketOfMoments (4783/5000) lo2044 hi2044 accepted2044
def lo2045b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨34,by decide⟩
def lo2045b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨35,by decide⟩
def lo2045 : CheckedMoment :=
  CheckedMoment.ofBessel lo2045b1 lo2045b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2045b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨39,by decide⟩
def hi2045b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨40,by decide⟩
def hi2045 : CheckedMoment :=
  CheckedMoment.ofBessel hi2045b1 hi2045b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2045 : meanBracketCheck (9567/10000) lo2045 hi2045=true := by decide +kernel
def bracket2045 : MeanBracket := meanBracketOfMoments (9567/10000) lo2045 hi2045 accepted2045
def lo2046b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨44,by decide⟩
def lo2046b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨45,by decide⟩
def lo2046 : CheckedMoment :=
  CheckedMoment.ofBessel lo2046b1 lo2046b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2046b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨49,by decide⟩
def hi2046b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨50,by decide⟩
def hi2046 : CheckedMoment :=
  CheckedMoment.ofBessel hi2046b1 hi2046b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2046 : meanBracketCheck (598/625) lo2046 hi2046=true := by decide +kernel
def bracket2046 : MeanBracket := meanBracketOfMoments (598/625) lo2046 hi2046 accepted2046
def lo2047b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨54,by decide⟩
def lo2047b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨55,by decide⟩
def lo2047 : CheckedMoment :=
  CheckedMoment.ofBessel lo2047b1 lo2047b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2047b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨59,by decide⟩
def hi2047b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨60,by decide⟩
def hi2047 : CheckedMoment :=
  CheckedMoment.ofBessel hi2047b1 hi2047b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2047 : meanBracketCheck (9569/10000) lo2047 hi2047=true := by decide +kernel
def bracket2047 : MeanBracket := meanBracketOfMoments (9569/10000) lo2047 hi2047 accepted2047
#print axioms bracket2032
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0127
