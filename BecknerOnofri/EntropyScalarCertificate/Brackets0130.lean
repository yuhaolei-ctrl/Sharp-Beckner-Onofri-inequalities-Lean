import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0325
import BecknerOnofri.EntropyScalarCertificate.Bessel0326
import BecknerOnofri.EntropyScalarCertificate.Bessel0327
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0130
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2080b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨0,by decide⟩
def lo2080b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨1,by decide⟩
def lo2080 : CheckedMoment :=
  CheckedMoment.ofBessel lo2080b1 lo2080b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2080b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨5,by decide⟩
def hi2080b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨6,by decide⟩
def hi2080 : CheckedMoment :=
  CheckedMoment.ofBessel hi2080b1 hi2080b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2080 : meanBracketCheck (4801/5000) lo2080 hi2080=true := by decide +kernel
def bracket2080 : MeanBracket := meanBracketOfMoments (4801/5000) lo2080 hi2080 accepted2080
def lo2081b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨10,by decide⟩
def lo2081b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨11,by decide⟩
def lo2081 : CheckedMoment :=
  CheckedMoment.ofBessel lo2081b1 lo2081b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2081b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨15,by decide⟩
def hi2081b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨16,by decide⟩
def hi2081 : CheckedMoment :=
  CheckedMoment.ofBessel hi2081b1 hi2081b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2081 : meanBracketCheck (9603/10000) lo2081 hi2081=true := by decide +kernel
def bracket2081 : MeanBracket := meanBracketOfMoments (9603/10000) lo2081 hi2081 accepted2081
def lo2082b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨20,by decide⟩
def lo2082b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨21,by decide⟩
def lo2082 : CheckedMoment :=
  CheckedMoment.ofBessel lo2082b1 lo2082b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2082b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨25,by decide⟩
def hi2082b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨26,by decide⟩
def hi2082 : CheckedMoment :=
  CheckedMoment.ofBessel hi2082b1 hi2082b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2082 : meanBracketCheck (2401/2500) lo2082 hi2082=true := by decide +kernel
def bracket2082 : MeanBracket := meanBracketOfMoments (2401/2500) lo2082 hi2082 accepted2082
def lo2083b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨30,by decide⟩
def lo2083b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨31,by decide⟩
def lo2083 : CheckedMoment :=
  CheckedMoment.ofBessel lo2083b1 lo2083b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2083b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨35,by decide⟩
def hi2083b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨36,by decide⟩
def hi2083 : CheckedMoment :=
  CheckedMoment.ofBessel hi2083b1 hi2083b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2083 : meanBracketCheck (1921/2000) lo2083 hi2083=true := by decide +kernel
def bracket2083 : MeanBracket := meanBracketOfMoments (1921/2000) lo2083 hi2083 accepted2083
def lo2084b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨40,by decide⟩
def lo2084b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨41,by decide⟩
def lo2084 : CheckedMoment :=
  CheckedMoment.ofBessel lo2084b1 lo2084b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2084b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨45,by decide⟩
def hi2084b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨46,by decide⟩
def hi2084 : CheckedMoment :=
  CheckedMoment.ofBessel hi2084b1 hi2084b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2084 : meanBracketCheck (4803/5000) lo2084 hi2084=true := by decide +kernel
def bracket2084 : MeanBracket := meanBracketOfMoments (4803/5000) lo2084 hi2084 accepted2084
def lo2085b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨50,by decide⟩
def lo2085b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨51,by decide⟩
def lo2085 : CheckedMoment :=
  CheckedMoment.ofBessel lo2085b1 lo2085b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2085b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨55,by decide⟩
def hi2085b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨56,by decide⟩
def hi2085 : CheckedMoment :=
  CheckedMoment.ofBessel hi2085b1 hi2085b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2085 : meanBracketCheck (9607/10000) lo2085 hi2085=true := by decide +kernel
def bracket2085 : MeanBracket := meanBracketOfMoments (9607/10000) lo2085 hi2085 accepted2085
def lo2086b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨60,by decide⟩
def lo2086b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨61,by decide⟩
def lo2086 : CheckedMoment :=
  CheckedMoment.ofBessel lo2086b1 lo2086b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2086b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨1,by decide⟩
def hi2086b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨2,by decide⟩
def hi2086 : CheckedMoment :=
  CheckedMoment.ofBessel hi2086b1 hi2086b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2086 : meanBracketCheck (1201/1250) lo2086 hi2086=true := by decide +kernel
def bracket2086 : MeanBracket := meanBracketOfMoments (1201/1250) lo2086 hi2086 accepted2086
def lo2087b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨6,by decide⟩
def lo2087b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨7,by decide⟩
def lo2087 : CheckedMoment :=
  CheckedMoment.ofBessel lo2087b1 lo2087b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2087b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨11,by decide⟩
def hi2087b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨12,by decide⟩
def hi2087 : CheckedMoment :=
  CheckedMoment.ofBessel hi2087b1 hi2087b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2087 : meanBracketCheck (9609/10000) lo2087 hi2087=true := by decide +kernel
def bracket2087 : MeanBracket := meanBracketOfMoments (9609/10000) lo2087 hi2087 accepted2087
def lo2088b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨16,by decide⟩
def lo2088b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨17,by decide⟩
def lo2088 : CheckedMoment :=
  CheckedMoment.ofBessel lo2088b1 lo2088b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2088b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨21,by decide⟩
def hi2088b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨22,by decide⟩
def hi2088 : CheckedMoment :=
  CheckedMoment.ofBessel hi2088b1 hi2088b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2088 : meanBracketCheck (961/1000) lo2088 hi2088=true := by decide +kernel
def bracket2088 : MeanBracket := meanBracketOfMoments (961/1000) lo2088 hi2088 accepted2088
def lo2089b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨26,by decide⟩
def lo2089b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨27,by decide⟩
def lo2089 : CheckedMoment :=
  CheckedMoment.ofBessel lo2089b1 lo2089b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2089b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨31,by decide⟩
def hi2089b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨32,by decide⟩
def hi2089 : CheckedMoment :=
  CheckedMoment.ofBessel hi2089b1 hi2089b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2089 : meanBracketCheck (9611/10000) lo2089 hi2089=true := by decide +kernel
def bracket2089 : MeanBracket := meanBracketOfMoments (9611/10000) lo2089 hi2089 accepted2089
def lo2090b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨36,by decide⟩
def lo2090b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨37,by decide⟩
def lo2090 : CheckedMoment :=
  CheckedMoment.ofBessel lo2090b1 lo2090b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2090b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨41,by decide⟩
def hi2090b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨42,by decide⟩
def hi2090 : CheckedMoment :=
  CheckedMoment.ofBessel hi2090b1 hi2090b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2090 : meanBracketCheck (2403/2500) lo2090 hi2090=true := by decide +kernel
def bracket2090 : MeanBracket := meanBracketOfMoments (2403/2500) lo2090 hi2090 accepted2090
def lo2091b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨46,by decide⟩
def lo2091b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨47,by decide⟩
def lo2091 : CheckedMoment :=
  CheckedMoment.ofBessel lo2091b1 lo2091b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2091b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨51,by decide⟩
def hi2091b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨52,by decide⟩
def hi2091 : CheckedMoment :=
  CheckedMoment.ofBessel hi2091b1 hi2091b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2091 : meanBracketCheck (9613/10000) lo2091 hi2091=true := by decide +kernel
def bracket2091 : MeanBracket := meanBracketOfMoments (9613/10000) lo2091 hi2091 accepted2091
def lo2092b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨56,by decide⟩
def lo2092b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨57,by decide⟩
def lo2092 : CheckedMoment :=
  CheckedMoment.ofBessel lo2092b1 lo2092b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2092b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨61,by decide⟩
def hi2092b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨62,by decide⟩
def hi2092 : CheckedMoment :=
  CheckedMoment.ofBessel hi2092b1 hi2092b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2092 : meanBracketCheck (4807/5000) lo2092 hi2092=true := by decide +kernel
def bracket2092 : MeanBracket := meanBracketOfMoments (4807/5000) lo2092 hi2092 accepted2092
def lo2093b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨2,by decide⟩
def lo2093b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨3,by decide⟩
def lo2093 : CheckedMoment :=
  CheckedMoment.ofBessel lo2093b1 lo2093b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2093b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨7,by decide⟩
def hi2093b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨8,by decide⟩
def hi2093 : CheckedMoment :=
  CheckedMoment.ofBessel hi2093b1 hi2093b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2093 : meanBracketCheck (1923/2000) lo2093 hi2093=true := by decide +kernel
def bracket2093 : MeanBracket := meanBracketOfMoments (1923/2000) lo2093 hi2093 accepted2093
def lo2094b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨12,by decide⟩
def lo2094b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨13,by decide⟩
def lo2094 : CheckedMoment :=
  CheckedMoment.ofBessel lo2094b1 lo2094b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2094b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨17,by decide⟩
def hi2094b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨18,by decide⟩
def hi2094 : CheckedMoment :=
  CheckedMoment.ofBessel hi2094b1 hi2094b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2094 : meanBracketCheck (601/625) lo2094 hi2094=true := by decide +kernel
def bracket2094 : MeanBracket := meanBracketOfMoments (601/625) lo2094 hi2094 accepted2094
def lo2095b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨22,by decide⟩
def lo2095b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨23,by decide⟩
def lo2095 : CheckedMoment :=
  CheckedMoment.ofBessel lo2095b1 lo2095b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2095b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨27,by decide⟩
def hi2095b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨28,by decide⟩
def hi2095 : CheckedMoment :=
  CheckedMoment.ofBessel hi2095b1 hi2095b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2095 : meanBracketCheck (9617/10000) lo2095 hi2095=true := by decide +kernel
def bracket2095 : MeanBracket := meanBracketOfMoments (9617/10000) lo2095 hi2095 accepted2095
#print axioms bracket2080
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0130
