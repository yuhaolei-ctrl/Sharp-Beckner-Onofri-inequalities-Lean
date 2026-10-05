import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0012
import BecknerOnofri.EntropyScalarCertificate.Bessel0013
import BecknerOnofri.EntropyScalarCertificate.Bessel0014
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0005
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0080b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨32,by decide⟩
def lo0080b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨33,by decide⟩
def lo0080 : CheckedMoment :=
  CheckedMoment.ofBessel lo0080b1 lo0080b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0080b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨37,by decide⟩
def hi0080b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨38,by decide⟩
def hi0080 : CheckedMoment :=
  CheckedMoment.ofBessel hi0080b1 hi0080b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0080 : meanBracketCheck (29/400) lo0080 hi0080=true := by decide +kernel
def bracket0080 : MeanBracket := meanBracketOfMoments (29/400) lo0080 hi0080 accepted0080
def lo0081b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨42,by decide⟩
def lo0081b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨43,by decide⟩
def lo0081 : CheckedMoment :=
  CheckedMoment.ofBessel lo0081b1 lo0081b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0081b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨47,by decide⟩
def hi0081b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨48,by decide⟩
def hi0081 : CheckedMoment :=
  CheckedMoment.ofBessel hi0081b1 hi0081b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0081 : meanBracketCheck (727/10000) lo0081 hi0081=true := by decide +kernel
def bracket0081 : MeanBracket := meanBracketOfMoments (727/10000) lo0081 hi0081 accepted0081
def lo0082b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨52,by decide⟩
def lo0082b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨53,by decide⟩
def lo0082 : CheckedMoment :=
  CheckedMoment.ofBessel lo0082b1 lo0082b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0082b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨57,by decide⟩
def hi0082b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨58,by decide⟩
def hi0082 : CheckedMoment :=
  CheckedMoment.ofBessel hi0082b1 hi0082b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0082 : meanBracketCheck (729/10000) lo0082 hi0082=true := by decide +kernel
def bracket0082 : MeanBracket := meanBracketOfMoments (729/10000) lo0082 hi0082 accepted0082
def lo0083b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨62,by decide⟩
def lo0083b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨63,by decide⟩
def lo0083 : CheckedMoment :=
  CheckedMoment.ofBessel lo0083b1 lo0083b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0083b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨3,by decide⟩
def hi0083b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨4,by decide⟩
def hi0083 : CheckedMoment :=
  CheckedMoment.ofBessel hi0083b1 hi0083b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0083 : meanBracketCheck (731/10000) lo0083 hi0083=true := by decide +kernel
def bracket0083 : MeanBracket := meanBracketOfMoments (731/10000) lo0083 hi0083 accepted0083
def lo0084b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨8,by decide⟩
def lo0084b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨9,by decide⟩
def lo0084 : CheckedMoment :=
  CheckedMoment.ofBessel lo0084b1 lo0084b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0084b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨13,by decide⟩
def hi0084b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨14,by decide⟩
def hi0084 : CheckedMoment :=
  CheckedMoment.ofBessel hi0084b1 hi0084b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0084 : meanBracketCheck (733/10000) lo0084 hi0084=true := by decide +kernel
def bracket0084 : MeanBracket := meanBracketOfMoments (733/10000) lo0084 hi0084 accepted0084
def lo0085b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨18,by decide⟩
def lo0085b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨19,by decide⟩
def lo0085 : CheckedMoment :=
  CheckedMoment.ofBessel lo0085b1 lo0085b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0085b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨23,by decide⟩
def hi0085b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨24,by decide⟩
def hi0085 : CheckedMoment :=
  CheckedMoment.ofBessel hi0085b1 hi0085b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0085 : meanBracketCheck (147/2000) lo0085 hi0085=true := by decide +kernel
def bracket0085 : MeanBracket := meanBracketOfMoments (147/2000) lo0085 hi0085 accepted0085
def lo0086b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨28,by decide⟩
def lo0086b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨29,by decide⟩
def lo0086 : CheckedMoment :=
  CheckedMoment.ofBessel lo0086b1 lo0086b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0086b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨33,by decide⟩
def hi0086b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨34,by decide⟩
def hi0086 : CheckedMoment :=
  CheckedMoment.ofBessel hi0086b1 hi0086b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0086 : meanBracketCheck (737/10000) lo0086 hi0086=true := by decide +kernel
def bracket0086 : MeanBracket := meanBracketOfMoments (737/10000) lo0086 hi0086 accepted0086
def lo0087b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨38,by decide⟩
def lo0087b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨39,by decide⟩
def lo0087 : CheckedMoment :=
  CheckedMoment.ofBessel lo0087b1 lo0087b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0087b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨43,by decide⟩
def hi0087b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨44,by decide⟩
def hi0087 : CheckedMoment :=
  CheckedMoment.ofBessel hi0087b1 hi0087b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0087 : meanBracketCheck (739/10000) lo0087 hi0087=true := by decide +kernel
def bracket0087 : MeanBracket := meanBracketOfMoments (739/10000) lo0087 hi0087 accepted0087
def lo0088b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨48,by decide⟩
def lo0088b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨49,by decide⟩
def lo0088 : CheckedMoment :=
  CheckedMoment.ofBessel lo0088b1 lo0088b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0088b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨53,by decide⟩
def hi0088b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨54,by decide⟩
def hi0088 : CheckedMoment :=
  CheckedMoment.ofBessel hi0088b1 hi0088b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0088 : meanBracketCheck (741/10000) lo0088 hi0088=true := by decide +kernel
def bracket0088 : MeanBracket := meanBracketOfMoments (741/10000) lo0088 hi0088 accepted0088
def lo0089b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨58,by decide⟩
def lo0089b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨59,by decide⟩
def lo0089 : CheckedMoment :=
  CheckedMoment.ofBessel lo0089b1 lo0089b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0089b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨63,by decide⟩
def hi0089b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨0,by decide⟩
def hi0089 : CheckedMoment :=
  CheckedMoment.ofBessel hi0089b1 hi0089b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0089 : meanBracketCheck (743/10000) lo0089 hi0089=true := by decide +kernel
def bracket0089 : MeanBracket := meanBracketOfMoments (743/10000) lo0089 hi0089 accepted0089
def lo0090b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨4,by decide⟩
def lo0090b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨5,by decide⟩
def lo0090 : CheckedMoment :=
  CheckedMoment.ofBessel lo0090b1 lo0090b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0090b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨9,by decide⟩
def hi0090b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨10,by decide⟩
def hi0090 : CheckedMoment :=
  CheckedMoment.ofBessel hi0090b1 hi0090b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0090 : meanBracketCheck (149/2000) lo0090 hi0090=true := by decide +kernel
def bracket0090 : MeanBracket := meanBracketOfMoments (149/2000) lo0090 hi0090 accepted0090
def lo0091b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨14,by decide⟩
def lo0091b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨15,by decide⟩
def lo0091 : CheckedMoment :=
  CheckedMoment.ofBessel lo0091b1 lo0091b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0091b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨19,by decide⟩
def hi0091b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨20,by decide⟩
def hi0091 : CheckedMoment :=
  CheckedMoment.ofBessel hi0091b1 hi0091b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0091 : meanBracketCheck (747/10000) lo0091 hi0091=true := by decide +kernel
def bracket0091 : MeanBracket := meanBracketOfMoments (747/10000) lo0091 hi0091 accepted0091
def lo0092b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨24,by decide⟩
def lo0092b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨25,by decide⟩
def lo0092 : CheckedMoment :=
  CheckedMoment.ofBessel lo0092b1 lo0092b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0092b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨29,by decide⟩
def hi0092b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨30,by decide⟩
def hi0092 : CheckedMoment :=
  CheckedMoment.ofBessel hi0092b1 hi0092b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0092 : meanBracketCheck (749/10000) lo0092 hi0092=true := by decide +kernel
def bracket0092 : MeanBracket := meanBracketOfMoments (749/10000) lo0092 hi0092 accepted0092
def lo0093b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨34,by decide⟩
def lo0093b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨35,by decide⟩
def lo0093 : CheckedMoment :=
  CheckedMoment.ofBessel lo0093b1 lo0093b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0093b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨39,by decide⟩
def hi0093b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨40,by decide⟩
def hi0093 : CheckedMoment :=
  CheckedMoment.ofBessel hi0093b1 hi0093b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0093 : meanBracketCheck (751/10000) lo0093 hi0093=true := by decide +kernel
def bracket0093 : MeanBracket := meanBracketOfMoments (751/10000) lo0093 hi0093 accepted0093
def lo0094b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨44,by decide⟩
def lo0094b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨45,by decide⟩
def lo0094 : CheckedMoment :=
  CheckedMoment.ofBessel lo0094b1 lo0094b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0094b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨49,by decide⟩
def hi0094b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨50,by decide⟩
def hi0094 : CheckedMoment :=
  CheckedMoment.ofBessel hi0094b1 hi0094b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0094 : meanBracketCheck (753/10000) lo0094 hi0094=true := by decide +kernel
def bracket0094 : MeanBracket := meanBracketOfMoments (753/10000) lo0094 hi0094 accepted0094
def lo0095b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨54,by decide⟩
def lo0095b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨55,by decide⟩
def lo0095 : CheckedMoment :=
  CheckedMoment.ofBessel lo0095b1 lo0095b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0095b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨59,by decide⟩
def hi0095b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨60,by decide⟩
def hi0095 : CheckedMoment :=
  CheckedMoment.ofBessel hi0095b1 hi0095b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0095 : meanBracketCheck (151/2000) lo0095 hi0095=true := by decide +kernel
def bracket0095 : MeanBracket := meanBracketOfMoments (151/2000) lo0095 hi0095 accepted0095
#print axioms bracket0080
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0005
