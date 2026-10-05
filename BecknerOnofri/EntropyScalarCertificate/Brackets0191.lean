import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0477
import BecknerOnofri.EntropyScalarCertificate.Bessel0478
import BecknerOnofri.EntropyScalarCertificate.Bessel0479
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0191
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo3056b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨32,by decide⟩
def lo3056b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨33,by decide⟩
def lo3056 : CheckedMoment :=
  CheckedMoment.ofBessel lo3056b1 lo3056b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3056b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨37,by decide⟩
def hi3056b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨38,by decide⟩
def hi3056 : CheckedMoment :=
  CheckedMoment.ofBessel hi3056b1 hi3056b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3056 : meanBracketCheck (12483/12500) lo3056 hi3056=true := by decide +kernel
def bracket3056 : MeanBracket := meanBracketOfMoments (12483/12500) lo3056 hi3056 accepted3056
def lo3057b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨42,by decide⟩
def lo3057b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨43,by decide⟩
def lo3057 : CheckedMoment :=
  CheckedMoment.ofBessel lo3057b1 lo3057b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3057b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨47,by decide⟩
def hi3057b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨48,by decide⟩
def hi3057 : CheckedMoment :=
  CheckedMoment.ofBessel hi3057b1 hi3057b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3057 : meanBracketCheck (199729/200000) lo3057 hi3057=true := by decide +kernel
def bracket3057 : MeanBracket := meanBracketOfMoments (199729/200000) lo3057 hi3057 accepted3057
def lo3058b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨52,by decide⟩
def lo3058b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨53,by decide⟩
def lo3058 : CheckedMoment :=
  CheckedMoment.ofBessel lo3058b1 lo3058b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3058b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨57,by decide⟩
def hi3058b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨58,by decide⟩
def hi3058 : CheckedMoment :=
  CheckedMoment.ofBessel hi3058b1 hi3058b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3058 : meanBracketCheck (19973/20000) lo3058 hi3058=true := by decide +kernel
def bracket3058 : MeanBracket := meanBracketOfMoments (19973/20000) lo3058 hi3058 accepted3058
def lo3059b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨62,by decide⟩
def lo3059b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨63,by decide⟩
def lo3059 : CheckedMoment :=
  CheckedMoment.ofBessel lo3059b1 lo3059b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3059b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨3,by decide⟩
def hi3059b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨4,by decide⟩
def hi3059 : CheckedMoment :=
  CheckedMoment.ofBessel hi3059b1 hi3059b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3059 : meanBracketCheck (199731/200000) lo3059 hi3059=true := by decide +kernel
def bracket3059 : MeanBracket := meanBracketOfMoments (199731/200000) lo3059 hi3059 accepted3059
def lo3060b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨8,by decide⟩
def lo3060b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨9,by decide⟩
def lo3060 : CheckedMoment :=
  CheckedMoment.ofBessel lo3060b1 lo3060b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3060b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨13,by decide⟩
def hi3060b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨14,by decide⟩
def hi3060 : CheckedMoment :=
  CheckedMoment.ofBessel hi3060b1 hi3060b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3060 : meanBracketCheck (49933/50000) lo3060 hi3060=true := by decide +kernel
def bracket3060 : MeanBracket := meanBracketOfMoments (49933/50000) lo3060 hi3060 accepted3060
def lo3061b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨18,by decide⟩
def lo3061b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨19,by decide⟩
def lo3061 : CheckedMoment :=
  CheckedMoment.ofBessel lo3061b1 lo3061b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3061b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨23,by decide⟩
def hi3061b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨24,by decide⟩
def hi3061 : CheckedMoment :=
  CheckedMoment.ofBessel hi3061b1 hi3061b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3061 : meanBracketCheck (199733/200000) lo3061 hi3061=true := by decide +kernel
def bracket3061 : MeanBracket := meanBracketOfMoments (199733/200000) lo3061 hi3061 accepted3061
def lo3062b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨28,by decide⟩
def lo3062b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨29,by decide⟩
def lo3062 : CheckedMoment :=
  CheckedMoment.ofBessel lo3062b1 lo3062b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3062b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨33,by decide⟩
def hi3062b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨34,by decide⟩
def hi3062 : CheckedMoment :=
  CheckedMoment.ofBessel hi3062b1 hi3062b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3062 : meanBracketCheck (99867/100000) lo3062 hi3062=true := by decide +kernel
def bracket3062 : MeanBracket := meanBracketOfMoments (99867/100000) lo3062 hi3062 accepted3062
def lo3063b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨38,by decide⟩
def lo3063b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨39,by decide⟩
def lo3063 : CheckedMoment :=
  CheckedMoment.ofBessel lo3063b1 lo3063b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3063b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨43,by decide⟩
def hi3063b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨44,by decide⟩
def hi3063 : CheckedMoment :=
  CheckedMoment.ofBessel hi3063b1 hi3063b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3063 : meanBracketCheck (39947/40000) lo3063 hi3063=true := by decide +kernel
def bracket3063 : MeanBracket := meanBracketOfMoments (39947/40000) lo3063 hi3063 accepted3063
def lo3064b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨48,by decide⟩
def lo3064b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨49,by decide⟩
def lo3064 : CheckedMoment :=
  CheckedMoment.ofBessel lo3064b1 lo3064b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3064b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨53,by decide⟩
def hi3064b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨54,by decide⟩
def hi3064 : CheckedMoment :=
  CheckedMoment.ofBessel hi3064b1 hi3064b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3064 : meanBracketCheck (24967/25000) lo3064 hi3064=true := by decide +kernel
def bracket3064 : MeanBracket := meanBracketOfMoments (24967/25000) lo3064 hi3064 accepted3064
def lo3065b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨58,by decide⟩
def lo3065b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨59,by decide⟩
def lo3065 : CheckedMoment :=
  CheckedMoment.ofBessel lo3065b1 lo3065b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3065b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨63,by decide⟩
def hi3065b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨0,by decide⟩
def hi3065 : CheckedMoment :=
  CheckedMoment.ofBessel hi3065b1 hi3065b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3065 : meanBracketCheck (199737/200000) lo3065 hi3065=true := by decide +kernel
def bracket3065 : MeanBracket := meanBracketOfMoments (199737/200000) lo3065 hi3065 accepted3065
def lo3066b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨4,by decide⟩
def lo3066b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨5,by decide⟩
def lo3066 : CheckedMoment :=
  CheckedMoment.ofBessel lo3066b1 lo3066b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3066b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨9,by decide⟩
def hi3066b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨10,by decide⟩
def hi3066 : CheckedMoment :=
  CheckedMoment.ofBessel hi3066b1 hi3066b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3066 : meanBracketCheck (99869/100000) lo3066 hi3066=true := by decide +kernel
def bracket3066 : MeanBracket := meanBracketOfMoments (99869/100000) lo3066 hi3066 accepted3066
def lo3067b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨14,by decide⟩
def lo3067b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨15,by decide⟩
def lo3067 : CheckedMoment :=
  CheckedMoment.ofBessel lo3067b1 lo3067b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3067b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨19,by decide⟩
def hi3067b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨20,by decide⟩
def hi3067 : CheckedMoment :=
  CheckedMoment.ofBessel hi3067b1 hi3067b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3067 : meanBracketCheck (199739/200000) lo3067 hi3067=true := by decide +kernel
def bracket3067 : MeanBracket := meanBracketOfMoments (199739/200000) lo3067 hi3067 accepted3067
def lo3068b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨24,by decide⟩
def lo3068b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨25,by decide⟩
def lo3068 : CheckedMoment :=
  CheckedMoment.ofBessel lo3068b1 lo3068b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3068b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨29,by decide⟩
def hi3068b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨30,by decide⟩
def hi3068 : CheckedMoment :=
  CheckedMoment.ofBessel hi3068b1 hi3068b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3068 : meanBracketCheck (9987/10000) lo3068 hi3068=true := by decide +kernel
def bracket3068 : MeanBracket := meanBracketOfMoments (9987/10000) lo3068 hi3068 accepted3068
def lo3069b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨34,by decide⟩
def lo3069b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨35,by decide⟩
def lo3069 : CheckedMoment :=
  CheckedMoment.ofBessel lo3069b1 lo3069b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3069b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨39,by decide⟩
def hi3069b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨40,by decide⟩
def hi3069 : CheckedMoment :=
  CheckedMoment.ofBessel hi3069b1 hi3069b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3069 : meanBracketCheck (199741/200000) lo3069 hi3069=true := by decide +kernel
def bracket3069 : MeanBracket := meanBracketOfMoments (199741/200000) lo3069 hi3069 accepted3069
def lo3070b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨44,by decide⟩
def lo3070b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨45,by decide⟩
def lo3070 : CheckedMoment :=
  CheckedMoment.ofBessel lo3070b1 lo3070b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3070b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨49,by decide⟩
def hi3070b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨50,by decide⟩
def hi3070 : CheckedMoment :=
  CheckedMoment.ofBessel hi3070b1 hi3070b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3070 : meanBracketCheck (99871/100000) lo3070 hi3070=true := by decide +kernel
def bracket3070 : MeanBracket := meanBracketOfMoments (99871/100000) lo3070 hi3070 accepted3070
def lo3071b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨54,by decide⟩
def lo3071b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨55,by decide⟩
def lo3071 : CheckedMoment :=
  CheckedMoment.ofBessel lo3071b1 lo3071b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3071b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨59,by decide⟩
def hi3071b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨60,by decide⟩
def hi3071 : CheckedMoment :=
  CheckedMoment.ofBessel hi3071b1 hi3071b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3071 : meanBracketCheck (199743/200000) lo3071 hi3071=true := by decide +kernel
def bracket3071 : MeanBracket := meanBracketOfMoments (199743/200000) lo3071 hi3071 accepted3071
#print axioms bracket3056
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0191
