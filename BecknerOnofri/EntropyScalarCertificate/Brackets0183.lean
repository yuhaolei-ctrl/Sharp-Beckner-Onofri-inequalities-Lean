import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0457
import BecknerOnofri.EntropyScalarCertificate.Bessel0458
import BecknerOnofri.EntropyScalarCertificate.Bessel0459
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0183
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2928b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨32,by decide⟩
def lo2928b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨33,by decide⟩
def lo2928 : CheckedMoment :=
  CheckedMoment.ofBessel lo2928b1 lo2928b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2928b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨37,by decide⟩
def hi2928b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨38,by decide⟩
def hi2928 : CheckedMoment :=
  CheckedMoment.ofBessel hi2928b1 hi2928b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2928 : meanBracketCheck (499/500) lo2928 hi2928=true := by decide +kernel
def bracket2928 : MeanBracket := meanBracketOfMoments (499/500) lo2928 hi2928 accepted2928
def lo2929b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨42,by decide⟩
def lo2929b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨43,by decide⟩
def lo2929 : CheckedMoment :=
  CheckedMoment.ofBessel lo2929b1 lo2929b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2929b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨47,by decide⟩
def hi2929b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨48,by decide⟩
def hi2929 : CheckedMoment :=
  CheckedMoment.ofBessel hi2929b1 hi2929b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2929 : meanBracketCheck (199601/200000) lo2929 hi2929=true := by decide +kernel
def bracket2929 : MeanBracket := meanBracketOfMoments (199601/200000) lo2929 hi2929 accepted2929
def lo2930b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨52,by decide⟩
def lo2930b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨53,by decide⟩
def lo2930 : CheckedMoment :=
  CheckedMoment.ofBessel lo2930b1 lo2930b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2930b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨57,by decide⟩
def hi2930b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨58,by decide⟩
def hi2930 : CheckedMoment :=
  CheckedMoment.ofBessel hi2930b1 hi2930b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2930 : meanBracketCheck (99801/100000) lo2930 hi2930=true := by decide +kernel
def bracket2930 : MeanBracket := meanBracketOfMoments (99801/100000) lo2930 hi2930 accepted2930
def lo2931b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨62,by decide⟩
def lo2931b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨63,by decide⟩
def lo2931 : CheckedMoment :=
  CheckedMoment.ofBessel lo2931b1 lo2931b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2931b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨3,by decide⟩
def hi2931b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨4,by decide⟩
def hi2931 : CheckedMoment :=
  CheckedMoment.ofBessel hi2931b1 hi2931b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2931 : meanBracketCheck (199603/200000) lo2931 hi2931=true := by decide +kernel
def bracket2931 : MeanBracket := meanBracketOfMoments (199603/200000) lo2931 hi2931 accepted2931
def lo2932b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨8,by decide⟩
def lo2932b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨9,by decide⟩
def lo2932 : CheckedMoment :=
  CheckedMoment.ofBessel lo2932b1 lo2932b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2932b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨13,by decide⟩
def hi2932b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨14,by decide⟩
def hi2932 : CheckedMoment :=
  CheckedMoment.ofBessel hi2932b1 hi2932b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2932 : meanBracketCheck (49901/50000) lo2932 hi2932=true := by decide +kernel
def bracket2932 : MeanBracket := meanBracketOfMoments (49901/50000) lo2932 hi2932 accepted2932
def lo2933b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨18,by decide⟩
def lo2933b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨19,by decide⟩
def lo2933 : CheckedMoment :=
  CheckedMoment.ofBessel lo2933b1 lo2933b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2933b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨23,by decide⟩
def hi2933b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨24,by decide⟩
def hi2933 : CheckedMoment :=
  CheckedMoment.ofBessel hi2933b1 hi2933b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2933 : meanBracketCheck (39921/40000) lo2933 hi2933=true := by decide +kernel
def bracket2933 : MeanBracket := meanBracketOfMoments (39921/40000) lo2933 hi2933 accepted2933
def lo2934b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨28,by decide⟩
def lo2934b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨29,by decide⟩
def lo2934 : CheckedMoment :=
  CheckedMoment.ofBessel lo2934b1 lo2934b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2934b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨33,by decide⟩
def hi2934b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨34,by decide⟩
def hi2934 : CheckedMoment :=
  CheckedMoment.ofBessel hi2934b1 hi2934b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2934 : meanBracketCheck (99803/100000) lo2934 hi2934=true := by decide +kernel
def bracket2934 : MeanBracket := meanBracketOfMoments (99803/100000) lo2934 hi2934 accepted2934
def lo2935b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨38,by decide⟩
def lo2935b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨39,by decide⟩
def lo2935 : CheckedMoment :=
  CheckedMoment.ofBessel lo2935b1 lo2935b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2935b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨43,by decide⟩
def hi2935b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨44,by decide⟩
def hi2935 : CheckedMoment :=
  CheckedMoment.ofBessel hi2935b1 hi2935b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2935 : meanBracketCheck (199607/200000) lo2935 hi2935=true := by decide +kernel
def bracket2935 : MeanBracket := meanBracketOfMoments (199607/200000) lo2935 hi2935 accepted2935
def lo2936b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨48,by decide⟩
def lo2936b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨49,by decide⟩
def lo2936 : CheckedMoment :=
  CheckedMoment.ofBessel lo2936b1 lo2936b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2936b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨53,by decide⟩
def hi2936b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨54,by decide⟩
def hi2936 : CheckedMoment :=
  CheckedMoment.ofBessel hi2936b1 hi2936b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2936 : meanBracketCheck (24951/25000) lo2936 hi2936=true := by decide +kernel
def bracket2936 : MeanBracket := meanBracketOfMoments (24951/25000) lo2936 hi2936 accepted2936
def lo2937b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨58,by decide⟩
def lo2937b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨59,by decide⟩
def lo2937 : CheckedMoment :=
  CheckedMoment.ofBessel lo2937b1 lo2937b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2937b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨63,by decide⟩
def hi2937b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨0,by decide⟩
def hi2937 : CheckedMoment :=
  CheckedMoment.ofBessel hi2937b1 hi2937b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2937 : meanBracketCheck (199609/200000) lo2937 hi2937=true := by decide +kernel
def bracket2937 : MeanBracket := meanBracketOfMoments (199609/200000) lo2937 hi2937 accepted2937
def lo2938b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨4,by decide⟩
def lo2938b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨5,by decide⟩
def lo2938 : CheckedMoment :=
  CheckedMoment.ofBessel lo2938b1 lo2938b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2938b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨9,by decide⟩
def hi2938b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨10,by decide⟩
def hi2938 : CheckedMoment :=
  CheckedMoment.ofBessel hi2938b1 hi2938b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2938 : meanBracketCheck (19961/20000) lo2938 hi2938=true := by decide +kernel
def bracket2938 : MeanBracket := meanBracketOfMoments (19961/20000) lo2938 hi2938 accepted2938
def lo2939b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨14,by decide⟩
def lo2939b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨15,by decide⟩
def lo2939 : CheckedMoment :=
  CheckedMoment.ofBessel lo2939b1 lo2939b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2939b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨19,by decide⟩
def hi2939b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨20,by decide⟩
def hi2939 : CheckedMoment :=
  CheckedMoment.ofBessel hi2939b1 hi2939b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2939 : meanBracketCheck (199611/200000) lo2939 hi2939=true := by decide +kernel
def bracket2939 : MeanBracket := meanBracketOfMoments (199611/200000) lo2939 hi2939 accepted2939
def lo2940b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨24,by decide⟩
def lo2940b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨25,by decide⟩
def lo2940 : CheckedMoment :=
  CheckedMoment.ofBessel lo2940b1 lo2940b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2940b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨29,by decide⟩
def hi2940b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨30,by decide⟩
def hi2940 : CheckedMoment :=
  CheckedMoment.ofBessel hi2940b1 hi2940b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2940 : meanBracketCheck (49903/50000) lo2940 hi2940=true := by decide +kernel
def bracket2940 : MeanBracket := meanBracketOfMoments (49903/50000) lo2940 hi2940 accepted2940
def lo2941b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨34,by decide⟩
def lo2941b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨35,by decide⟩
def lo2941 : CheckedMoment :=
  CheckedMoment.ofBessel lo2941b1 lo2941b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2941b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨39,by decide⟩
def hi2941b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨40,by decide⟩
def hi2941 : CheckedMoment :=
  CheckedMoment.ofBessel hi2941b1 hi2941b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2941 : meanBracketCheck (199613/200000) lo2941 hi2941=true := by decide +kernel
def bracket2941 : MeanBracket := meanBracketOfMoments (199613/200000) lo2941 hi2941 accepted2941
def lo2942b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨44,by decide⟩
def lo2942b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨45,by decide⟩
def lo2942 : CheckedMoment :=
  CheckedMoment.ofBessel lo2942b1 lo2942b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2942b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨49,by decide⟩
def hi2942b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨50,by decide⟩
def hi2942 : CheckedMoment :=
  CheckedMoment.ofBessel hi2942b1 hi2942b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2942 : meanBracketCheck (99807/100000) lo2942 hi2942=true := by decide +kernel
def bracket2942 : MeanBracket := meanBracketOfMoments (99807/100000) lo2942 hi2942 accepted2942
def lo2943b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨54,by decide⟩
def lo2943b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨55,by decide⟩
def lo2943 : CheckedMoment :=
  CheckedMoment.ofBessel lo2943b1 lo2943b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2943b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨59,by decide⟩
def hi2943b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨60,by decide⟩
def hi2943 : CheckedMoment :=
  CheckedMoment.ofBessel hi2943b1 hi2943b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2943 : meanBracketCheck (39923/40000) lo2943 hi2943=true := by decide +kernel
def bracket2943 : MeanBracket := meanBracketOfMoments (39923/40000) lo2943 hi2943 accepted2943
#print axioms bracket2928
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0183
