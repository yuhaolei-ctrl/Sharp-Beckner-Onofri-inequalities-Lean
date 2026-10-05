import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0482
import BecknerOnofri.EntropyScalarCertificate.Bessel0483
import BecknerOnofri.EntropyScalarCertificate.Bessel0484
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0193
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo3088b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨32,by decide⟩
def lo3088b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨33,by decide⟩
def lo3088 : CheckedMoment :=
  CheckedMoment.ofBessel lo3088b1 lo3088b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3088b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨37,by decide⟩
def hi3088b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨38,by decide⟩
def hi3088 : CheckedMoment :=
  CheckedMoment.ofBessel hi3088b1 hi3088b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3088 : meanBracketCheck (2497/2500) lo3088 hi3088=true := by decide +kernel
def bracket3088 : MeanBracket := meanBracketOfMoments (2497/2500) lo3088 hi3088 accepted3088
def lo3089b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨42,by decide⟩
def lo3089b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨43,by decide⟩
def lo3089 : CheckedMoment :=
  CheckedMoment.ofBessel lo3089b1 lo3089b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3089b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨47,by decide⟩
def hi3089b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨48,by decide⟩
def hi3089 : CheckedMoment :=
  CheckedMoment.ofBessel hi3089b1 hi3089b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3089 : meanBracketCheck (199761/200000) lo3089 hi3089=true := by decide +kernel
def bracket3089 : MeanBracket := meanBracketOfMoments (199761/200000) lo3089 hi3089 accepted3089
def lo3090b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨52,by decide⟩
def lo3090b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨53,by decide⟩
def lo3090 : CheckedMoment :=
  CheckedMoment.ofBessel lo3090b1 lo3090b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3090b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨57,by decide⟩
def hi3090b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨58,by decide⟩
def hi3090 : CheckedMoment :=
  CheckedMoment.ofBessel hi3090b1 hi3090b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3090 : meanBracketCheck (99881/100000) lo3090 hi3090=true := by decide +kernel
def bracket3090 : MeanBracket := meanBracketOfMoments (99881/100000) lo3090 hi3090 accepted3090
def lo3091b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨62,by decide⟩
def lo3091b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨63,by decide⟩
def lo3091 : CheckedMoment :=
  CheckedMoment.ofBessel lo3091b1 lo3091b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3091b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨3,by decide⟩
def hi3091b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨4,by decide⟩
def hi3091 : CheckedMoment :=
  CheckedMoment.ofBessel hi3091b1 hi3091b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3091 : meanBracketCheck (199763/200000) lo3091 hi3091=true := by decide +kernel
def bracket3091 : MeanBracket := meanBracketOfMoments (199763/200000) lo3091 hi3091 accepted3091
def lo3092b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨8,by decide⟩
def lo3092b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨9,by decide⟩
def lo3092 : CheckedMoment :=
  CheckedMoment.ofBessel lo3092b1 lo3092b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3092b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨13,by decide⟩
def hi3092b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨14,by decide⟩
def hi3092 : CheckedMoment :=
  CheckedMoment.ofBessel hi3092b1 hi3092b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3092 : meanBracketCheck (49941/50000) lo3092 hi3092=true := by decide +kernel
def bracket3092 : MeanBracket := meanBracketOfMoments (49941/50000) lo3092 hi3092 accepted3092
def lo3093b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨18,by decide⟩
def lo3093b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨19,by decide⟩
def lo3093 : CheckedMoment :=
  CheckedMoment.ofBessel lo3093b1 lo3093b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3093b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨23,by decide⟩
def hi3093b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨24,by decide⟩
def hi3093 : CheckedMoment :=
  CheckedMoment.ofBessel hi3093b1 hi3093b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3093 : meanBracketCheck (39953/40000) lo3093 hi3093=true := by decide +kernel
def bracket3093 : MeanBracket := meanBracketOfMoments (39953/40000) lo3093 hi3093 accepted3093
def lo3094b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨28,by decide⟩
def lo3094b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨29,by decide⟩
def lo3094 : CheckedMoment :=
  CheckedMoment.ofBessel lo3094b1 lo3094b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3094b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨33,by decide⟩
def hi3094b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨34,by decide⟩
def hi3094 : CheckedMoment :=
  CheckedMoment.ofBessel hi3094b1 hi3094b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3094 : meanBracketCheck (99883/100000) lo3094 hi3094=true := by decide +kernel
def bracket3094 : MeanBracket := meanBracketOfMoments (99883/100000) lo3094 hi3094 accepted3094
def lo3095b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨38,by decide⟩
def lo3095b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨39,by decide⟩
def lo3095 : CheckedMoment :=
  CheckedMoment.ofBessel lo3095b1 lo3095b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3095b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨43,by decide⟩
def hi3095b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨44,by decide⟩
def hi3095 : CheckedMoment :=
  CheckedMoment.ofBessel hi3095b1 hi3095b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3095 : meanBracketCheck (199767/200000) lo3095 hi3095=true := by decide +kernel
def bracket3095 : MeanBracket := meanBracketOfMoments (199767/200000) lo3095 hi3095 accepted3095
def lo3096b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨48,by decide⟩
def lo3096b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨49,by decide⟩
def lo3096 : CheckedMoment :=
  CheckedMoment.ofBessel lo3096b1 lo3096b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3096b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨53,by decide⟩
def hi3096b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨54,by decide⟩
def hi3096 : CheckedMoment :=
  CheckedMoment.ofBessel hi3096b1 hi3096b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3096 : meanBracketCheck (24971/25000) lo3096 hi3096=true := by decide +kernel
def bracket3096 : MeanBracket := meanBracketOfMoments (24971/25000) lo3096 hi3096 accepted3096
def lo3097b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨58,by decide⟩
def lo3097b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨59,by decide⟩
def lo3097 : CheckedMoment :=
  CheckedMoment.ofBessel lo3097b1 lo3097b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3097b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨63,by decide⟩
def hi3097b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨0,by decide⟩
def hi3097 : CheckedMoment :=
  CheckedMoment.ofBessel hi3097b1 hi3097b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3097 : meanBracketCheck (199769/200000) lo3097 hi3097=true := by decide +kernel
def bracket3097 : MeanBracket := meanBracketOfMoments (199769/200000) lo3097 hi3097 accepted3097
def lo3098b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨4,by decide⟩
def lo3098b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨5,by decide⟩
def lo3098 : CheckedMoment :=
  CheckedMoment.ofBessel lo3098b1 lo3098b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3098b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨9,by decide⟩
def hi3098b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨10,by decide⟩
def hi3098 : CheckedMoment :=
  CheckedMoment.ofBessel hi3098b1 hi3098b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3098 : meanBracketCheck (19977/20000) lo3098 hi3098=true := by decide +kernel
def bracket3098 : MeanBracket := meanBracketOfMoments (19977/20000) lo3098 hi3098 accepted3098
def lo3099b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨14,by decide⟩
def lo3099b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨15,by decide⟩
def lo3099 : CheckedMoment :=
  CheckedMoment.ofBessel lo3099b1 lo3099b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3099b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨19,by decide⟩
def hi3099b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨20,by decide⟩
def hi3099 : CheckedMoment :=
  CheckedMoment.ofBessel hi3099b1 hi3099b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3099 : meanBracketCheck (199771/200000) lo3099 hi3099=true := by decide +kernel
def bracket3099 : MeanBracket := meanBracketOfMoments (199771/200000) lo3099 hi3099 accepted3099
def lo3100b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨24,by decide⟩
def lo3100b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨25,by decide⟩
def lo3100 : CheckedMoment :=
  CheckedMoment.ofBessel lo3100b1 lo3100b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3100b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨29,by decide⟩
def hi3100b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨30,by decide⟩
def hi3100 : CheckedMoment :=
  CheckedMoment.ofBessel hi3100b1 hi3100b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3100 : meanBracketCheck (49943/50000) lo3100 hi3100=true := by decide +kernel
def bracket3100 : MeanBracket := meanBracketOfMoments (49943/50000) lo3100 hi3100 accepted3100
def lo3101b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨34,by decide⟩
def lo3101b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨35,by decide⟩
def lo3101 : CheckedMoment :=
  CheckedMoment.ofBessel lo3101b1 lo3101b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3101b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨39,by decide⟩
def hi3101b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨40,by decide⟩
def hi3101 : CheckedMoment :=
  CheckedMoment.ofBessel hi3101b1 hi3101b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3101 : meanBracketCheck (199773/200000) lo3101 hi3101=true := by decide +kernel
def bracket3101 : MeanBracket := meanBracketOfMoments (199773/200000) lo3101 hi3101 accepted3101
def lo3102b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨44,by decide⟩
def lo3102b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨45,by decide⟩
def lo3102 : CheckedMoment :=
  CheckedMoment.ofBessel lo3102b1 lo3102b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3102b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨49,by decide⟩
def hi3102b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨50,by decide⟩
def hi3102 : CheckedMoment :=
  CheckedMoment.ofBessel hi3102b1 hi3102b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3102 : meanBracketCheck (99887/100000) lo3102 hi3102=true := by decide +kernel
def bracket3102 : MeanBracket := meanBracketOfMoments (99887/100000) lo3102 hi3102 accepted3102
def lo3103b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨54,by decide⟩
def lo3103b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨55,by decide⟩
def lo3103 : CheckedMoment :=
  CheckedMoment.ofBessel lo3103b1 lo3103b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3103b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨59,by decide⟩
def hi3103b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨60,by decide⟩
def hi3103 : CheckedMoment :=
  CheckedMoment.ofBessel hi3103b1 hi3103b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3103 : meanBracketCheck (7991/8000) lo3103 hi3103=true := by decide +kernel
def bracket3103 : MeanBracket := meanBracketOfMoments (7991/8000) lo3103 hi3103 accepted3103
#print axioms bracket3088
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0193
