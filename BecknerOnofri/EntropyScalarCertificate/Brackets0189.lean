module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0472
public import BecknerOnofri.EntropyScalarCertificate.Bessel0473
public import BecknerOnofri.EntropyScalarCertificate.Bessel0474

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0189
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo3024b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨32,by decide⟩
def lo3024b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨33,by decide⟩
def lo3024 : CheckedMoment :=
  CheckedMoment.ofBessel lo3024b1 lo3024b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3024b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨37,by decide⟩
def hi3024b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨38,by decide⟩
def hi3024 : CheckedMoment :=
  CheckedMoment.ofBessel hi3024b1 hi3024b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3024 : meanBracketCheck (12481/12500) lo3024 hi3024=true := by decide +kernel
def bracket3024 : MeanBracket := meanBracketOfMoments (12481/12500) lo3024 hi3024 accepted3024
def lo3025b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨42,by decide⟩
def lo3025b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨43,by decide⟩
def lo3025 : CheckedMoment :=
  CheckedMoment.ofBessel lo3025b1 lo3025b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3025b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨47,by decide⟩
def hi3025b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨48,by decide⟩
def hi3025 : CheckedMoment :=
  CheckedMoment.ofBessel hi3025b1 hi3025b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3025 : meanBracketCheck (199697/200000) lo3025 hi3025=true := by decide +kernel
def bracket3025 : MeanBracket := meanBracketOfMoments (199697/200000) lo3025 hi3025 accepted3025
def lo3026b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨52,by decide⟩
def lo3026b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨53,by decide⟩
def lo3026 : CheckedMoment :=
  CheckedMoment.ofBessel lo3026b1 lo3026b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3026b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨57,by decide⟩
def hi3026b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨58,by decide⟩
def hi3026 : CheckedMoment :=
  CheckedMoment.ofBessel hi3026b1 hi3026b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3026 : meanBracketCheck (99849/100000) lo3026 hi3026=true := by decide +kernel
def bracket3026 : MeanBracket := meanBracketOfMoments (99849/100000) lo3026 hi3026 accepted3026
def lo3027b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨62,by decide⟩
def lo3027b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨63,by decide⟩
def lo3027 : CheckedMoment :=
  CheckedMoment.ofBessel lo3027b1 lo3027b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3027b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨3,by decide⟩
def hi3027b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨4,by decide⟩
def hi3027 : CheckedMoment :=
  CheckedMoment.ofBessel hi3027b1 hi3027b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3027 : meanBracketCheck (199699/200000) lo3027 hi3027=true := by decide +kernel
def bracket3027 : MeanBracket := meanBracketOfMoments (199699/200000) lo3027 hi3027 accepted3027
def lo3028b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨8,by decide⟩
def lo3028b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨9,by decide⟩
def lo3028 : CheckedMoment :=
  CheckedMoment.ofBessel lo3028b1 lo3028b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3028b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨13,by decide⟩
def hi3028b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨14,by decide⟩
def hi3028 : CheckedMoment :=
  CheckedMoment.ofBessel hi3028b1 hi3028b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3028 : meanBracketCheck (1997/2000) lo3028 hi3028=true := by decide +kernel
def bracket3028 : MeanBracket := meanBracketOfMoments (1997/2000) lo3028 hi3028 accepted3028
def lo3029b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨18,by decide⟩
def lo3029b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨19,by decide⟩
def lo3029 : CheckedMoment :=
  CheckedMoment.ofBessel lo3029b1 lo3029b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3029b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨23,by decide⟩
def hi3029b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨24,by decide⟩
def hi3029 : CheckedMoment :=
  CheckedMoment.ofBessel hi3029b1 hi3029b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3029 : meanBracketCheck (199701/200000) lo3029 hi3029=true := by decide +kernel
def bracket3029 : MeanBracket := meanBracketOfMoments (199701/200000) lo3029 hi3029 accepted3029
def lo3030b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨28,by decide⟩
def lo3030b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨29,by decide⟩
def lo3030 : CheckedMoment :=
  CheckedMoment.ofBessel lo3030b1 lo3030b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3030b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨33,by decide⟩
def hi3030b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨34,by decide⟩
def hi3030 : CheckedMoment :=
  CheckedMoment.ofBessel hi3030b1 hi3030b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3030 : meanBracketCheck (99851/100000) lo3030 hi3030=true := by decide +kernel
def bracket3030 : MeanBracket := meanBracketOfMoments (99851/100000) lo3030 hi3030 accepted3030
def lo3031b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨38,by decide⟩
def lo3031b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨39,by decide⟩
def lo3031 : CheckedMoment :=
  CheckedMoment.ofBessel lo3031b1 lo3031b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3031b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨43,by decide⟩
def hi3031b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨44,by decide⟩
def hi3031 : CheckedMoment :=
  CheckedMoment.ofBessel hi3031b1 hi3031b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3031 : meanBracketCheck (199703/200000) lo3031 hi3031=true := by decide +kernel
def bracket3031 : MeanBracket := meanBracketOfMoments (199703/200000) lo3031 hi3031 accepted3031
def lo3032b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨48,by decide⟩
def lo3032b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨49,by decide⟩
def lo3032 : CheckedMoment :=
  CheckedMoment.ofBessel lo3032b1 lo3032b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3032b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨53,by decide⟩
def hi3032b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨54,by decide⟩
def hi3032 : CheckedMoment :=
  CheckedMoment.ofBessel hi3032b1 hi3032b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3032 : meanBracketCheck (24963/25000) lo3032 hi3032=true := by decide +kernel
def bracket3032 : MeanBracket := meanBracketOfMoments (24963/25000) lo3032 hi3032 accepted3032
def lo3033b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨58,by decide⟩
def lo3033b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨59,by decide⟩
def lo3033 : CheckedMoment :=
  CheckedMoment.ofBessel lo3033b1 lo3033b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3033b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨63,by decide⟩
def hi3033b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨0,by decide⟩
def hi3033 : CheckedMoment :=
  CheckedMoment.ofBessel hi3033b1 hi3033b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3033 : meanBracketCheck (39941/40000) lo3033 hi3033=true := by decide +kernel
def bracket3033 : MeanBracket := meanBracketOfMoments (39941/40000) lo3033 hi3033 accepted3033
def lo3034b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨4,by decide⟩
def lo3034b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨5,by decide⟩
def lo3034 : CheckedMoment :=
  CheckedMoment.ofBessel lo3034b1 lo3034b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3034b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨9,by decide⟩
def hi3034b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨10,by decide⟩
def hi3034 : CheckedMoment :=
  CheckedMoment.ofBessel hi3034b1 hi3034b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3034 : meanBracketCheck (99853/100000) lo3034 hi3034=true := by decide +kernel
def bracket3034 : MeanBracket := meanBracketOfMoments (99853/100000) lo3034 hi3034 accepted3034
def lo3035b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨14,by decide⟩
def lo3035b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨15,by decide⟩
def lo3035 : CheckedMoment :=
  CheckedMoment.ofBessel lo3035b1 lo3035b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3035b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨19,by decide⟩
def hi3035b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨20,by decide⟩
def hi3035 : CheckedMoment :=
  CheckedMoment.ofBessel hi3035b1 hi3035b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3035 : meanBracketCheck (199707/200000) lo3035 hi3035=true := by decide +kernel
def bracket3035 : MeanBracket := meanBracketOfMoments (199707/200000) lo3035 hi3035 accepted3035
def lo3036b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨24,by decide⟩
def lo3036b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨25,by decide⟩
def lo3036 : CheckedMoment :=
  CheckedMoment.ofBessel lo3036b1 lo3036b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3036b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨29,by decide⟩
def hi3036b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨30,by decide⟩
def hi3036 : CheckedMoment :=
  CheckedMoment.ofBessel hi3036b1 hi3036b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3036 : meanBracketCheck (49927/50000) lo3036 hi3036=true := by decide +kernel
def bracket3036 : MeanBracket := meanBracketOfMoments (49927/50000) lo3036 hi3036 accepted3036
def lo3037b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨34,by decide⟩
def lo3037b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨35,by decide⟩
def lo3037 : CheckedMoment :=
  CheckedMoment.ofBessel lo3037b1 lo3037b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3037b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨39,by decide⟩
def hi3037b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨40,by decide⟩
def hi3037 : CheckedMoment :=
  CheckedMoment.ofBessel hi3037b1 hi3037b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3037 : meanBracketCheck (199709/200000) lo3037 hi3037=true := by decide +kernel
def bracket3037 : MeanBracket := meanBracketOfMoments (199709/200000) lo3037 hi3037 accepted3037
def lo3038b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨44,by decide⟩
def lo3038b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨45,by decide⟩
def lo3038 : CheckedMoment :=
  CheckedMoment.ofBessel lo3038b1 lo3038b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3038b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨49,by decide⟩
def hi3038b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨50,by decide⟩
def hi3038 : CheckedMoment :=
  CheckedMoment.ofBessel hi3038b1 hi3038b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3038 : meanBracketCheck (19971/20000) lo3038 hi3038=true := by decide +kernel
def bracket3038 : MeanBracket := meanBracketOfMoments (19971/20000) lo3038 hi3038 accepted3038
def lo3039b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨54,by decide⟩
def lo3039b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨55,by decide⟩
def lo3039 : CheckedMoment :=
  CheckedMoment.ofBessel lo3039b1 lo3039b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3039b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨59,by decide⟩
def hi3039b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨60,by decide⟩
def hi3039 : CheckedMoment :=
  CheckedMoment.ofBessel hi3039b1 hi3039b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3039 : meanBracketCheck (199711/200000) lo3039 hi3039=true := by decide +kernel
def bracket3039 : MeanBracket := meanBracketOfMoments (199711/200000) lo3039 hi3039 accepted3039
#print axioms bracket3024
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0189
