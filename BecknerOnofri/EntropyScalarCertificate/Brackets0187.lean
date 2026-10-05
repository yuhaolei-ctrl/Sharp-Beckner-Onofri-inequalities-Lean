import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0467
import BecknerOnofri.EntropyScalarCertificate.Bessel0468
import BecknerOnofri.EntropyScalarCertificate.Bessel0469
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0187
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2992b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨32,by decide⟩
def lo2992b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨33,by decide⟩
def lo2992 : CheckedMoment :=
  CheckedMoment.ofBessel lo2992b1 lo2992b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2992b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨37,by decide⟩
def hi2992b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨38,by decide⟩
def hi2992 : CheckedMoment :=
  CheckedMoment.ofBessel hi2992b1 hi2992b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2992 : meanBracketCheck (12479/12500) lo2992 hi2992=true := by decide +kernel
def bracket2992 : MeanBracket := meanBracketOfMoments (12479/12500) lo2992 hi2992 accepted2992
def lo2993b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨42,by decide⟩
def lo2993b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨43,by decide⟩
def lo2993 : CheckedMoment :=
  CheckedMoment.ofBessel lo2993b1 lo2993b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2993b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨47,by decide⟩
def hi2993b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨48,by decide⟩
def hi2993 : CheckedMoment :=
  CheckedMoment.ofBessel hi2993b1 hi2993b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2993 : meanBracketCheck (39933/40000) lo2993 hi2993=true := by decide +kernel
def bracket2993 : MeanBracket := meanBracketOfMoments (39933/40000) lo2993 hi2993 accepted2993
def lo2994b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨52,by decide⟩
def lo2994b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨53,by decide⟩
def lo2994 : CheckedMoment :=
  CheckedMoment.ofBessel lo2994b1 lo2994b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2994b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨57,by decide⟩
def hi2994b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨58,by decide⟩
def hi2994 : CheckedMoment :=
  CheckedMoment.ofBessel hi2994b1 hi2994b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2994 : meanBracketCheck (99833/100000) lo2994 hi2994=true := by decide +kernel
def bracket2994 : MeanBracket := meanBracketOfMoments (99833/100000) lo2994 hi2994 accepted2994
def lo2995b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨62,by decide⟩
def lo2995b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨63,by decide⟩
def lo2995 : CheckedMoment :=
  CheckedMoment.ofBessel lo2995b1 lo2995b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2995b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨3,by decide⟩
def hi2995b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨4,by decide⟩
def hi2995 : CheckedMoment :=
  CheckedMoment.ofBessel hi2995b1 hi2995b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2995 : meanBracketCheck (199667/200000) lo2995 hi2995=true := by decide +kernel
def bracket2995 : MeanBracket := meanBracketOfMoments (199667/200000) lo2995 hi2995 accepted2995
def lo2996b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨8,by decide⟩
def lo2996b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨9,by decide⟩
def lo2996 : CheckedMoment :=
  CheckedMoment.ofBessel lo2996b1 lo2996b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2996b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨13,by decide⟩
def hi2996b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨14,by decide⟩
def hi2996 : CheckedMoment :=
  CheckedMoment.ofBessel hi2996b1 hi2996b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2996 : meanBracketCheck (49917/50000) lo2996 hi2996=true := by decide +kernel
def bracket2996 : MeanBracket := meanBracketOfMoments (49917/50000) lo2996 hi2996 accepted2996
def lo2997b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨18,by decide⟩
def lo2997b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨19,by decide⟩
def lo2997 : CheckedMoment :=
  CheckedMoment.ofBessel lo2997b1 lo2997b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2997b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨23,by decide⟩
def hi2997b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨24,by decide⟩
def hi2997 : CheckedMoment :=
  CheckedMoment.ofBessel hi2997b1 hi2997b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2997 : meanBracketCheck (199669/200000) lo2997 hi2997=true := by decide +kernel
def bracket2997 : MeanBracket := meanBracketOfMoments (199669/200000) lo2997 hi2997 accepted2997
def lo2998b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨28,by decide⟩
def lo2998b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨29,by decide⟩
def lo2998 : CheckedMoment :=
  CheckedMoment.ofBessel lo2998b1 lo2998b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2998b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨33,by decide⟩
def hi2998b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨34,by decide⟩
def hi2998 : CheckedMoment :=
  CheckedMoment.ofBessel hi2998b1 hi2998b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2998 : meanBracketCheck (19967/20000) lo2998 hi2998=true := by decide +kernel
def bracket2998 : MeanBracket := meanBracketOfMoments (19967/20000) lo2998 hi2998 accepted2998
def lo2999b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨38,by decide⟩
def lo2999b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨39,by decide⟩
def lo2999 : CheckedMoment :=
  CheckedMoment.ofBessel lo2999b1 lo2999b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2999b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨43,by decide⟩
def hi2999b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨44,by decide⟩
def hi2999 : CheckedMoment :=
  CheckedMoment.ofBessel hi2999b1 hi2999b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2999 : meanBracketCheck (199671/200000) lo2999 hi2999=true := by decide +kernel
def bracket2999 : MeanBracket := meanBracketOfMoments (199671/200000) lo2999 hi2999 accepted2999
def lo3000b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨48,by decide⟩
def lo3000b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨49,by decide⟩
def lo3000 : CheckedMoment :=
  CheckedMoment.ofBessel lo3000b1 lo3000b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3000b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨53,by decide⟩
def hi3000b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨54,by decide⟩
def hi3000 : CheckedMoment :=
  CheckedMoment.ofBessel hi3000b1 hi3000b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3000 : meanBracketCheck (24959/25000) lo3000 hi3000=true := by decide +kernel
def bracket3000 : MeanBracket := meanBracketOfMoments (24959/25000) lo3000 hi3000 accepted3000
def lo3001b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨58,by decide⟩
def lo3001b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨59,by decide⟩
def lo3001 : CheckedMoment :=
  CheckedMoment.ofBessel lo3001b1 lo3001b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3001b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0468.rows BesselBatch0468.accepted ⟨63,by decide⟩
def hi3001b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨0,by decide⟩
def hi3001 : CheckedMoment :=
  CheckedMoment.ofBessel hi3001b1 hi3001b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3001 : meanBracketCheck (199673/200000) lo3001 hi3001=true := by decide +kernel
def bracket3001 : MeanBracket := meanBracketOfMoments (199673/200000) lo3001 hi3001 accepted3001
def lo3002b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨4,by decide⟩
def lo3002b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨5,by decide⟩
def lo3002 : CheckedMoment :=
  CheckedMoment.ofBessel lo3002b1 lo3002b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3002b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨9,by decide⟩
def hi3002b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨10,by decide⟩
def hi3002 : CheckedMoment :=
  CheckedMoment.ofBessel hi3002b1 hi3002b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3002 : meanBracketCheck (99837/100000) lo3002 hi3002=true := by decide +kernel
def bracket3002 : MeanBracket := meanBracketOfMoments (99837/100000) lo3002 hi3002 accepted3002
def lo3003b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨14,by decide⟩
def lo3003b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨15,by decide⟩
def lo3003 : CheckedMoment :=
  CheckedMoment.ofBessel lo3003b1 lo3003b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3003b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨19,by decide⟩
def hi3003b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨20,by decide⟩
def hi3003 : CheckedMoment :=
  CheckedMoment.ofBessel hi3003b1 hi3003b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3003 : meanBracketCheck (7987/8000) lo3003 hi3003=true := by decide +kernel
def bracket3003 : MeanBracket := meanBracketOfMoments (7987/8000) lo3003 hi3003 accepted3003
def lo3004b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨24,by decide⟩
def lo3004b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨25,by decide⟩
def lo3004 : CheckedMoment :=
  CheckedMoment.ofBessel lo3004b1 lo3004b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3004b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨29,by decide⟩
def hi3004b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨30,by decide⟩
def hi3004 : CheckedMoment :=
  CheckedMoment.ofBessel hi3004b1 hi3004b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3004 : meanBracketCheck (49919/50000) lo3004 hi3004=true := by decide +kernel
def bracket3004 : MeanBracket := meanBracketOfMoments (49919/50000) lo3004 hi3004 accepted3004
def lo3005b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨34,by decide⟩
def lo3005b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨35,by decide⟩
def lo3005 : CheckedMoment :=
  CheckedMoment.ofBessel lo3005b1 lo3005b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3005b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨39,by decide⟩
def hi3005b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨40,by decide⟩
def hi3005 : CheckedMoment :=
  CheckedMoment.ofBessel hi3005b1 hi3005b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3005 : meanBracketCheck (199677/200000) lo3005 hi3005=true := by decide +kernel
def bracket3005 : MeanBracket := meanBracketOfMoments (199677/200000) lo3005 hi3005 accepted3005
def lo3006b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨44,by decide⟩
def lo3006b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨45,by decide⟩
def lo3006 : CheckedMoment :=
  CheckedMoment.ofBessel lo3006b1 lo3006b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3006b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨49,by decide⟩
def hi3006b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨50,by decide⟩
def hi3006 : CheckedMoment :=
  CheckedMoment.ofBessel hi3006b1 hi3006b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3006 : meanBracketCheck (99839/100000) lo3006 hi3006=true := by decide +kernel
def bracket3006 : MeanBracket := meanBracketOfMoments (99839/100000) lo3006 hi3006 accepted3006
def lo3007b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨54,by decide⟩
def lo3007b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨55,by decide⟩
def lo3007 : CheckedMoment :=
  CheckedMoment.ofBessel lo3007b1 lo3007b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3007b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨59,by decide⟩
def hi3007b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0469.rows BesselBatch0469.accepted ⟨60,by decide⟩
def hi3007 : CheckedMoment :=
  CheckedMoment.ofBessel hi3007b1 hi3007b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3007 : meanBracketCheck (199679/200000) lo3007 hi3007=true := by decide +kernel
def bracket3007 : MeanBracket := meanBracketOfMoments (199679/200000) lo3007 hi3007 accepted3007
#print axioms bracket2992
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0187
