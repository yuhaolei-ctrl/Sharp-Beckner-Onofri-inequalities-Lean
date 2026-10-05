module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0462
public import BecknerOnofri.EntropyScalarCertificate.Bessel0463
public import BecknerOnofri.EntropyScalarCertificate.Bessel0464

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0185
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2960b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨32,by decide⟩
def lo2960b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨33,by decide⟩
def lo2960 : CheckedMoment :=
  CheckedMoment.ofBessel lo2960b1 lo2960b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2960b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨37,by decide⟩
def hi2960b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨38,by decide⟩
def hi2960 : CheckedMoment :=
  CheckedMoment.ofBessel hi2960b1 hi2960b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2960 : meanBracketCheck (12477/12500) lo2960 hi2960=true := by decide +kernel
def bracket2960 : MeanBracket := meanBracketOfMoments (12477/12500) lo2960 hi2960 accepted2960
def lo2961b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨42,by decide⟩
def lo2961b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨43,by decide⟩
def lo2961 : CheckedMoment :=
  CheckedMoment.ofBessel lo2961b1 lo2961b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2961b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨47,by decide⟩
def hi2961b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨48,by decide⟩
def hi2961 : CheckedMoment :=
  CheckedMoment.ofBessel hi2961b1 hi2961b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2961 : meanBracketCheck (199633/200000) lo2961 hi2961=true := by decide +kernel
def bracket2961 : MeanBracket := meanBracketOfMoments (199633/200000) lo2961 hi2961 accepted2961
def lo2962b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨52,by decide⟩
def lo2962b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨53,by decide⟩
def lo2962 : CheckedMoment :=
  CheckedMoment.ofBessel lo2962b1 lo2962b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2962b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨57,by decide⟩
def hi2962b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨58,by decide⟩
def hi2962 : CheckedMoment :=
  CheckedMoment.ofBessel hi2962b1 hi2962b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2962 : meanBracketCheck (99817/100000) lo2962 hi2962=true := by decide +kernel
def bracket2962 : MeanBracket := meanBracketOfMoments (99817/100000) lo2962 hi2962 accepted2962
def lo2963b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨62,by decide⟩
def lo2963b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨63,by decide⟩
def lo2963 : CheckedMoment :=
  CheckedMoment.ofBessel lo2963b1 lo2963b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2963b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨3,by decide⟩
def hi2963b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨4,by decide⟩
def hi2963 : CheckedMoment :=
  CheckedMoment.ofBessel hi2963b1 hi2963b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2963 : meanBracketCheck (39927/40000) lo2963 hi2963=true := by decide +kernel
def bracket2963 : MeanBracket := meanBracketOfMoments (39927/40000) lo2963 hi2963 accepted2963
def lo2964b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨8,by decide⟩
def lo2964b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨9,by decide⟩
def lo2964 : CheckedMoment :=
  CheckedMoment.ofBessel lo2964b1 lo2964b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2964b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨13,by decide⟩
def hi2964b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨14,by decide⟩
def hi2964 : CheckedMoment :=
  CheckedMoment.ofBessel hi2964b1 hi2964b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2964 : meanBracketCheck (49909/50000) lo2964 hi2964=true := by decide +kernel
def bracket2964 : MeanBracket := meanBracketOfMoments (49909/50000) lo2964 hi2964 accepted2964
def lo2965b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨18,by decide⟩
def lo2965b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨19,by decide⟩
def lo2965 : CheckedMoment :=
  CheckedMoment.ofBessel lo2965b1 lo2965b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2965b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨23,by decide⟩
def hi2965b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨24,by decide⟩
def hi2965 : CheckedMoment :=
  CheckedMoment.ofBessel hi2965b1 hi2965b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2965 : meanBracketCheck (199637/200000) lo2965 hi2965=true := by decide +kernel
def bracket2965 : MeanBracket := meanBracketOfMoments (199637/200000) lo2965 hi2965 accepted2965
def lo2966b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨28,by decide⟩
def lo2966b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨29,by decide⟩
def lo2966 : CheckedMoment :=
  CheckedMoment.ofBessel lo2966b1 lo2966b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2966b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨33,by decide⟩
def hi2966b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨34,by decide⟩
def hi2966 : CheckedMoment :=
  CheckedMoment.ofBessel hi2966b1 hi2966b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2966 : meanBracketCheck (99819/100000) lo2966 hi2966=true := by decide +kernel
def bracket2966 : MeanBracket := meanBracketOfMoments (99819/100000) lo2966 hi2966 accepted2966
def lo2967b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨38,by decide⟩
def lo2967b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨39,by decide⟩
def lo2967 : CheckedMoment :=
  CheckedMoment.ofBessel lo2967b1 lo2967b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2967b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨43,by decide⟩
def hi2967b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨44,by decide⟩
def hi2967 : CheckedMoment :=
  CheckedMoment.ofBessel hi2967b1 hi2967b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2967 : meanBracketCheck (199639/200000) lo2967 hi2967=true := by decide +kernel
def bracket2967 : MeanBracket := meanBracketOfMoments (199639/200000) lo2967 hi2967 accepted2967
def lo2968b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨48,by decide⟩
def lo2968b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨49,by decide⟩
def lo2968 : CheckedMoment :=
  CheckedMoment.ofBessel lo2968b1 lo2968b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2968b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨53,by decide⟩
def hi2968b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨54,by decide⟩
def hi2968 : CheckedMoment :=
  CheckedMoment.ofBessel hi2968b1 hi2968b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2968 : meanBracketCheck (4991/5000) lo2968 hi2968=true := by decide +kernel
def bracket2968 : MeanBracket := meanBracketOfMoments (4991/5000) lo2968 hi2968 accepted2968
def lo2969b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨58,by decide⟩
def lo2969b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨59,by decide⟩
def lo2969 : CheckedMoment :=
  CheckedMoment.ofBessel lo2969b1 lo2969b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2969b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0463.rows BesselBatch0463.accepted ⟨63,by decide⟩
def hi2969b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨0,by decide⟩
def hi2969 : CheckedMoment :=
  CheckedMoment.ofBessel hi2969b1 hi2969b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2969 : meanBracketCheck (199641/200000) lo2969 hi2969=true := by decide +kernel
def bracket2969 : MeanBracket := meanBracketOfMoments (199641/200000) lo2969 hi2969 accepted2969
def lo2970b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨4,by decide⟩
def lo2970b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨5,by decide⟩
def lo2970 : CheckedMoment :=
  CheckedMoment.ofBessel lo2970b1 lo2970b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2970b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨9,by decide⟩
def hi2970b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨10,by decide⟩
def hi2970 : CheckedMoment :=
  CheckedMoment.ofBessel hi2970b1 hi2970b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2970 : meanBracketCheck (99821/100000) lo2970 hi2970=true := by decide +kernel
def bracket2970 : MeanBracket := meanBracketOfMoments (99821/100000) lo2970 hi2970 accepted2970
def lo2971b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨14,by decide⟩
def lo2971b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨15,by decide⟩
def lo2971 : CheckedMoment :=
  CheckedMoment.ofBessel lo2971b1 lo2971b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2971b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨19,by decide⟩
def hi2971b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨20,by decide⟩
def hi2971 : CheckedMoment :=
  CheckedMoment.ofBessel hi2971b1 hi2971b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2971 : meanBracketCheck (199643/200000) lo2971 hi2971=true := by decide +kernel
def bracket2971 : MeanBracket := meanBracketOfMoments (199643/200000) lo2971 hi2971 accepted2971
def lo2972b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨24,by decide⟩
def lo2972b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨25,by decide⟩
def lo2972 : CheckedMoment :=
  CheckedMoment.ofBessel lo2972b1 lo2972b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2972b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨29,by decide⟩
def hi2972b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨30,by decide⟩
def hi2972 : CheckedMoment :=
  CheckedMoment.ofBessel hi2972b1 hi2972b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2972 : meanBracketCheck (49911/50000) lo2972 hi2972=true := by decide +kernel
def bracket2972 : MeanBracket := meanBracketOfMoments (49911/50000) lo2972 hi2972 accepted2972
def lo2973b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨34,by decide⟩
def lo2973b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨35,by decide⟩
def lo2973 : CheckedMoment :=
  CheckedMoment.ofBessel lo2973b1 lo2973b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2973b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨39,by decide⟩
def hi2973b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨40,by decide⟩
def hi2973 : CheckedMoment :=
  CheckedMoment.ofBessel hi2973b1 hi2973b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2973 : meanBracketCheck (39929/40000) lo2973 hi2973=true := by decide +kernel
def bracket2973 : MeanBracket := meanBracketOfMoments (39929/40000) lo2973 hi2973 accepted2973
def lo2974b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨44,by decide⟩
def lo2974b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨45,by decide⟩
def lo2974 : CheckedMoment :=
  CheckedMoment.ofBessel lo2974b1 lo2974b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2974b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨49,by decide⟩
def hi2974b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨50,by decide⟩
def hi2974 : CheckedMoment :=
  CheckedMoment.ofBessel hi2974b1 hi2974b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2974 : meanBracketCheck (99823/100000) lo2974 hi2974=true := by decide +kernel
def bracket2974 : MeanBracket := meanBracketOfMoments (99823/100000) lo2974 hi2974 accepted2974
def lo2975b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨54,by decide⟩
def lo2975b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨55,by decide⟩
def lo2975 : CheckedMoment :=
  CheckedMoment.ofBessel lo2975b1 lo2975b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2975b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨59,by decide⟩
def hi2975b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0464.rows BesselBatch0464.accepted ⟨60,by decide⟩
def hi2975 : CheckedMoment :=
  CheckedMoment.ofBessel hi2975b1 hi2975b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2975 : meanBracketCheck (199647/200000) lo2975 hi2975=true := by decide +kernel
def bracket2975 : MeanBracket := meanBracketOfMoments (199647/200000) lo2975 hi2975 accepted2975
#print axioms bracket2960
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0185
