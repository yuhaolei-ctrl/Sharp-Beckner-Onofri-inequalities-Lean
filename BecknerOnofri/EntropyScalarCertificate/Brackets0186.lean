import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0465
import BecknerOnofri.EntropyScalarCertificate.Bessel0466
import BecknerOnofri.EntropyScalarCertificate.Bessel0467
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0186
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2976b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨0,by decide⟩
def lo2976b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨1,by decide⟩
def lo2976 : CheckedMoment :=
  CheckedMoment.ofBessel lo2976b1 lo2976b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2976b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨5,by decide⟩
def hi2976b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨6,by decide⟩
def hi2976 : CheckedMoment :=
  CheckedMoment.ofBessel hi2976b1 hi2976b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2976 : meanBracketCheck (6239/6250) lo2976 hi2976=true := by decide +kernel
def bracket2976 : MeanBracket := meanBracketOfMoments (6239/6250) lo2976 hi2976 accepted2976
def lo2977b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨10,by decide⟩
def lo2977b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨11,by decide⟩
def lo2977 : CheckedMoment :=
  CheckedMoment.ofBessel lo2977b1 lo2977b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2977b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨15,by decide⟩
def hi2977b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨16,by decide⟩
def hi2977 : CheckedMoment :=
  CheckedMoment.ofBessel hi2977b1 hi2977b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2977 : meanBracketCheck (199649/200000) lo2977 hi2977=true := by decide +kernel
def bracket2977 : MeanBracket := meanBracketOfMoments (199649/200000) lo2977 hi2977 accepted2977
def lo2978b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨20,by decide⟩
def lo2978b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨21,by decide⟩
def lo2978 : CheckedMoment :=
  CheckedMoment.ofBessel lo2978b1 lo2978b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2978b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨25,by decide⟩
def hi2978b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨26,by decide⟩
def hi2978 : CheckedMoment :=
  CheckedMoment.ofBessel hi2978b1 hi2978b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2978 : meanBracketCheck (3993/4000) lo2978 hi2978=true := by decide +kernel
def bracket2978 : MeanBracket := meanBracketOfMoments (3993/4000) lo2978 hi2978 accepted2978
def lo2979b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨30,by decide⟩
def lo2979b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨31,by decide⟩
def lo2979 : CheckedMoment :=
  CheckedMoment.ofBessel lo2979b1 lo2979b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2979b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨35,by decide⟩
def hi2979b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨36,by decide⟩
def hi2979 : CheckedMoment :=
  CheckedMoment.ofBessel hi2979b1 hi2979b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2979 : meanBracketCheck (199651/200000) lo2979 hi2979=true := by decide +kernel
def bracket2979 : MeanBracket := meanBracketOfMoments (199651/200000) lo2979 hi2979 accepted2979
def lo2980b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨40,by decide⟩
def lo2980b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨41,by decide⟩
def lo2980 : CheckedMoment :=
  CheckedMoment.ofBessel lo2980b1 lo2980b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2980b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨45,by decide⟩
def hi2980b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨46,by decide⟩
def hi2980 : CheckedMoment :=
  CheckedMoment.ofBessel hi2980b1 hi2980b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2980 : meanBracketCheck (49913/50000) lo2980 hi2980=true := by decide +kernel
def bracket2980 : MeanBracket := meanBracketOfMoments (49913/50000) lo2980 hi2980 accepted2980
def lo2981b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨50,by decide⟩
def lo2981b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨51,by decide⟩
def lo2981 : CheckedMoment :=
  CheckedMoment.ofBessel lo2981b1 lo2981b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2981b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨55,by decide⟩
def hi2981b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨56,by decide⟩
def hi2981 : CheckedMoment :=
  CheckedMoment.ofBessel hi2981b1 hi2981b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2981 : meanBracketCheck (199653/200000) lo2981 hi2981=true := by decide +kernel
def bracket2981 : MeanBracket := meanBracketOfMoments (199653/200000) lo2981 hi2981 accepted2981
def lo2982b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨60,by decide⟩
def lo2982b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨61,by decide⟩
def lo2982 : CheckedMoment :=
  CheckedMoment.ofBessel lo2982b1 lo2982b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2982b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨1,by decide⟩
def hi2982b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨2,by decide⟩
def hi2982 : CheckedMoment :=
  CheckedMoment.ofBessel hi2982b1 hi2982b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2982 : meanBracketCheck (99827/100000) lo2982 hi2982=true := by decide +kernel
def bracket2982 : MeanBracket := meanBracketOfMoments (99827/100000) lo2982 hi2982 accepted2982
def lo2983b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨6,by decide⟩
def lo2983b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨7,by decide⟩
def lo2983 : CheckedMoment :=
  CheckedMoment.ofBessel lo2983b1 lo2983b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2983b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨11,by decide⟩
def hi2983b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨12,by decide⟩
def hi2983 : CheckedMoment :=
  CheckedMoment.ofBessel hi2983b1 hi2983b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2983 : meanBracketCheck (39931/40000) lo2983 hi2983=true := by decide +kernel
def bracket2983 : MeanBracket := meanBracketOfMoments (39931/40000) lo2983 hi2983 accepted2983
def lo2984b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨16,by decide⟩
def lo2984b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨17,by decide⟩
def lo2984 : CheckedMoment :=
  CheckedMoment.ofBessel lo2984b1 lo2984b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2984b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨21,by decide⟩
def hi2984b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨22,by decide⟩
def hi2984 : CheckedMoment :=
  CheckedMoment.ofBessel hi2984b1 hi2984b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2984 : meanBracketCheck (24957/25000) lo2984 hi2984=true := by decide +kernel
def bracket2984 : MeanBracket := meanBracketOfMoments (24957/25000) lo2984 hi2984 accepted2984
def lo2985b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨26,by decide⟩
def lo2985b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨27,by decide⟩
def lo2985 : CheckedMoment :=
  CheckedMoment.ofBessel lo2985b1 lo2985b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2985b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨31,by decide⟩
def hi2985b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨32,by decide⟩
def hi2985 : CheckedMoment :=
  CheckedMoment.ofBessel hi2985b1 hi2985b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2985 : meanBracketCheck (199657/200000) lo2985 hi2985=true := by decide +kernel
def bracket2985 : MeanBracket := meanBracketOfMoments (199657/200000) lo2985 hi2985 accepted2985
def lo2986b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨36,by decide⟩
def lo2986b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨37,by decide⟩
def lo2986 : CheckedMoment :=
  CheckedMoment.ofBessel lo2986b1 lo2986b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2986b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨41,by decide⟩
def hi2986b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨42,by decide⟩
def hi2986 : CheckedMoment :=
  CheckedMoment.ofBessel hi2986b1 hi2986b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2986 : meanBracketCheck (99829/100000) lo2986 hi2986=true := by decide +kernel
def bracket2986 : MeanBracket := meanBracketOfMoments (99829/100000) lo2986 hi2986 accepted2986
def lo2987b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨46,by decide⟩
def lo2987b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨47,by decide⟩
def lo2987 : CheckedMoment :=
  CheckedMoment.ofBessel lo2987b1 lo2987b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2987b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨51,by decide⟩
def hi2987b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨52,by decide⟩
def hi2987 : CheckedMoment :=
  CheckedMoment.ofBessel hi2987b1 hi2987b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2987 : meanBracketCheck (199659/200000) lo2987 hi2987=true := by decide +kernel
def bracket2987 : MeanBracket := meanBracketOfMoments (199659/200000) lo2987 hi2987 accepted2987
def lo2988b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨56,by decide⟩
def lo2988b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨57,by decide⟩
def lo2988 : CheckedMoment :=
  CheckedMoment.ofBessel lo2988b1 lo2988b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2988b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨61,by decide⟩
def hi2988b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨62,by decide⟩
def hi2988 : CheckedMoment :=
  CheckedMoment.ofBessel hi2988b1 hi2988b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2988 : meanBracketCheck (9983/10000) lo2988 hi2988=true := by decide +kernel
def bracket2988 : MeanBracket := meanBracketOfMoments (9983/10000) lo2988 hi2988 accepted2988
def lo2989b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨2,by decide⟩
def lo2989b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨3,by decide⟩
def lo2989 : CheckedMoment :=
  CheckedMoment.ofBessel lo2989b1 lo2989b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2989b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨7,by decide⟩
def hi2989b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨8,by decide⟩
def hi2989 : CheckedMoment :=
  CheckedMoment.ofBessel hi2989b1 hi2989b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2989 : meanBracketCheck (199661/200000) lo2989 hi2989=true := by decide +kernel
def bracket2989 : MeanBracket := meanBracketOfMoments (199661/200000) lo2989 hi2989 accepted2989
def lo2990b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨12,by decide⟩
def lo2990b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨13,by decide⟩
def lo2990 : CheckedMoment :=
  CheckedMoment.ofBessel lo2990b1 lo2990b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2990b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨17,by decide⟩
def hi2990b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨18,by decide⟩
def hi2990 : CheckedMoment :=
  CheckedMoment.ofBessel hi2990b1 hi2990b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2990 : meanBracketCheck (99831/100000) lo2990 hi2990=true := by decide +kernel
def bracket2990 : MeanBracket := meanBracketOfMoments (99831/100000) lo2990 hi2990 accepted2990
def lo2991b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨22,by decide⟩
def lo2991b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨23,by decide⟩
def lo2991 : CheckedMoment :=
  CheckedMoment.ofBessel lo2991b1 lo2991b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2991b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨27,by decide⟩
def hi2991b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0467.rows BesselBatch0467.accepted ⟨28,by decide⟩
def hi2991 : CheckedMoment :=
  CheckedMoment.ofBessel hi2991b1 hi2991b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2991 : meanBracketCheck (199663/200000) lo2991 hi2991=true := by decide +kernel
def bracket2991 : MeanBracket := meanBracketOfMoments (199663/200000) lo2991 hi2991 accepted2991
#print axioms bracket2976
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0186
