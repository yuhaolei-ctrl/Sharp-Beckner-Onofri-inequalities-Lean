import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0460
import BecknerOnofri.EntropyScalarCertificate.Bessel0461
import BecknerOnofri.EntropyScalarCertificate.Bessel0462
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0184
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2944b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨0,by decide⟩
def lo2944b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨1,by decide⟩
def lo2944 : CheckedMoment :=
  CheckedMoment.ofBessel lo2944b1 lo2944b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2944b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨5,by decide⟩
def hi2944b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨6,by decide⟩
def hi2944 : CheckedMoment :=
  CheckedMoment.ofBessel hi2944b1 hi2944b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2944 : meanBracketCheck (3119/3125) lo2944 hi2944=true := by decide +kernel
def bracket2944 : MeanBracket := meanBracketOfMoments (3119/3125) lo2944 hi2944 accepted2944
def lo2945b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨10,by decide⟩
def lo2945b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨11,by decide⟩
def lo2945 : CheckedMoment :=
  CheckedMoment.ofBessel lo2945b1 lo2945b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2945b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨15,by decide⟩
def hi2945b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨16,by decide⟩
def hi2945 : CheckedMoment :=
  CheckedMoment.ofBessel hi2945b1 hi2945b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2945 : meanBracketCheck (199617/200000) lo2945 hi2945=true := by decide +kernel
def bracket2945 : MeanBracket := meanBracketOfMoments (199617/200000) lo2945 hi2945 accepted2945
def lo2946b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨20,by decide⟩
def lo2946b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨21,by decide⟩
def lo2946 : CheckedMoment :=
  CheckedMoment.ofBessel lo2946b1 lo2946b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2946b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨25,by decide⟩
def hi2946b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨26,by decide⟩
def hi2946 : CheckedMoment :=
  CheckedMoment.ofBessel hi2946b1 hi2946b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2946 : meanBracketCheck (99809/100000) lo2946 hi2946=true := by decide +kernel
def bracket2946 : MeanBracket := meanBracketOfMoments (99809/100000) lo2946 hi2946 accepted2946
def lo2947b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨30,by decide⟩
def lo2947b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨31,by decide⟩
def lo2947 : CheckedMoment :=
  CheckedMoment.ofBessel lo2947b1 lo2947b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2947b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨35,by decide⟩
def hi2947b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨36,by decide⟩
def hi2947 : CheckedMoment :=
  CheckedMoment.ofBessel hi2947b1 hi2947b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2947 : meanBracketCheck (199619/200000) lo2947 hi2947=true := by decide +kernel
def bracket2947 : MeanBracket := meanBracketOfMoments (199619/200000) lo2947 hi2947 accepted2947
def lo2948b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨40,by decide⟩
def lo2948b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨41,by decide⟩
def lo2948 : CheckedMoment :=
  CheckedMoment.ofBessel lo2948b1 lo2948b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2948b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨45,by decide⟩
def hi2948b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨46,by decide⟩
def hi2948 : CheckedMoment :=
  CheckedMoment.ofBessel hi2948b1 hi2948b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2948 : meanBracketCheck (9981/10000) lo2948 hi2948=true := by decide +kernel
def bracket2948 : MeanBracket := meanBracketOfMoments (9981/10000) lo2948 hi2948 accepted2948
def lo2949b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨50,by decide⟩
def lo2949b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨51,by decide⟩
def lo2949 : CheckedMoment :=
  CheckedMoment.ofBessel lo2949b1 lo2949b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2949b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨55,by decide⟩
def hi2949b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨56,by decide⟩
def hi2949 : CheckedMoment :=
  CheckedMoment.ofBessel hi2949b1 hi2949b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2949 : meanBracketCheck (199621/200000) lo2949 hi2949=true := by decide +kernel
def bracket2949 : MeanBracket := meanBracketOfMoments (199621/200000) lo2949 hi2949 accepted2949
def lo2950b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨60,by decide⟩
def lo2950b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨61,by decide⟩
def lo2950 : CheckedMoment :=
  CheckedMoment.ofBessel lo2950b1 lo2950b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2950b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨1,by decide⟩
def hi2950b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨2,by decide⟩
def hi2950 : CheckedMoment :=
  CheckedMoment.ofBessel hi2950b1 hi2950b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2950 : meanBracketCheck (99811/100000) lo2950 hi2950=true := by decide +kernel
def bracket2950 : MeanBracket := meanBracketOfMoments (99811/100000) lo2950 hi2950 accepted2950
def lo2951b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨6,by decide⟩
def lo2951b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨7,by decide⟩
def lo2951 : CheckedMoment :=
  CheckedMoment.ofBessel lo2951b1 lo2951b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2951b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨11,by decide⟩
def hi2951b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨12,by decide⟩
def hi2951 : CheckedMoment :=
  CheckedMoment.ofBessel hi2951b1 hi2951b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2951 : meanBracketCheck (199623/200000) lo2951 hi2951=true := by decide +kernel
def bracket2951 : MeanBracket := meanBracketOfMoments (199623/200000) lo2951 hi2951 accepted2951
def lo2952b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨16,by decide⟩
def lo2952b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨17,by decide⟩
def lo2952 : CheckedMoment :=
  CheckedMoment.ofBessel lo2952b1 lo2952b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2952b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨21,by decide⟩
def hi2952b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨22,by decide⟩
def hi2952 : CheckedMoment :=
  CheckedMoment.ofBessel hi2952b1 hi2952b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2952 : meanBracketCheck (24953/25000) lo2952 hi2952=true := by decide +kernel
def bracket2952 : MeanBracket := meanBracketOfMoments (24953/25000) lo2952 hi2952 accepted2952
def lo2953b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨26,by decide⟩
def lo2953b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨27,by decide⟩
def lo2953 : CheckedMoment :=
  CheckedMoment.ofBessel lo2953b1 lo2953b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2953b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨31,by decide⟩
def hi2953b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨32,by decide⟩
def hi2953 : CheckedMoment :=
  CheckedMoment.ofBessel hi2953b1 hi2953b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2953 : meanBracketCheck (1597/1600) lo2953 hi2953=true := by decide +kernel
def bracket2953 : MeanBracket := meanBracketOfMoments (1597/1600) lo2953 hi2953 accepted2953
def lo2954b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨36,by decide⟩
def lo2954b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨37,by decide⟩
def lo2954 : CheckedMoment :=
  CheckedMoment.ofBessel lo2954b1 lo2954b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2954b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨41,by decide⟩
def hi2954b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨42,by decide⟩
def hi2954 : CheckedMoment :=
  CheckedMoment.ofBessel hi2954b1 hi2954b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2954 : meanBracketCheck (99813/100000) lo2954 hi2954=true := by decide +kernel
def bracket2954 : MeanBracket := meanBracketOfMoments (99813/100000) lo2954 hi2954 accepted2954
def lo2955b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨46,by decide⟩
def lo2955b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨47,by decide⟩
def lo2955 : CheckedMoment :=
  CheckedMoment.ofBessel lo2955b1 lo2955b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2955b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨51,by decide⟩
def hi2955b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨52,by decide⟩
def hi2955 : CheckedMoment :=
  CheckedMoment.ofBessel hi2955b1 hi2955b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2955 : meanBracketCheck (199627/200000) lo2955 hi2955=true := by decide +kernel
def bracket2955 : MeanBracket := meanBracketOfMoments (199627/200000) lo2955 hi2955 accepted2955
def lo2956b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨56,by decide⟩
def lo2956b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨57,by decide⟩
def lo2956 : CheckedMoment :=
  CheckedMoment.ofBessel lo2956b1 lo2956b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2956b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨61,by decide⟩
def hi2956b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨62,by decide⟩
def hi2956 : CheckedMoment :=
  CheckedMoment.ofBessel hi2956b1 hi2956b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2956 : meanBracketCheck (49907/50000) lo2956 hi2956=true := by decide +kernel
def bracket2956 : MeanBracket := meanBracketOfMoments (49907/50000) lo2956 hi2956 accepted2956
def lo2957b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨2,by decide⟩
def lo2957b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨3,by decide⟩
def lo2957 : CheckedMoment :=
  CheckedMoment.ofBessel lo2957b1 lo2957b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2957b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨7,by decide⟩
def hi2957b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨8,by decide⟩
def hi2957 : CheckedMoment :=
  CheckedMoment.ofBessel hi2957b1 hi2957b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2957 : meanBracketCheck (199629/200000) lo2957 hi2957=true := by decide +kernel
def bracket2957 : MeanBracket := meanBracketOfMoments (199629/200000) lo2957 hi2957 accepted2957
def lo2958b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨12,by decide⟩
def lo2958b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨13,by decide⟩
def lo2958 : CheckedMoment :=
  CheckedMoment.ofBessel lo2958b1 lo2958b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2958b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨17,by decide⟩
def hi2958b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨18,by decide⟩
def hi2958 : CheckedMoment :=
  CheckedMoment.ofBessel hi2958b1 hi2958b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2958 : meanBracketCheck (19963/20000) lo2958 hi2958=true := by decide +kernel
def bracket2958 : MeanBracket := meanBracketOfMoments (19963/20000) lo2958 hi2958 accepted2958
def lo2959b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨22,by decide⟩
def lo2959b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨23,by decide⟩
def lo2959 : CheckedMoment :=
  CheckedMoment.ofBessel lo2959b1 lo2959b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2959b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨27,by decide⟩
def hi2959b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨28,by decide⟩
def hi2959 : CheckedMoment :=
  CheckedMoment.ofBessel hi2959b1 hi2959b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2959 : meanBracketCheck (199631/200000) lo2959 hi2959=true := by decide +kernel
def bracket2959 : MeanBracket := meanBracketOfMoments (199631/200000) lo2959 hi2959 accepted2959
#print axioms bracket2944
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0184
