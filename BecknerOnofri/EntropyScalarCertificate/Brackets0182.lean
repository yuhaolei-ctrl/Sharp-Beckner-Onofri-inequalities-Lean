import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0455
import BecknerOnofri.EntropyScalarCertificate.Bessel0456
import BecknerOnofri.EntropyScalarCertificate.Bessel0457
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0182
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2912b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨0,by decide⟩
def lo2912b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨1,by decide⟩
def lo2912 : CheckedMoment :=
  CheckedMoment.ofBessel lo2912b1 lo2912b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2912b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨5,by decide⟩
def hi2912b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨6,by decide⟩
def hi2912 : CheckedMoment :=
  CheckedMoment.ofBessel hi2912b1 hi2912b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2912 : meanBracketCheck (6237/6250) lo2912 hi2912=true := by decide +kernel
def bracket2912 : MeanBracket := meanBracketOfMoments (6237/6250) lo2912 hi2912 accepted2912
def lo2913b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨10,by decide⟩
def lo2913b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨11,by decide⟩
def lo2913 : CheckedMoment :=
  CheckedMoment.ofBessel lo2913b1 lo2913b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2913b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨15,by decide⟩
def hi2913b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨16,by decide⟩
def hi2913 : CheckedMoment :=
  CheckedMoment.ofBessel hi2913b1 hi2913b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2913 : meanBracketCheck (39917/40000) lo2913 hi2913=true := by decide +kernel
def bracket2913 : MeanBracket := meanBracketOfMoments (39917/40000) lo2913 hi2913 accepted2913
def lo2914b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨20,by decide⟩
def lo2914b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨21,by decide⟩
def lo2914 : CheckedMoment :=
  CheckedMoment.ofBessel lo2914b1 lo2914b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2914b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨25,by decide⟩
def hi2914b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨26,by decide⟩
def hi2914 : CheckedMoment :=
  CheckedMoment.ofBessel hi2914b1 hi2914b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2914 : meanBracketCheck (99793/100000) lo2914 hi2914=true := by decide +kernel
def bracket2914 : MeanBracket := meanBracketOfMoments (99793/100000) lo2914 hi2914 accepted2914
def lo2915b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨30,by decide⟩
def lo2915b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨31,by decide⟩
def lo2915 : CheckedMoment :=
  CheckedMoment.ofBessel lo2915b1 lo2915b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2915b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨35,by decide⟩
def hi2915b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨36,by decide⟩
def hi2915 : CheckedMoment :=
  CheckedMoment.ofBessel hi2915b1 hi2915b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2915 : meanBracketCheck (199587/200000) lo2915 hi2915=true := by decide +kernel
def bracket2915 : MeanBracket := meanBracketOfMoments (199587/200000) lo2915 hi2915 accepted2915
def lo2916b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨40,by decide⟩
def lo2916b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨41,by decide⟩
def lo2916 : CheckedMoment :=
  CheckedMoment.ofBessel lo2916b1 lo2916b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2916b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨45,by decide⟩
def hi2916b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨46,by decide⟩
def hi2916 : CheckedMoment :=
  CheckedMoment.ofBessel hi2916b1 hi2916b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2916 : meanBracketCheck (49897/50000) lo2916 hi2916=true := by decide +kernel
def bracket2916 : MeanBracket := meanBracketOfMoments (49897/50000) lo2916 hi2916 accepted2916
def lo2917b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨50,by decide⟩
def lo2917b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨51,by decide⟩
def lo2917 : CheckedMoment :=
  CheckedMoment.ofBessel lo2917b1 lo2917b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2917b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨55,by decide⟩
def hi2917b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨56,by decide⟩
def hi2917 : CheckedMoment :=
  CheckedMoment.ofBessel hi2917b1 hi2917b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2917 : meanBracketCheck (199589/200000) lo2917 hi2917=true := by decide +kernel
def bracket2917 : MeanBracket := meanBracketOfMoments (199589/200000) lo2917 hi2917 accepted2917
def lo2918b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨60,by decide⟩
def lo2918b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨61,by decide⟩
def lo2918 : CheckedMoment :=
  CheckedMoment.ofBessel lo2918b1 lo2918b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2918b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨1,by decide⟩
def hi2918b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨2,by decide⟩
def hi2918 : CheckedMoment :=
  CheckedMoment.ofBessel hi2918b1 hi2918b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2918 : meanBracketCheck (19959/20000) lo2918 hi2918=true := by decide +kernel
def bracket2918 : MeanBracket := meanBracketOfMoments (19959/20000) lo2918 hi2918 accepted2918
def lo2919b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨6,by decide⟩
def lo2919b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨7,by decide⟩
def lo2919 : CheckedMoment :=
  CheckedMoment.ofBessel lo2919b1 lo2919b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2919b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨11,by decide⟩
def hi2919b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨12,by decide⟩
def hi2919 : CheckedMoment :=
  CheckedMoment.ofBessel hi2919b1 hi2919b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2919 : meanBracketCheck (199591/200000) lo2919 hi2919=true := by decide +kernel
def bracket2919 : MeanBracket := meanBracketOfMoments (199591/200000) lo2919 hi2919 accepted2919
def lo2920b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨16,by decide⟩
def lo2920b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨17,by decide⟩
def lo2920 : CheckedMoment :=
  CheckedMoment.ofBessel lo2920b1 lo2920b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2920b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨21,by decide⟩
def hi2920b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨22,by decide⟩
def hi2920 : CheckedMoment :=
  CheckedMoment.ofBessel hi2920b1 hi2920b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2920 : meanBracketCheck (24949/25000) lo2920 hi2920=true := by decide +kernel
def bracket2920 : MeanBracket := meanBracketOfMoments (24949/25000) lo2920 hi2920 accepted2920
def lo2921b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨26,by decide⟩
def lo2921b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨27,by decide⟩
def lo2921 : CheckedMoment :=
  CheckedMoment.ofBessel lo2921b1 lo2921b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2921b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨31,by decide⟩
def hi2921b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨32,by decide⟩
def hi2921 : CheckedMoment :=
  CheckedMoment.ofBessel hi2921b1 hi2921b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2921 : meanBracketCheck (199593/200000) lo2921 hi2921=true := by decide +kernel
def bracket2921 : MeanBracket := meanBracketOfMoments (199593/200000) lo2921 hi2921 accepted2921
def lo2922b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨36,by decide⟩
def lo2922b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨37,by decide⟩
def lo2922 : CheckedMoment :=
  CheckedMoment.ofBessel lo2922b1 lo2922b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2922b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨41,by decide⟩
def hi2922b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨42,by decide⟩
def hi2922 : CheckedMoment :=
  CheckedMoment.ofBessel hi2922b1 hi2922b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2922 : meanBracketCheck (99797/100000) lo2922 hi2922=true := by decide +kernel
def bracket2922 : MeanBracket := meanBracketOfMoments (99797/100000) lo2922 hi2922 accepted2922
def lo2923b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨46,by decide⟩
def lo2923b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨47,by decide⟩
def lo2923 : CheckedMoment :=
  CheckedMoment.ofBessel lo2923b1 lo2923b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2923b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨51,by decide⟩
def hi2923b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨52,by decide⟩
def hi2923 : CheckedMoment :=
  CheckedMoment.ofBessel hi2923b1 hi2923b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2923 : meanBracketCheck (39919/40000) lo2923 hi2923=true := by decide +kernel
def bracket2923 : MeanBracket := meanBracketOfMoments (39919/40000) lo2923 hi2923 accepted2923
def lo2924b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨56,by decide⟩
def lo2924b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨57,by decide⟩
def lo2924 : CheckedMoment :=
  CheckedMoment.ofBessel lo2924b1 lo2924b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2924b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨61,by decide⟩
def hi2924b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨62,by decide⟩
def hi2924 : CheckedMoment :=
  CheckedMoment.ofBessel hi2924b1 hi2924b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2924 : meanBracketCheck (49899/50000) lo2924 hi2924=true := by decide +kernel
def bracket2924 : MeanBracket := meanBracketOfMoments (49899/50000) lo2924 hi2924 accepted2924
def lo2925b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨2,by decide⟩
def lo2925b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨3,by decide⟩
def lo2925 : CheckedMoment :=
  CheckedMoment.ofBessel lo2925b1 lo2925b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2925b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨7,by decide⟩
def hi2925b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨8,by decide⟩
def hi2925 : CheckedMoment :=
  CheckedMoment.ofBessel hi2925b1 hi2925b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2925 : meanBracketCheck (199597/200000) lo2925 hi2925=true := by decide +kernel
def bracket2925 : MeanBracket := meanBracketOfMoments (199597/200000) lo2925 hi2925 accepted2925
def lo2926b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨12,by decide⟩
def lo2926b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨13,by decide⟩
def lo2926 : CheckedMoment :=
  CheckedMoment.ofBessel lo2926b1 lo2926b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2926b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨17,by decide⟩
def hi2926b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨18,by decide⟩
def hi2926 : CheckedMoment :=
  CheckedMoment.ofBessel hi2926b1 hi2926b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2926 : meanBracketCheck (99799/100000) lo2926 hi2926=true := by decide +kernel
def bracket2926 : MeanBracket := meanBracketOfMoments (99799/100000) lo2926 hi2926 accepted2926
def lo2927b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨22,by decide⟩
def lo2927b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨23,by decide⟩
def lo2927 : CheckedMoment :=
  CheckedMoment.ofBessel lo2927b1 lo2927b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2927b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨27,by decide⟩
def hi2927b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨28,by decide⟩
def hi2927 : CheckedMoment :=
  CheckedMoment.ofBessel hi2927b1 hi2927b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2927 : meanBracketCheck (199599/200000) lo2927 hi2927=true := by decide +kernel
def bracket2927 : MeanBracket := meanBracketOfMoments (199599/200000) lo2927 hi2927 accepted2927
#print axioms bracket2912
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0182
