import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0450
import BecknerOnofri.EntropyScalarCertificate.Bessel0451
import BecknerOnofri.EntropyScalarCertificate.Bessel0452
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0180
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2880b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨0,by decide⟩
def lo2880b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨1,by decide⟩
def lo2880 : CheckedMoment :=
  CheckedMoment.ofBessel lo2880b1 lo2880b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2880b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨5,by decide⟩
def hi2880b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨6,by decide⟩
def hi2880 : CheckedMoment :=
  CheckedMoment.ofBessel hi2880b1 hi2880b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2880 : meanBracketCheck (3118/3125) lo2880 hi2880=true := by decide +kernel
def bracket2880 : MeanBracket := meanBracketOfMoments (3118/3125) lo2880 hi2880 accepted2880
def lo2881b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨10,by decide⟩
def lo2881b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨11,by decide⟩
def lo2881 : CheckedMoment :=
  CheckedMoment.ofBessel lo2881b1 lo2881b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2881b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨15,by decide⟩
def hi2881b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨16,by decide⟩
def hi2881 : CheckedMoment :=
  CheckedMoment.ofBessel hi2881b1 hi2881b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2881 : meanBracketCheck (199553/200000) lo2881 hi2881=true := by decide +kernel
def bracket2881 : MeanBracket := meanBracketOfMoments (199553/200000) lo2881 hi2881 accepted2881
def lo2882b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨20,by decide⟩
def lo2882b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨21,by decide⟩
def lo2882 : CheckedMoment :=
  CheckedMoment.ofBessel lo2882b1 lo2882b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2882b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨25,by decide⟩
def hi2882b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨26,by decide⟩
def hi2882 : CheckedMoment :=
  CheckedMoment.ofBessel hi2882b1 hi2882b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2882 : meanBracketCheck (99777/100000) lo2882 hi2882=true := by decide +kernel
def bracket2882 : MeanBracket := meanBracketOfMoments (99777/100000) lo2882 hi2882 accepted2882
def lo2883b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨30,by decide⟩
def lo2883b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨31,by decide⟩
def lo2883 : CheckedMoment :=
  CheckedMoment.ofBessel lo2883b1 lo2883b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2883b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨35,by decide⟩
def hi2883b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨36,by decide⟩
def hi2883 : CheckedMoment :=
  CheckedMoment.ofBessel hi2883b1 hi2883b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2883 : meanBracketCheck (39911/40000) lo2883 hi2883=true := by decide +kernel
def bracket2883 : MeanBracket := meanBracketOfMoments (39911/40000) lo2883 hi2883 accepted2883
def lo2884b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨40,by decide⟩
def lo2884b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨41,by decide⟩
def lo2884 : CheckedMoment :=
  CheckedMoment.ofBessel lo2884b1 lo2884b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2884b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨45,by decide⟩
def hi2884b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨46,by decide⟩
def hi2884 : CheckedMoment :=
  CheckedMoment.ofBessel hi2884b1 hi2884b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2884 : meanBracketCheck (49889/50000) lo2884 hi2884=true := by decide +kernel
def bracket2884 : MeanBracket := meanBracketOfMoments (49889/50000) lo2884 hi2884 accepted2884
def lo2885b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨50,by decide⟩
def lo2885b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨51,by decide⟩
def lo2885 : CheckedMoment :=
  CheckedMoment.ofBessel lo2885b1 lo2885b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2885b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨55,by decide⟩
def hi2885b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨56,by decide⟩
def hi2885 : CheckedMoment :=
  CheckedMoment.ofBessel hi2885b1 hi2885b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2885 : meanBracketCheck (199557/200000) lo2885 hi2885=true := by decide +kernel
def bracket2885 : MeanBracket := meanBracketOfMoments (199557/200000) lo2885 hi2885 accepted2885
def lo2886b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨60,by decide⟩
def lo2886b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨61,by decide⟩
def lo2886 : CheckedMoment :=
  CheckedMoment.ofBessel lo2886b1 lo2886b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2886b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨1,by decide⟩
def hi2886b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨2,by decide⟩
def hi2886 : CheckedMoment :=
  CheckedMoment.ofBessel hi2886b1 hi2886b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2886 : meanBracketCheck (99779/100000) lo2886 hi2886=true := by decide +kernel
def bracket2886 : MeanBracket := meanBracketOfMoments (99779/100000) lo2886 hi2886 accepted2886
def lo2887b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨6,by decide⟩
def lo2887b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨7,by decide⟩
def lo2887 : CheckedMoment :=
  CheckedMoment.ofBessel lo2887b1 lo2887b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2887b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨11,by decide⟩
def hi2887b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨12,by decide⟩
def hi2887 : CheckedMoment :=
  CheckedMoment.ofBessel hi2887b1 hi2887b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2887 : meanBracketCheck (199559/200000) lo2887 hi2887=true := by decide +kernel
def bracket2887 : MeanBracket := meanBracketOfMoments (199559/200000) lo2887 hi2887 accepted2887
def lo2888b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨16,by decide⟩
def lo2888b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨17,by decide⟩
def lo2888 : CheckedMoment :=
  CheckedMoment.ofBessel lo2888b1 lo2888b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2888b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨21,by decide⟩
def hi2888b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨22,by decide⟩
def hi2888 : CheckedMoment :=
  CheckedMoment.ofBessel hi2888b1 hi2888b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2888 : meanBracketCheck (4989/5000) lo2888 hi2888=true := by decide +kernel
def bracket2888 : MeanBracket := meanBracketOfMoments (4989/5000) lo2888 hi2888 accepted2888
def lo2889b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨26,by decide⟩
def lo2889b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨27,by decide⟩
def lo2889 : CheckedMoment :=
  CheckedMoment.ofBessel lo2889b1 lo2889b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2889b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨31,by decide⟩
def hi2889b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨32,by decide⟩
def hi2889 : CheckedMoment :=
  CheckedMoment.ofBessel hi2889b1 hi2889b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2889 : meanBracketCheck (199561/200000) lo2889 hi2889=true := by decide +kernel
def bracket2889 : MeanBracket := meanBracketOfMoments (199561/200000) lo2889 hi2889 accepted2889
def lo2890b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨36,by decide⟩
def lo2890b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨37,by decide⟩
def lo2890 : CheckedMoment :=
  CheckedMoment.ofBessel lo2890b1 lo2890b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2890b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨41,by decide⟩
def hi2890b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨42,by decide⟩
def hi2890 : CheckedMoment :=
  CheckedMoment.ofBessel hi2890b1 hi2890b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2890 : meanBracketCheck (99781/100000) lo2890 hi2890=true := by decide +kernel
def bracket2890 : MeanBracket := meanBracketOfMoments (99781/100000) lo2890 hi2890 accepted2890
def lo2891b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨46,by decide⟩
def lo2891b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨47,by decide⟩
def lo2891 : CheckedMoment :=
  CheckedMoment.ofBessel lo2891b1 lo2891b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2891b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨51,by decide⟩
def hi2891b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨52,by decide⟩
def hi2891 : CheckedMoment :=
  CheckedMoment.ofBessel hi2891b1 hi2891b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2891 : meanBracketCheck (199563/200000) lo2891 hi2891=true := by decide +kernel
def bracket2891 : MeanBracket := meanBracketOfMoments (199563/200000) lo2891 hi2891 accepted2891
def lo2892b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨56,by decide⟩
def lo2892b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨57,by decide⟩
def lo2892 : CheckedMoment :=
  CheckedMoment.ofBessel lo2892b1 lo2892b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2892b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨61,by decide⟩
def hi2892b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0451.rows BesselBatch0451.accepted ⟨62,by decide⟩
def hi2892 : CheckedMoment :=
  CheckedMoment.ofBessel hi2892b1 hi2892b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2892 : meanBracketCheck (49891/50000) lo2892 hi2892=true := by decide +kernel
def bracket2892 : MeanBracket := meanBracketOfMoments (49891/50000) lo2892 hi2892 accepted2892
def lo2893b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨2,by decide⟩
def lo2893b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨3,by decide⟩
def lo2893 : CheckedMoment :=
  CheckedMoment.ofBessel lo2893b1 lo2893b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2893b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨7,by decide⟩
def hi2893b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨8,by decide⟩
def hi2893 : CheckedMoment :=
  CheckedMoment.ofBessel hi2893b1 hi2893b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2893 : meanBracketCheck (39913/40000) lo2893 hi2893=true := by decide +kernel
def bracket2893 : MeanBracket := meanBracketOfMoments (39913/40000) lo2893 hi2893 accepted2893
def lo2894b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨12,by decide⟩
def lo2894b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨13,by decide⟩
def lo2894 : CheckedMoment :=
  CheckedMoment.ofBessel lo2894b1 lo2894b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2894b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨17,by decide⟩
def hi2894b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨18,by decide⟩
def hi2894 : CheckedMoment :=
  CheckedMoment.ofBessel hi2894b1 hi2894b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2894 : meanBracketCheck (99783/100000) lo2894 hi2894=true := by decide +kernel
def bracket2894 : MeanBracket := meanBracketOfMoments (99783/100000) lo2894 hi2894 accepted2894
def lo2895b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨22,by decide⟩
def lo2895b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨23,by decide⟩
def lo2895 : CheckedMoment :=
  CheckedMoment.ofBessel lo2895b1 lo2895b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2895b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨27,by decide⟩
def hi2895b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0452.rows BesselBatch0452.accepted ⟨28,by decide⟩
def hi2895 : CheckedMoment :=
  CheckedMoment.ofBessel hi2895b1 hi2895b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2895 : meanBracketCheck (199567/200000) lo2895 hi2895=true := by decide +kernel
def bracket2895 : MeanBracket := meanBracketOfMoments (199567/200000) lo2895 hi2895 accepted2895
#print axioms bracket2880
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0180
