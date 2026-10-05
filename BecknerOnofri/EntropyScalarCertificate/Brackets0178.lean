import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0445
import BecknerOnofri.EntropyScalarCertificate.Bessel0446
import BecknerOnofri.EntropyScalarCertificate.Bessel0447
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0178
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2848b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨0,by decide⟩
def lo2848b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨1,by decide⟩
def lo2848 : CheckedMoment :=
  CheckedMoment.ofBessel lo2848b1 lo2848b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2848b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨5,by decide⟩
def hi2848b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨6,by decide⟩
def hi2848 : CheckedMoment :=
  CheckedMoment.ofBessel hi2848b1 hi2848b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2848 : meanBracketCheck (1247/1250) lo2848 hi2848=true := by decide +kernel
def bracket2848 : MeanBracket := meanBracketOfMoments (1247/1250) lo2848 hi2848 accepted2848
def lo2849b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨10,by decide⟩
def lo2849b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨11,by decide⟩
def lo2849 : CheckedMoment :=
  CheckedMoment.ofBessel lo2849b1 lo2849b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2849b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨15,by decide⟩
def hi2849b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨16,by decide⟩
def hi2849 : CheckedMoment :=
  CheckedMoment.ofBessel hi2849b1 hi2849b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2849 : meanBracketCheck (199521/200000) lo2849 hi2849=true := by decide +kernel
def bracket2849 : MeanBracket := meanBracketOfMoments (199521/200000) lo2849 hi2849 accepted2849
def lo2850b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨20,by decide⟩
def lo2850b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨21,by decide⟩
def lo2850 : CheckedMoment :=
  CheckedMoment.ofBessel lo2850b1 lo2850b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2850b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨25,by decide⟩
def hi2850b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨26,by decide⟩
def hi2850 : CheckedMoment :=
  CheckedMoment.ofBessel hi2850b1 hi2850b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2850 : meanBracketCheck (99761/100000) lo2850 hi2850=true := by decide +kernel
def bracket2850 : MeanBracket := meanBracketOfMoments (99761/100000) lo2850 hi2850 accepted2850
def lo2851b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨30,by decide⟩
def lo2851b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨31,by decide⟩
def lo2851 : CheckedMoment :=
  CheckedMoment.ofBessel lo2851b1 lo2851b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2851b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨35,by decide⟩
def hi2851b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨36,by decide⟩
def hi2851 : CheckedMoment :=
  CheckedMoment.ofBessel hi2851b1 hi2851b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2851 : meanBracketCheck (199523/200000) lo2851 hi2851=true := by decide +kernel
def bracket2851 : MeanBracket := meanBracketOfMoments (199523/200000) lo2851 hi2851 accepted2851
def lo2852b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨40,by decide⟩
def lo2852b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨41,by decide⟩
def lo2852 : CheckedMoment :=
  CheckedMoment.ofBessel lo2852b1 lo2852b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2852b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨45,by decide⟩
def hi2852b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨46,by decide⟩
def hi2852 : CheckedMoment :=
  CheckedMoment.ofBessel hi2852b1 hi2852b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2852 : meanBracketCheck (49881/50000) lo2852 hi2852=true := by decide +kernel
def bracket2852 : MeanBracket := meanBracketOfMoments (49881/50000) lo2852 hi2852 accepted2852
def lo2853b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨50,by decide⟩
def lo2853b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨51,by decide⟩
def lo2853 : CheckedMoment :=
  CheckedMoment.ofBessel lo2853b1 lo2853b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2853b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨55,by decide⟩
def hi2853b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨56,by decide⟩
def hi2853 : CheckedMoment :=
  CheckedMoment.ofBessel hi2853b1 hi2853b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2853 : meanBracketCheck (7981/8000) lo2853 hi2853=true := by decide +kernel
def bracket2853 : MeanBracket := meanBracketOfMoments (7981/8000) lo2853 hi2853 accepted2853
def lo2854b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨60,by decide⟩
def lo2854b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0445.rows BesselBatch0445.accepted ⟨61,by decide⟩
def lo2854 : CheckedMoment :=
  CheckedMoment.ofBessel lo2854b1 lo2854b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2854b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨1,by decide⟩
def hi2854b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨2,by decide⟩
def hi2854 : CheckedMoment :=
  CheckedMoment.ofBessel hi2854b1 hi2854b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2854 : meanBracketCheck (99763/100000) lo2854 hi2854=true := by decide +kernel
def bracket2854 : MeanBracket := meanBracketOfMoments (99763/100000) lo2854 hi2854 accepted2854
def lo2855b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨6,by decide⟩
def lo2855b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨7,by decide⟩
def lo2855 : CheckedMoment :=
  CheckedMoment.ofBessel lo2855b1 lo2855b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2855b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨11,by decide⟩
def hi2855b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨12,by decide⟩
def hi2855 : CheckedMoment :=
  CheckedMoment.ofBessel hi2855b1 hi2855b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2855 : meanBracketCheck (199527/200000) lo2855 hi2855=true := by decide +kernel
def bracket2855 : MeanBracket := meanBracketOfMoments (199527/200000) lo2855 hi2855 accepted2855
def lo2856b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨16,by decide⟩
def lo2856b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨17,by decide⟩
def lo2856 : CheckedMoment :=
  CheckedMoment.ofBessel lo2856b1 lo2856b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2856b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨21,by decide⟩
def hi2856b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨22,by decide⟩
def hi2856 : CheckedMoment :=
  CheckedMoment.ofBessel hi2856b1 hi2856b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2856 : meanBracketCheck (24941/25000) lo2856 hi2856=true := by decide +kernel
def bracket2856 : MeanBracket := meanBracketOfMoments (24941/25000) lo2856 hi2856 accepted2856
def lo2857b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨26,by decide⟩
def lo2857b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨27,by decide⟩
def lo2857 : CheckedMoment :=
  CheckedMoment.ofBessel lo2857b1 lo2857b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2857b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨31,by decide⟩
def hi2857b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨32,by decide⟩
def hi2857 : CheckedMoment :=
  CheckedMoment.ofBessel hi2857b1 hi2857b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2857 : meanBracketCheck (199529/200000) lo2857 hi2857=true := by decide +kernel
def bracket2857 : MeanBracket := meanBracketOfMoments (199529/200000) lo2857 hi2857 accepted2857
def lo2858b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨36,by decide⟩
def lo2858b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨37,by decide⟩
def lo2858 : CheckedMoment :=
  CheckedMoment.ofBessel lo2858b1 lo2858b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2858b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨41,by decide⟩
def hi2858b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨42,by decide⟩
def hi2858 : CheckedMoment :=
  CheckedMoment.ofBessel hi2858b1 hi2858b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2858 : meanBracketCheck (19953/20000) lo2858 hi2858=true := by decide +kernel
def bracket2858 : MeanBracket := meanBracketOfMoments (19953/20000) lo2858 hi2858 accepted2858
def lo2859b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨46,by decide⟩
def lo2859b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨47,by decide⟩
def lo2859 : CheckedMoment :=
  CheckedMoment.ofBessel lo2859b1 lo2859b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2859b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨51,by decide⟩
def hi2859b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨52,by decide⟩
def hi2859 : CheckedMoment :=
  CheckedMoment.ofBessel hi2859b1 hi2859b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2859 : meanBracketCheck (199531/200000) lo2859 hi2859=true := by decide +kernel
def bracket2859 : MeanBracket := meanBracketOfMoments (199531/200000) lo2859 hi2859 accepted2859
def lo2860b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨56,by decide⟩
def lo2860b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨57,by decide⟩
def lo2860 : CheckedMoment :=
  CheckedMoment.ofBessel lo2860b1 lo2860b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2860b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨61,by decide⟩
def hi2860b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨62,by decide⟩
def hi2860 : CheckedMoment :=
  CheckedMoment.ofBessel hi2860b1 hi2860b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2860 : meanBracketCheck (49883/50000) lo2860 hi2860=true := by decide +kernel
def bracket2860 : MeanBracket := meanBracketOfMoments (49883/50000) lo2860 hi2860 accepted2860
def lo2861b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨2,by decide⟩
def lo2861b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨3,by decide⟩
def lo2861 : CheckedMoment :=
  CheckedMoment.ofBessel lo2861b1 lo2861b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2861b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨7,by decide⟩
def hi2861b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨8,by decide⟩
def hi2861 : CheckedMoment :=
  CheckedMoment.ofBessel hi2861b1 hi2861b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2861 : meanBracketCheck (199533/200000) lo2861 hi2861=true := by decide +kernel
def bracket2861 : MeanBracket := meanBracketOfMoments (199533/200000) lo2861 hi2861 accepted2861
def lo2862b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨12,by decide⟩
def lo2862b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨13,by decide⟩
def lo2862 : CheckedMoment :=
  CheckedMoment.ofBessel lo2862b1 lo2862b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2862b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨17,by decide⟩
def hi2862b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨18,by decide⟩
def hi2862 : CheckedMoment :=
  CheckedMoment.ofBessel hi2862b1 hi2862b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2862 : meanBracketCheck (99767/100000) lo2862 hi2862=true := by decide +kernel
def bracket2862 : MeanBracket := meanBracketOfMoments (99767/100000) lo2862 hi2862 accepted2862
def lo2863b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨22,by decide⟩
def lo2863b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨23,by decide⟩
def lo2863 : CheckedMoment :=
  CheckedMoment.ofBessel lo2863b1 lo2863b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2863b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨27,by decide⟩
def hi2863b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨28,by decide⟩
def hi2863 : CheckedMoment :=
  CheckedMoment.ofBessel hi2863b1 hi2863b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2863 : meanBracketCheck (39907/40000) lo2863 hi2863=true := by decide +kernel
def bracket2863 : MeanBracket := meanBracketOfMoments (39907/40000) lo2863 hi2863 accepted2863
#print axioms bracket2848
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0178
