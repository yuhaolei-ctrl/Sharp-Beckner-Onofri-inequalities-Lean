import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0447
import BecknerOnofri.EntropyScalarCertificate.Bessel0448
import BecknerOnofri.EntropyScalarCertificate.Bessel0449
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0179
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2864b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨32,by decide⟩
def lo2864b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨33,by decide⟩
def lo2864 : CheckedMoment :=
  CheckedMoment.ofBessel lo2864b1 lo2864b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2864b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨37,by decide⟩
def hi2864b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨38,by decide⟩
def hi2864 : CheckedMoment :=
  CheckedMoment.ofBessel hi2864b1 hi2864b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2864 : meanBracketCheck (12471/12500) lo2864 hi2864=true := by decide +kernel
def bracket2864 : MeanBracket := meanBracketOfMoments (12471/12500) lo2864 hi2864 accepted2864
def lo2865b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨42,by decide⟩
def lo2865b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨43,by decide⟩
def lo2865 : CheckedMoment :=
  CheckedMoment.ofBessel lo2865b1 lo2865b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2865b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨47,by decide⟩
def hi2865b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨48,by decide⟩
def hi2865 : CheckedMoment :=
  CheckedMoment.ofBessel hi2865b1 hi2865b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2865 : meanBracketCheck (199537/200000) lo2865 hi2865=true := by decide +kernel
def bracket2865 : MeanBracket := meanBracketOfMoments (199537/200000) lo2865 hi2865 accepted2865
def lo2866b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨52,by decide⟩
def lo2866b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨53,by decide⟩
def lo2866 : CheckedMoment :=
  CheckedMoment.ofBessel lo2866b1 lo2866b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2866b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨57,by decide⟩
def hi2866b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨58,by decide⟩
def hi2866 : CheckedMoment :=
  CheckedMoment.ofBessel hi2866b1 hi2866b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2866 : meanBracketCheck (99769/100000) lo2866 hi2866=true := by decide +kernel
def bracket2866 : MeanBracket := meanBracketOfMoments (99769/100000) lo2866 hi2866 accepted2866
def lo2867b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨62,by decide⟩
def lo2867b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨63,by decide⟩
def lo2867 : CheckedMoment :=
  CheckedMoment.ofBessel lo2867b1 lo2867b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2867b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨3,by decide⟩
def hi2867b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨4,by decide⟩
def hi2867 : CheckedMoment :=
  CheckedMoment.ofBessel hi2867b1 hi2867b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2867 : meanBracketCheck (199539/200000) lo2867 hi2867=true := by decide +kernel
def bracket2867 : MeanBracket := meanBracketOfMoments (199539/200000) lo2867 hi2867 accepted2867
def lo2868b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨8,by decide⟩
def lo2868b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨9,by decide⟩
def lo2868 : CheckedMoment :=
  CheckedMoment.ofBessel lo2868b1 lo2868b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2868b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨13,by decide⟩
def hi2868b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨14,by decide⟩
def hi2868 : CheckedMoment :=
  CheckedMoment.ofBessel hi2868b1 hi2868b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2868 : meanBracketCheck (9977/10000) lo2868 hi2868=true := by decide +kernel
def bracket2868 : MeanBracket := meanBracketOfMoments (9977/10000) lo2868 hi2868 accepted2868
def lo2869b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨18,by decide⟩
def lo2869b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨19,by decide⟩
def lo2869 : CheckedMoment :=
  CheckedMoment.ofBessel lo2869b1 lo2869b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2869b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨23,by decide⟩
def hi2869b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨24,by decide⟩
def hi2869 : CheckedMoment :=
  CheckedMoment.ofBessel hi2869b1 hi2869b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2869 : meanBracketCheck (199541/200000) lo2869 hi2869=true := by decide +kernel
def bracket2869 : MeanBracket := meanBracketOfMoments (199541/200000) lo2869 hi2869 accepted2869
def lo2870b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨28,by decide⟩
def lo2870b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨29,by decide⟩
def lo2870 : CheckedMoment :=
  CheckedMoment.ofBessel lo2870b1 lo2870b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2870b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨33,by decide⟩
def hi2870b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨34,by decide⟩
def hi2870 : CheckedMoment :=
  CheckedMoment.ofBessel hi2870b1 hi2870b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2870 : meanBracketCheck (99771/100000) lo2870 hi2870=true := by decide +kernel
def bracket2870 : MeanBracket := meanBracketOfMoments (99771/100000) lo2870 hi2870 accepted2870
def lo2871b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨38,by decide⟩
def lo2871b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨39,by decide⟩
def lo2871 : CheckedMoment :=
  CheckedMoment.ofBessel lo2871b1 lo2871b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2871b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨43,by decide⟩
def hi2871b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨44,by decide⟩
def hi2871 : CheckedMoment :=
  CheckedMoment.ofBessel hi2871b1 hi2871b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2871 : meanBracketCheck (199543/200000) lo2871 hi2871=true := by decide +kernel
def bracket2871 : MeanBracket := meanBracketOfMoments (199543/200000) lo2871 hi2871 accepted2871
def lo2872b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨48,by decide⟩
def lo2872b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨49,by decide⟩
def lo2872 : CheckedMoment :=
  CheckedMoment.ofBessel lo2872b1 lo2872b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2872b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨53,by decide⟩
def hi2872b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨54,by decide⟩
def hi2872 : CheckedMoment :=
  CheckedMoment.ofBessel hi2872b1 hi2872b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2872 : meanBracketCheck (24943/25000) lo2872 hi2872=true := by decide +kernel
def bracket2872 : MeanBracket := meanBracketOfMoments (24943/25000) lo2872 hi2872 accepted2872
def lo2873b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨58,by decide⟩
def lo2873b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨59,by decide⟩
def lo2873 : CheckedMoment :=
  CheckedMoment.ofBessel lo2873b1 lo2873b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2873b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨63,by decide⟩
def hi2873b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨0,by decide⟩
def hi2873 : CheckedMoment :=
  CheckedMoment.ofBessel hi2873b1 hi2873b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2873 : meanBracketCheck (39909/40000) lo2873 hi2873=true := by decide +kernel
def bracket2873 : MeanBracket := meanBracketOfMoments (39909/40000) lo2873 hi2873 accepted2873
def lo2874b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨4,by decide⟩
def lo2874b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨5,by decide⟩
def lo2874 : CheckedMoment :=
  CheckedMoment.ofBessel lo2874b1 lo2874b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2874b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨9,by decide⟩
def hi2874b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨10,by decide⟩
def hi2874 : CheckedMoment :=
  CheckedMoment.ofBessel hi2874b1 hi2874b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2874 : meanBracketCheck (99773/100000) lo2874 hi2874=true := by decide +kernel
def bracket2874 : MeanBracket := meanBracketOfMoments (99773/100000) lo2874 hi2874 accepted2874
def lo2875b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨14,by decide⟩
def lo2875b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨15,by decide⟩
def lo2875 : CheckedMoment :=
  CheckedMoment.ofBessel lo2875b1 lo2875b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2875b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨19,by decide⟩
def hi2875b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨20,by decide⟩
def hi2875 : CheckedMoment :=
  CheckedMoment.ofBessel hi2875b1 hi2875b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2875 : meanBracketCheck (199547/200000) lo2875 hi2875=true := by decide +kernel
def bracket2875 : MeanBracket := meanBracketOfMoments (199547/200000) lo2875 hi2875 accepted2875
def lo2876b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨24,by decide⟩
def lo2876b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨25,by decide⟩
def lo2876 : CheckedMoment :=
  CheckedMoment.ofBessel lo2876b1 lo2876b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2876b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨29,by decide⟩
def hi2876b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨30,by decide⟩
def hi2876 : CheckedMoment :=
  CheckedMoment.ofBessel hi2876b1 hi2876b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2876 : meanBracketCheck (49887/50000) lo2876 hi2876=true := by decide +kernel
def bracket2876 : MeanBracket := meanBracketOfMoments (49887/50000) lo2876 hi2876 accepted2876
def lo2877b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨34,by decide⟩
def lo2877b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨35,by decide⟩
def lo2877 : CheckedMoment :=
  CheckedMoment.ofBessel lo2877b1 lo2877b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2877b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨39,by decide⟩
def hi2877b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨40,by decide⟩
def hi2877 : CheckedMoment :=
  CheckedMoment.ofBessel hi2877b1 hi2877b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2877 : meanBracketCheck (199549/200000) lo2877 hi2877=true := by decide +kernel
def bracket2877 : MeanBracket := meanBracketOfMoments (199549/200000) lo2877 hi2877 accepted2877
def lo2878b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨44,by decide⟩
def lo2878b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨45,by decide⟩
def lo2878 : CheckedMoment :=
  CheckedMoment.ofBessel lo2878b1 lo2878b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2878b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨49,by decide⟩
def hi2878b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨50,by decide⟩
def hi2878 : CheckedMoment :=
  CheckedMoment.ofBessel hi2878b1 hi2878b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2878 : meanBracketCheck (3991/4000) lo2878 hi2878=true := by decide +kernel
def bracket2878 : MeanBracket := meanBracketOfMoments (3991/4000) lo2878 hi2878 accepted2878
def lo2879b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨54,by decide⟩
def lo2879b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨55,by decide⟩
def lo2879 : CheckedMoment :=
  CheckedMoment.ofBessel lo2879b1 lo2879b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2879b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨59,by decide⟩
def hi2879b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨60,by decide⟩
def hi2879 : CheckedMoment :=
  CheckedMoment.ofBessel hi2879b1 hi2879b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2879 : meanBracketCheck (199551/200000) lo2879 hi2879=true := by decide +kernel
def bracket2879 : MeanBracket := meanBracketOfMoments (199551/200000) lo2879 hi2879 accepted2879
#print axioms bracket2864
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0179
