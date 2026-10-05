import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0442
import BecknerOnofri.EntropyScalarCertificate.Bessel0443
import BecknerOnofri.EntropyScalarCertificate.Bessel0444
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0177
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2832b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨32,by decide⟩
def lo2832b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨33,by decide⟩
def lo2832 : CheckedMoment :=
  CheckedMoment.ofBessel lo2832b1 lo2832b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2832b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨37,by decide⟩
def hi2832b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨38,by decide⟩
def hi2832 : CheckedMoment :=
  CheckedMoment.ofBessel hi2832b1 hi2832b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2832 : meanBracketCheck (12469/12500) lo2832 hi2832=true := by decide +kernel
def bracket2832 : MeanBracket := meanBracketOfMoments (12469/12500) lo2832 hi2832 accepted2832
def lo2833b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨42,by decide⟩
def lo2833b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨43,by decide⟩
def lo2833 : CheckedMoment :=
  CheckedMoment.ofBessel lo2833b1 lo2833b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2833b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨47,by decide⟩
def hi2833b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨48,by decide⟩
def hi2833 : CheckedMoment :=
  CheckedMoment.ofBessel hi2833b1 hi2833b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2833 : meanBracketCheck (39901/40000) lo2833 hi2833=true := by decide +kernel
def bracket2833 : MeanBracket := meanBracketOfMoments (39901/40000) lo2833 hi2833 accepted2833
def lo2834b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨52,by decide⟩
def lo2834b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨53,by decide⟩
def lo2834 : CheckedMoment :=
  CheckedMoment.ofBessel lo2834b1 lo2834b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2834b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨57,by decide⟩
def hi2834b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨58,by decide⟩
def hi2834 : CheckedMoment :=
  CheckedMoment.ofBessel hi2834b1 hi2834b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2834 : meanBracketCheck (99753/100000) lo2834 hi2834=true := by decide +kernel
def bracket2834 : MeanBracket := meanBracketOfMoments (99753/100000) lo2834 hi2834 accepted2834
def lo2835b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨62,by decide⟩
def lo2835b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨63,by decide⟩
def lo2835 : CheckedMoment :=
  CheckedMoment.ofBessel lo2835b1 lo2835b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2835b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨3,by decide⟩
def hi2835b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨4,by decide⟩
def hi2835 : CheckedMoment :=
  CheckedMoment.ofBessel hi2835b1 hi2835b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2835 : meanBracketCheck (199507/200000) lo2835 hi2835=true := by decide +kernel
def bracket2835 : MeanBracket := meanBracketOfMoments (199507/200000) lo2835 hi2835 accepted2835
def lo2836b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨8,by decide⟩
def lo2836b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨9,by decide⟩
def lo2836 : CheckedMoment :=
  CheckedMoment.ofBessel lo2836b1 lo2836b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2836b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨13,by decide⟩
def hi2836b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨14,by decide⟩
def hi2836 : CheckedMoment :=
  CheckedMoment.ofBessel hi2836b1 hi2836b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2836 : meanBracketCheck (49877/50000) lo2836 hi2836=true := by decide +kernel
def bracket2836 : MeanBracket := meanBracketOfMoments (49877/50000) lo2836 hi2836 accepted2836
def lo2837b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨18,by decide⟩
def lo2837b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨19,by decide⟩
def lo2837 : CheckedMoment :=
  CheckedMoment.ofBessel lo2837b1 lo2837b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2837b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨23,by decide⟩
def hi2837b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨24,by decide⟩
def hi2837 : CheckedMoment :=
  CheckedMoment.ofBessel hi2837b1 hi2837b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2837 : meanBracketCheck (199509/200000) lo2837 hi2837=true := by decide +kernel
def bracket2837 : MeanBracket := meanBracketOfMoments (199509/200000) lo2837 hi2837 accepted2837
def lo2838b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨28,by decide⟩
def lo2838b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨29,by decide⟩
def lo2838 : CheckedMoment :=
  CheckedMoment.ofBessel lo2838b1 lo2838b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2838b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨33,by decide⟩
def hi2838b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨34,by decide⟩
def hi2838 : CheckedMoment :=
  CheckedMoment.ofBessel hi2838b1 hi2838b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2838 : meanBracketCheck (19951/20000) lo2838 hi2838=true := by decide +kernel
def bracket2838 : MeanBracket := meanBracketOfMoments (19951/20000) lo2838 hi2838 accepted2838
def lo2839b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨38,by decide⟩
def lo2839b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨39,by decide⟩
def lo2839 : CheckedMoment :=
  CheckedMoment.ofBessel lo2839b1 lo2839b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2839b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨43,by decide⟩
def hi2839b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨44,by decide⟩
def hi2839 : CheckedMoment :=
  CheckedMoment.ofBessel hi2839b1 hi2839b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2839 : meanBracketCheck (199511/200000) lo2839 hi2839=true := by decide +kernel
def bracket2839 : MeanBracket := meanBracketOfMoments (199511/200000) lo2839 hi2839 accepted2839
def lo2840b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨48,by decide⟩
def lo2840b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨49,by decide⟩
def lo2840 : CheckedMoment :=
  CheckedMoment.ofBessel lo2840b1 lo2840b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2840b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨53,by decide⟩
def hi2840b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨54,by decide⟩
def hi2840 : CheckedMoment :=
  CheckedMoment.ofBessel hi2840b1 hi2840b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2840 : meanBracketCheck (24939/25000) lo2840 hi2840=true := by decide +kernel
def bracket2840 : MeanBracket := meanBracketOfMoments (24939/25000) lo2840 hi2840 accepted2840
def lo2841b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨58,by decide⟩
def lo2841b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨59,by decide⟩
def lo2841 : CheckedMoment :=
  CheckedMoment.ofBessel lo2841b1 lo2841b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2841b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨63,by decide⟩
def hi2841b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨0,by decide⟩
def hi2841 : CheckedMoment :=
  CheckedMoment.ofBessel hi2841b1 hi2841b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2841 : meanBracketCheck (199513/200000) lo2841 hi2841=true := by decide +kernel
def bracket2841 : MeanBracket := meanBracketOfMoments (199513/200000) lo2841 hi2841 accepted2841
def lo2842b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨4,by decide⟩
def lo2842b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨5,by decide⟩
def lo2842 : CheckedMoment :=
  CheckedMoment.ofBessel lo2842b1 lo2842b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2842b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨9,by decide⟩
def hi2842b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨10,by decide⟩
def hi2842 : CheckedMoment :=
  CheckedMoment.ofBessel hi2842b1 hi2842b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2842 : meanBracketCheck (99757/100000) lo2842 hi2842=true := by decide +kernel
def bracket2842 : MeanBracket := meanBracketOfMoments (99757/100000) lo2842 hi2842 accepted2842
def lo2843b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨14,by decide⟩
def lo2843b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨15,by decide⟩
def lo2843 : CheckedMoment :=
  CheckedMoment.ofBessel lo2843b1 lo2843b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2843b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨19,by decide⟩
def hi2843b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨20,by decide⟩
def hi2843 : CheckedMoment :=
  CheckedMoment.ofBessel hi2843b1 hi2843b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2843 : meanBracketCheck (39903/40000) lo2843 hi2843=true := by decide +kernel
def bracket2843 : MeanBracket := meanBracketOfMoments (39903/40000) lo2843 hi2843 accepted2843
def lo2844b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨24,by decide⟩
def lo2844b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨25,by decide⟩
def lo2844 : CheckedMoment :=
  CheckedMoment.ofBessel lo2844b1 lo2844b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2844b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨29,by decide⟩
def hi2844b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨30,by decide⟩
def hi2844 : CheckedMoment :=
  CheckedMoment.ofBessel hi2844b1 hi2844b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2844 : meanBracketCheck (49879/50000) lo2844 hi2844=true := by decide +kernel
def bracket2844 : MeanBracket := meanBracketOfMoments (49879/50000) lo2844 hi2844 accepted2844
def lo2845b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨34,by decide⟩
def lo2845b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨35,by decide⟩
def lo2845 : CheckedMoment :=
  CheckedMoment.ofBessel lo2845b1 lo2845b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2845b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨39,by decide⟩
def hi2845b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨40,by decide⟩
def hi2845 : CheckedMoment :=
  CheckedMoment.ofBessel hi2845b1 hi2845b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2845 : meanBracketCheck (199517/200000) lo2845 hi2845=true := by decide +kernel
def bracket2845 : MeanBracket := meanBracketOfMoments (199517/200000) lo2845 hi2845 accepted2845
def lo2846b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨44,by decide⟩
def lo2846b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨45,by decide⟩
def lo2846 : CheckedMoment :=
  CheckedMoment.ofBessel lo2846b1 lo2846b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2846b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨49,by decide⟩
def hi2846b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨50,by decide⟩
def hi2846 : CheckedMoment :=
  CheckedMoment.ofBessel hi2846b1 hi2846b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2846 : meanBracketCheck (99759/100000) lo2846 hi2846=true := by decide +kernel
def bracket2846 : MeanBracket := meanBracketOfMoments (99759/100000) lo2846 hi2846 accepted2846
def lo2847b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨54,by decide⟩
def lo2847b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨55,by decide⟩
def lo2847 : CheckedMoment :=
  CheckedMoment.ofBessel lo2847b1 lo2847b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2847b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨59,by decide⟩
def hi2847b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0444.rows BesselBatch0444.accepted ⟨60,by decide⟩
def hi2847 : CheckedMoment :=
  CheckedMoment.ofBessel hi2847b1 hi2847b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2847 : meanBracketCheck (199519/200000) lo2847 hi2847=true := by decide +kernel
def bracket2847 : MeanBracket := meanBracketOfMoments (199519/200000) lo2847 hi2847 accepted2847
#print axioms bracket2832
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0177
