import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0440
import BecknerOnofri.EntropyScalarCertificate.Bessel0441
import BecknerOnofri.EntropyScalarCertificate.Bessel0442
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0176
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2816b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨0,by decide⟩
def lo2816b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨1,by decide⟩
def lo2816 : CheckedMoment :=
  CheckedMoment.ofBessel lo2816b1 lo2816b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2816b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨5,by decide⟩
def hi2816b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨6,by decide⟩
def hi2816 : CheckedMoment :=
  CheckedMoment.ofBessel hi2816b1 hi2816b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2816 : meanBracketCheck (3117/3125) lo2816 hi2816=true := by decide +kernel
def bracket2816 : MeanBracket := meanBracketOfMoments (3117/3125) lo2816 hi2816 accepted2816
def lo2817b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨10,by decide⟩
def lo2817b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨11,by decide⟩
def lo2817 : CheckedMoment :=
  CheckedMoment.ofBessel lo2817b1 lo2817b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2817b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨15,by decide⟩
def hi2817b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨16,by decide⟩
def hi2817 : CheckedMoment :=
  CheckedMoment.ofBessel hi2817b1 hi2817b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2817 : meanBracketCheck (199489/200000) lo2817 hi2817=true := by decide +kernel
def bracket2817 : MeanBracket := meanBracketOfMoments (199489/200000) lo2817 hi2817 accepted2817
def lo2818b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨20,by decide⟩
def lo2818b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨21,by decide⟩
def lo2818 : CheckedMoment :=
  CheckedMoment.ofBessel lo2818b1 lo2818b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2818b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨25,by decide⟩
def hi2818b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨26,by decide⟩
def hi2818 : CheckedMoment :=
  CheckedMoment.ofBessel hi2818b1 hi2818b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2818 : meanBracketCheck (19949/20000) lo2818 hi2818=true := by decide +kernel
def bracket2818 : MeanBracket := meanBracketOfMoments (19949/20000) lo2818 hi2818 accepted2818
def lo2819b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨30,by decide⟩
def lo2819b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨31,by decide⟩
def lo2819 : CheckedMoment :=
  CheckedMoment.ofBessel lo2819b1 lo2819b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2819b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨35,by decide⟩
def hi2819b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨36,by decide⟩
def hi2819 : CheckedMoment :=
  CheckedMoment.ofBessel hi2819b1 hi2819b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2819 : meanBracketCheck (199491/200000) lo2819 hi2819=true := by decide +kernel
def bracket2819 : MeanBracket := meanBracketOfMoments (199491/200000) lo2819 hi2819 accepted2819
def lo2820b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨40,by decide⟩
def lo2820b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨41,by decide⟩
def lo2820 : CheckedMoment :=
  CheckedMoment.ofBessel lo2820b1 lo2820b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2820b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨45,by decide⟩
def hi2820b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨46,by decide⟩
def hi2820 : CheckedMoment :=
  CheckedMoment.ofBessel hi2820b1 hi2820b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2820 : meanBracketCheck (49873/50000) lo2820 hi2820=true := by decide +kernel
def bracket2820 : MeanBracket := meanBracketOfMoments (49873/50000) lo2820 hi2820 accepted2820
def lo2821b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨50,by decide⟩
def lo2821b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨51,by decide⟩
def lo2821 : CheckedMoment :=
  CheckedMoment.ofBessel lo2821b1 lo2821b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2821b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨55,by decide⟩
def hi2821b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨56,by decide⟩
def hi2821 : CheckedMoment :=
  CheckedMoment.ofBessel hi2821b1 hi2821b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2821 : meanBracketCheck (199493/200000) lo2821 hi2821=true := by decide +kernel
def bracket2821 : MeanBracket := meanBracketOfMoments (199493/200000) lo2821 hi2821 accepted2821
def lo2822b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨60,by decide⟩
def lo2822b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨61,by decide⟩
def lo2822 : CheckedMoment :=
  CheckedMoment.ofBessel lo2822b1 lo2822b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2822b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨1,by decide⟩
def hi2822b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨2,by decide⟩
def hi2822 : CheckedMoment :=
  CheckedMoment.ofBessel hi2822b1 hi2822b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2822 : meanBracketCheck (99747/100000) lo2822 hi2822=true := by decide +kernel
def bracket2822 : MeanBracket := meanBracketOfMoments (99747/100000) lo2822 hi2822 accepted2822
def lo2823b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨6,by decide⟩
def lo2823b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨7,by decide⟩
def lo2823 : CheckedMoment :=
  CheckedMoment.ofBessel lo2823b1 lo2823b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2823b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨11,by decide⟩
def hi2823b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨12,by decide⟩
def hi2823 : CheckedMoment :=
  CheckedMoment.ofBessel hi2823b1 hi2823b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2823 : meanBracketCheck (39899/40000) lo2823 hi2823=true := by decide +kernel
def bracket2823 : MeanBracket := meanBracketOfMoments (39899/40000) lo2823 hi2823 accepted2823
def lo2824b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨16,by decide⟩
def lo2824b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨17,by decide⟩
def lo2824 : CheckedMoment :=
  CheckedMoment.ofBessel lo2824b1 lo2824b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2824b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨21,by decide⟩
def hi2824b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨22,by decide⟩
def hi2824 : CheckedMoment :=
  CheckedMoment.ofBessel hi2824b1 hi2824b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2824 : meanBracketCheck (24937/25000) lo2824 hi2824=true := by decide +kernel
def bracket2824 : MeanBracket := meanBracketOfMoments (24937/25000) lo2824 hi2824 accepted2824
def lo2825b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨26,by decide⟩
def lo2825b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨27,by decide⟩
def lo2825 : CheckedMoment :=
  CheckedMoment.ofBessel lo2825b1 lo2825b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2825b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨31,by decide⟩
def hi2825b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨32,by decide⟩
def hi2825 : CheckedMoment :=
  CheckedMoment.ofBessel hi2825b1 hi2825b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2825 : meanBracketCheck (199497/200000) lo2825 hi2825=true := by decide +kernel
def bracket2825 : MeanBracket := meanBracketOfMoments (199497/200000) lo2825 hi2825 accepted2825
def lo2826b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨36,by decide⟩
def lo2826b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨37,by decide⟩
def lo2826 : CheckedMoment :=
  CheckedMoment.ofBessel lo2826b1 lo2826b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2826b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨41,by decide⟩
def hi2826b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨42,by decide⟩
def hi2826 : CheckedMoment :=
  CheckedMoment.ofBessel hi2826b1 hi2826b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2826 : meanBracketCheck (99749/100000) lo2826 hi2826=true := by decide +kernel
def bracket2826 : MeanBracket := meanBracketOfMoments (99749/100000) lo2826 hi2826 accepted2826
def lo2827b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨46,by decide⟩
def lo2827b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨47,by decide⟩
def lo2827 : CheckedMoment :=
  CheckedMoment.ofBessel lo2827b1 lo2827b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2827b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨51,by decide⟩
def hi2827b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨52,by decide⟩
def hi2827 : CheckedMoment :=
  CheckedMoment.ofBessel hi2827b1 hi2827b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2827 : meanBracketCheck (199499/200000) lo2827 hi2827=true := by decide +kernel
def bracket2827 : MeanBracket := meanBracketOfMoments (199499/200000) lo2827 hi2827 accepted2827
def lo2828b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨56,by decide⟩
def lo2828b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨57,by decide⟩
def lo2828 : CheckedMoment :=
  CheckedMoment.ofBessel lo2828b1 lo2828b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2828b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨61,by decide⟩
def hi2828b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨62,by decide⟩
def hi2828 : CheckedMoment :=
  CheckedMoment.ofBessel hi2828b1 hi2828b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2828 : meanBracketCheck (399/400) lo2828 hi2828=true := by decide +kernel
def bracket2828 : MeanBracket := meanBracketOfMoments (399/400) lo2828 hi2828 accepted2828
def lo2829b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨2,by decide⟩
def lo2829b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨3,by decide⟩
def lo2829 : CheckedMoment :=
  CheckedMoment.ofBessel lo2829b1 lo2829b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2829b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨7,by decide⟩
def hi2829b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨8,by decide⟩
def hi2829 : CheckedMoment :=
  CheckedMoment.ofBessel hi2829b1 hi2829b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2829 : meanBracketCheck (199501/200000) lo2829 hi2829=true := by decide +kernel
def bracket2829 : MeanBracket := meanBracketOfMoments (199501/200000) lo2829 hi2829 accepted2829
def lo2830b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨12,by decide⟩
def lo2830b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨13,by decide⟩
def lo2830 : CheckedMoment :=
  CheckedMoment.ofBessel lo2830b1 lo2830b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2830b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨17,by decide⟩
def hi2830b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨18,by decide⟩
def hi2830 : CheckedMoment :=
  CheckedMoment.ofBessel hi2830b1 hi2830b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2830 : meanBracketCheck (99751/100000) lo2830 hi2830=true := by decide +kernel
def bracket2830 : MeanBracket := meanBracketOfMoments (99751/100000) lo2830 hi2830 accepted2830
def lo2831b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨22,by decide⟩
def lo2831b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨23,by decide⟩
def lo2831 : CheckedMoment :=
  CheckedMoment.ofBessel lo2831b1 lo2831b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2831b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨27,by decide⟩
def hi2831b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨28,by decide⟩
def hi2831 : CheckedMoment :=
  CheckedMoment.ofBessel hi2831b1 hi2831b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2831 : meanBracketCheck (199503/200000) lo2831 hi2831=true := by decide +kernel
def bracket2831 : MeanBracket := meanBracketOfMoments (199503/200000) lo2831 hi2831 accepted2831
#print axioms bracket2816
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0176
