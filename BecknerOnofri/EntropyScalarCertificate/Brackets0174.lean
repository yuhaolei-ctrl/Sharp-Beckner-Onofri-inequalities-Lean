import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0435
import BecknerOnofri.EntropyScalarCertificate.Bessel0436
import BecknerOnofri.EntropyScalarCertificate.Bessel0437
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0174
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2784b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨0,by decide⟩
def lo2784b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨1,by decide⟩
def lo2784 : CheckedMoment :=
  CheckedMoment.ofBessel lo2784b1 lo2784b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2784b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨5,by decide⟩
def hi2784b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨6,by decide⟩
def hi2784 : CheckedMoment :=
  CheckedMoment.ofBessel hi2784b1 hi2784b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2784 : meanBracketCheck (6233/6250) lo2784 hi2784=true := by decide +kernel
def bracket2784 : MeanBracket := meanBracketOfMoments (6233/6250) lo2784 hi2784 accepted2784
def lo2785b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨10,by decide⟩
def lo2785b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨11,by decide⟩
def lo2785 : CheckedMoment :=
  CheckedMoment.ofBessel lo2785b1 lo2785b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2785b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨15,by decide⟩
def hi2785b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨16,by decide⟩
def hi2785 : CheckedMoment :=
  CheckedMoment.ofBessel hi2785b1 hi2785b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2785 : meanBracketCheck (199457/200000) lo2785 hi2785=true := by decide +kernel
def bracket2785 : MeanBracket := meanBracketOfMoments (199457/200000) lo2785 hi2785 accepted2785
def lo2786b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨20,by decide⟩
def lo2786b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨21,by decide⟩
def lo2786 : CheckedMoment :=
  CheckedMoment.ofBessel lo2786b1 lo2786b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2786b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨25,by decide⟩
def hi2786b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨26,by decide⟩
def hi2786 : CheckedMoment :=
  CheckedMoment.ofBessel hi2786b1 hi2786b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2786 : meanBracketCheck (99729/100000) lo2786 hi2786=true := by decide +kernel
def bracket2786 : MeanBracket := meanBracketOfMoments (99729/100000) lo2786 hi2786 accepted2786
def lo2787b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨30,by decide⟩
def lo2787b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨31,by decide⟩
def lo2787 : CheckedMoment :=
  CheckedMoment.ofBessel lo2787b1 lo2787b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2787b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨35,by decide⟩
def hi2787b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨36,by decide⟩
def hi2787 : CheckedMoment :=
  CheckedMoment.ofBessel hi2787b1 hi2787b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2787 : meanBracketCheck (199459/200000) lo2787 hi2787=true := by decide +kernel
def bracket2787 : MeanBracket := meanBracketOfMoments (199459/200000) lo2787 hi2787 accepted2787
def lo2788b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨40,by decide⟩
def lo2788b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨41,by decide⟩
def lo2788 : CheckedMoment :=
  CheckedMoment.ofBessel lo2788b1 lo2788b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2788b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨45,by decide⟩
def hi2788b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨46,by decide⟩
def hi2788 : CheckedMoment :=
  CheckedMoment.ofBessel hi2788b1 hi2788b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2788 : meanBracketCheck (9973/10000) lo2788 hi2788=true := by decide +kernel
def bracket2788 : MeanBracket := meanBracketOfMoments (9973/10000) lo2788 hi2788 accepted2788
def lo2789b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨50,by decide⟩
def lo2789b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨51,by decide⟩
def lo2789 : CheckedMoment :=
  CheckedMoment.ofBessel lo2789b1 lo2789b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2789b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨55,by decide⟩
def hi2789b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨56,by decide⟩
def hi2789 : CheckedMoment :=
  CheckedMoment.ofBessel hi2789b1 hi2789b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2789 : meanBracketCheck (199461/200000) lo2789 hi2789=true := by decide +kernel
def bracket2789 : MeanBracket := meanBracketOfMoments (199461/200000) lo2789 hi2789 accepted2789
def lo2790b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨60,by decide⟩
def lo2790b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨61,by decide⟩
def lo2790 : CheckedMoment :=
  CheckedMoment.ofBessel lo2790b1 lo2790b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2790b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨1,by decide⟩
def hi2790b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨2,by decide⟩
def hi2790 : CheckedMoment :=
  CheckedMoment.ofBessel hi2790b1 hi2790b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2790 : meanBracketCheck (99731/100000) lo2790 hi2790=true := by decide +kernel
def bracket2790 : MeanBracket := meanBracketOfMoments (99731/100000) lo2790 hi2790 accepted2790
def lo2791b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨6,by decide⟩
def lo2791b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨7,by decide⟩
def lo2791 : CheckedMoment :=
  CheckedMoment.ofBessel lo2791b1 lo2791b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2791b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨11,by decide⟩
def hi2791b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨12,by decide⟩
def hi2791 : CheckedMoment :=
  CheckedMoment.ofBessel hi2791b1 hi2791b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2791 : meanBracketCheck (199463/200000) lo2791 hi2791=true := by decide +kernel
def bracket2791 : MeanBracket := meanBracketOfMoments (199463/200000) lo2791 hi2791 accepted2791
def lo2792b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨16,by decide⟩
def lo2792b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨17,by decide⟩
def lo2792 : CheckedMoment :=
  CheckedMoment.ofBessel lo2792b1 lo2792b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2792b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨21,by decide⟩
def hi2792b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨22,by decide⟩
def hi2792 : CheckedMoment :=
  CheckedMoment.ofBessel hi2792b1 hi2792b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2792 : meanBracketCheck (24933/25000) lo2792 hi2792=true := by decide +kernel
def bracket2792 : MeanBracket := meanBracketOfMoments (24933/25000) lo2792 hi2792 accepted2792
def lo2793b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨26,by decide⟩
def lo2793b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨27,by decide⟩
def lo2793 : CheckedMoment :=
  CheckedMoment.ofBessel lo2793b1 lo2793b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2793b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨31,by decide⟩
def hi2793b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨32,by decide⟩
def hi2793 : CheckedMoment :=
  CheckedMoment.ofBessel hi2793b1 hi2793b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2793 : meanBracketCheck (39893/40000) lo2793 hi2793=true := by decide +kernel
def bracket2793 : MeanBracket := meanBracketOfMoments (39893/40000) lo2793 hi2793 accepted2793
def lo2794b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨36,by decide⟩
def lo2794b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨37,by decide⟩
def lo2794 : CheckedMoment :=
  CheckedMoment.ofBessel lo2794b1 lo2794b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2794b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨41,by decide⟩
def hi2794b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨42,by decide⟩
def hi2794 : CheckedMoment :=
  CheckedMoment.ofBessel hi2794b1 hi2794b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2794 : meanBracketCheck (99733/100000) lo2794 hi2794=true := by decide +kernel
def bracket2794 : MeanBracket := meanBracketOfMoments (99733/100000) lo2794 hi2794 accepted2794
def lo2795b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨46,by decide⟩
def lo2795b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨47,by decide⟩
def lo2795 : CheckedMoment :=
  CheckedMoment.ofBessel lo2795b1 lo2795b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2795b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨51,by decide⟩
def hi2795b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨52,by decide⟩
def hi2795 : CheckedMoment :=
  CheckedMoment.ofBessel hi2795b1 hi2795b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2795 : meanBracketCheck (199467/200000) lo2795 hi2795=true := by decide +kernel
def bracket2795 : MeanBracket := meanBracketOfMoments (199467/200000) lo2795 hi2795 accepted2795
def lo2796b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨56,by decide⟩
def lo2796b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨57,by decide⟩
def lo2796 : CheckedMoment :=
  CheckedMoment.ofBessel lo2796b1 lo2796b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2796b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨61,by decide⟩
def hi2796b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨62,by decide⟩
def hi2796 : CheckedMoment :=
  CheckedMoment.ofBessel hi2796b1 hi2796b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2796 : meanBracketCheck (49867/50000) lo2796 hi2796=true := by decide +kernel
def bracket2796 : MeanBracket := meanBracketOfMoments (49867/50000) lo2796 hi2796 accepted2796
def lo2797b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨2,by decide⟩
def lo2797b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨3,by decide⟩
def lo2797 : CheckedMoment :=
  CheckedMoment.ofBessel lo2797b1 lo2797b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2797b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨7,by decide⟩
def hi2797b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨8,by decide⟩
def hi2797 : CheckedMoment :=
  CheckedMoment.ofBessel hi2797b1 hi2797b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2797 : meanBracketCheck (199469/200000) lo2797 hi2797=true := by decide +kernel
def bracket2797 : MeanBracket := meanBracketOfMoments (199469/200000) lo2797 hi2797 accepted2797
def lo2798b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨12,by decide⟩
def lo2798b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨13,by decide⟩
def lo2798 : CheckedMoment :=
  CheckedMoment.ofBessel lo2798b1 lo2798b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2798b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨17,by decide⟩
def hi2798b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨18,by decide⟩
def hi2798 : CheckedMoment :=
  CheckedMoment.ofBessel hi2798b1 hi2798b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2798 : meanBracketCheck (19947/20000) lo2798 hi2798=true := by decide +kernel
def bracket2798 : MeanBracket := meanBracketOfMoments (19947/20000) lo2798 hi2798 accepted2798
def lo2799b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨22,by decide⟩
def lo2799b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨23,by decide⟩
def lo2799 : CheckedMoment :=
  CheckedMoment.ofBessel lo2799b1 lo2799b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2799b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨27,by decide⟩
def hi2799b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨28,by decide⟩
def hi2799 : CheckedMoment :=
  CheckedMoment.ofBessel hi2799b1 hi2799b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2799 : meanBracketCheck (199471/200000) lo2799 hi2799=true := by decide +kernel
def bracket2799 : MeanBracket := meanBracketOfMoments (199471/200000) lo2799 hi2799 accepted2799
#print axioms bracket2784
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0174
