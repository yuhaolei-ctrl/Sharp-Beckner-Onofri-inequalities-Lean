import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0420
import BecknerOnofri.EntropyScalarCertificate.Bessel0421
import BecknerOnofri.EntropyScalarCertificate.Bessel0422
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0168
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2688b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨0,by decide⟩
def lo2688b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨1,by decide⟩
def lo2688 : CheckedMoment :=
  CheckedMoment.ofBessel lo2688b1 lo2688b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2688b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨5,by decide⟩
def hi2688b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨6,by decide⟩
def hi2688 : CheckedMoment :=
  CheckedMoment.ofBessel hi2688b1 hi2688b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2688 : meanBracketCheck (4981/5000) lo2688 hi2688=true := by decide +kernel
def bracket2688 : MeanBracket := meanBracketOfMoments (4981/5000) lo2688 hi2688 accepted2688
def lo2689b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨10,by decide⟩
def lo2689b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨11,by decide⟩
def lo2689 : CheckedMoment :=
  CheckedMoment.ofBessel lo2689b1 lo2689b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2689b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨15,by decide⟩
def hi2689b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨16,by decide⟩
def hi2689 : CheckedMoment :=
  CheckedMoment.ofBessel hi2689b1 hi2689b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2689 : meanBracketCheck (49811/50000) lo2689 hi2689=true := by decide +kernel
def bracket2689 : MeanBracket := meanBracketOfMoments (49811/50000) lo2689 hi2689 accepted2689
def lo2690b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨20,by decide⟩
def lo2690b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨21,by decide⟩
def lo2690 : CheckedMoment :=
  CheckedMoment.ofBessel lo2690b1 lo2690b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2690b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨25,by decide⟩
def hi2690b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨26,by decide⟩
def hi2690 : CheckedMoment :=
  CheckedMoment.ofBessel hi2690b1 hi2690b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2690 : meanBracketCheck (12453/12500) lo2690 hi2690=true := by decide +kernel
def bracket2690 : MeanBracket := meanBracketOfMoments (12453/12500) lo2690 hi2690 accepted2690
def lo2691b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨30,by decide⟩
def lo2691b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨31,by decide⟩
def lo2691 : CheckedMoment :=
  CheckedMoment.ofBessel lo2691b1 lo2691b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2691b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨35,by decide⟩
def hi2691b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨36,by decide⟩
def hi2691 : CheckedMoment :=
  CheckedMoment.ofBessel hi2691b1 hi2691b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2691 : meanBracketCheck (49813/50000) lo2691 hi2691=true := by decide +kernel
def bracket2691 : MeanBracket := meanBracketOfMoments (49813/50000) lo2691 hi2691 accepted2691
def lo2692b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨40,by decide⟩
def lo2692b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨41,by decide⟩
def lo2692 : CheckedMoment :=
  CheckedMoment.ofBessel lo2692b1 lo2692b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2692b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨45,by decide⟩
def hi2692b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨46,by decide⟩
def hi2692 : CheckedMoment :=
  CheckedMoment.ofBessel hi2692b1 hi2692b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2692 : meanBracketCheck (24907/25000) lo2692 hi2692=true := by decide +kernel
def bracket2692 : MeanBracket := meanBracketOfMoments (24907/25000) lo2692 hi2692 accepted2692
def lo2693b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨50,by decide⟩
def lo2693b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨51,by decide⟩
def lo2693 : CheckedMoment :=
  CheckedMoment.ofBessel lo2693b1 lo2693b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2693b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨55,by decide⟩
def hi2693b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨56,by decide⟩
def hi2693 : CheckedMoment :=
  CheckedMoment.ofBessel hi2693b1 hi2693b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2693 : meanBracketCheck (9963/10000) lo2693 hi2693=true := by decide +kernel
def bracket2693 : MeanBracket := meanBracketOfMoments (9963/10000) lo2693 hi2693 accepted2693
def lo2694b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨60,by decide⟩
def lo2694b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨61,by decide⟩
def lo2694 : CheckedMoment :=
  CheckedMoment.ofBessel lo2694b1 lo2694b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2694b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨1,by decide⟩
def hi2694b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨2,by decide⟩
def hi2694 : CheckedMoment :=
  CheckedMoment.ofBessel hi2694b1 hi2694b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2694 : meanBracketCheck (6227/6250) lo2694 hi2694=true := by decide +kernel
def bracket2694 : MeanBracket := meanBracketOfMoments (6227/6250) lo2694 hi2694 accepted2694
def lo2695b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨6,by decide⟩
def lo2695b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨7,by decide⟩
def lo2695 : CheckedMoment :=
  CheckedMoment.ofBessel lo2695b1 lo2695b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2695b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨11,by decide⟩
def hi2695b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨12,by decide⟩
def hi2695 : CheckedMoment :=
  CheckedMoment.ofBessel hi2695b1 hi2695b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2695 : meanBracketCheck (49817/50000) lo2695 hi2695=true := by decide +kernel
def bracket2695 : MeanBracket := meanBracketOfMoments (49817/50000) lo2695 hi2695 accepted2695
def lo2696b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨16,by decide⟩
def lo2696b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨17,by decide⟩
def lo2696 : CheckedMoment :=
  CheckedMoment.ofBessel lo2696b1 lo2696b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2696b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨21,by decide⟩
def hi2696b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨22,by decide⟩
def hi2696 : CheckedMoment :=
  CheckedMoment.ofBessel hi2696b1 hi2696b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2696 : meanBracketCheck (24909/25000) lo2696 hi2696=true := by decide +kernel
def bracket2696 : MeanBracket := meanBracketOfMoments (24909/25000) lo2696 hi2696 accepted2696
def lo2697b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨26,by decide⟩
def lo2697b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨27,by decide⟩
def lo2697 : CheckedMoment :=
  CheckedMoment.ofBessel lo2697b1 lo2697b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2697b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨31,by decide⟩
def hi2697b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨32,by decide⟩
def hi2697 : CheckedMoment :=
  CheckedMoment.ofBessel hi2697b1 hi2697b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2697 : meanBracketCheck (49819/50000) lo2697 hi2697=true := by decide +kernel
def bracket2697 : MeanBracket := meanBracketOfMoments (49819/50000) lo2697 hi2697 accepted2697
def lo2698b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨36,by decide⟩
def lo2698b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨37,by decide⟩
def lo2698 : CheckedMoment :=
  CheckedMoment.ofBessel lo2698b1 lo2698b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2698b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨41,by decide⟩
def hi2698b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨42,by decide⟩
def hi2698 : CheckedMoment :=
  CheckedMoment.ofBessel hi2698b1 hi2698b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2698 : meanBracketCheck (2491/2500) lo2698 hi2698=true := by decide +kernel
def bracket2698 : MeanBracket := meanBracketOfMoments (2491/2500) lo2698 hi2698 accepted2698
def lo2699b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨46,by decide⟩
def lo2699b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨47,by decide⟩
def lo2699 : CheckedMoment :=
  CheckedMoment.ofBessel lo2699b1 lo2699b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2699b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨51,by decide⟩
def hi2699b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨52,by decide⟩
def hi2699 : CheckedMoment :=
  CheckedMoment.ofBessel hi2699b1 hi2699b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2699 : meanBracketCheck (49821/50000) lo2699 hi2699=true := by decide +kernel
def bracket2699 : MeanBracket := meanBracketOfMoments (49821/50000) lo2699 hi2699 accepted2699
def lo2700b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨56,by decide⟩
def lo2700b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨57,by decide⟩
def lo2700 : CheckedMoment :=
  CheckedMoment.ofBessel lo2700b1 lo2700b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2700b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨61,by decide⟩
def hi2700b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨62,by decide⟩
def hi2700 : CheckedMoment :=
  CheckedMoment.ofBessel hi2700b1 hi2700b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2700 : meanBracketCheck (24911/25000) lo2700 hi2700=true := by decide +kernel
def bracket2700 : MeanBracket := meanBracketOfMoments (24911/25000) lo2700 hi2700 accepted2700
def lo2701b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨2,by decide⟩
def lo2701b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨3,by decide⟩
def lo2701 : CheckedMoment :=
  CheckedMoment.ofBessel lo2701b1 lo2701b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2701b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨7,by decide⟩
def hi2701b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨8,by decide⟩
def hi2701 : CheckedMoment :=
  CheckedMoment.ofBessel hi2701b1 hi2701b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2701 : meanBracketCheck (49823/50000) lo2701 hi2701=true := by decide +kernel
def bracket2701 : MeanBracket := meanBracketOfMoments (49823/50000) lo2701 hi2701 accepted2701
def lo2702b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨12,by decide⟩
def lo2702b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨13,by decide⟩
def lo2702 : CheckedMoment :=
  CheckedMoment.ofBessel lo2702b1 lo2702b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2702b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨17,by decide⟩
def hi2702b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨18,by decide⟩
def hi2702 : CheckedMoment :=
  CheckedMoment.ofBessel hi2702b1 hi2702b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2702 : meanBracketCheck (3114/3125) lo2702 hi2702=true := by decide +kernel
def bracket2702 : MeanBracket := meanBracketOfMoments (3114/3125) lo2702 hi2702 accepted2702
def lo2703b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨22,by decide⟩
def lo2703b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨23,by decide⟩
def lo2703 : CheckedMoment :=
  CheckedMoment.ofBessel lo2703b1 lo2703b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2703b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨27,by decide⟩
def hi2703b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨28,by decide⟩
def hi2703 : CheckedMoment :=
  CheckedMoment.ofBessel hi2703b1 hi2703b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2703 : meanBracketCheck (1993/2000) lo2703 hi2703=true := by decide +kernel
def bracket2703 : MeanBracket := meanBracketOfMoments (1993/2000) lo2703 hi2703 accepted2703
#print axioms bracket2688
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0168
