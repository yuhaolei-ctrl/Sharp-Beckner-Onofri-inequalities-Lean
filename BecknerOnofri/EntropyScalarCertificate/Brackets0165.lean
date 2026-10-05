import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0412
import BecknerOnofri.EntropyScalarCertificate.Bessel0413
import BecknerOnofri.EntropyScalarCertificate.Bessel0414
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0165
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2640b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨32,by decide⟩
def lo2640b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨33,by decide⟩
def lo2640 : CheckedMoment :=
  CheckedMoment.ofBessel lo2640b1 lo2640b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2640b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨37,by decide⟩
def hi2640b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨38,by decide⟩
def hi2640 : CheckedMoment :=
  CheckedMoment.ofBessel hi2640b1 hi2640b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2640 : meanBracketCheck (24881/25000) lo2640 hi2640=true := by decide +kernel
def bracket2640 : MeanBracket := meanBracketOfMoments (24881/25000) lo2640 hi2640 accepted2640
def lo2641b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨42,by decide⟩
def lo2641b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨43,by decide⟩
def lo2641 : CheckedMoment :=
  CheckedMoment.ofBessel lo2641b1 lo2641b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2641b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨47,by decide⟩
def hi2641b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨48,by decide⟩
def hi2641 : CheckedMoment :=
  CheckedMoment.ofBessel hi2641b1 hi2641b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2641 : meanBracketCheck (49763/50000) lo2641 hi2641=true := by decide +kernel
def bracket2641 : MeanBracket := meanBracketOfMoments (49763/50000) lo2641 hi2641 accepted2641
def lo2642b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨52,by decide⟩
def lo2642b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨53,by decide⟩
def lo2642 : CheckedMoment :=
  CheckedMoment.ofBessel lo2642b1 lo2642b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2642b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨57,by decide⟩
def hi2642b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨58,by decide⟩
def hi2642 : CheckedMoment :=
  CheckedMoment.ofBessel hi2642b1 hi2642b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2642 : meanBracketCheck (12441/12500) lo2642 hi2642=true := by decide +kernel
def bracket2642 : MeanBracket := meanBracketOfMoments (12441/12500) lo2642 hi2642 accepted2642
def lo2643b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨62,by decide⟩
def lo2643b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨63,by decide⟩
def lo2643 : CheckedMoment :=
  CheckedMoment.ofBessel lo2643b1 lo2643b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2643b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨3,by decide⟩
def hi2643b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨4,by decide⟩
def hi2643 : CheckedMoment :=
  CheckedMoment.ofBessel hi2643b1 hi2643b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2643 : meanBracketCheck (9953/10000) lo2643 hi2643=true := by decide +kernel
def bracket2643 : MeanBracket := meanBracketOfMoments (9953/10000) lo2643 hi2643 accepted2643
def lo2644b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨8,by decide⟩
def lo2644b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨9,by decide⟩
def lo2644 : CheckedMoment :=
  CheckedMoment.ofBessel lo2644b1 lo2644b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2644b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨13,by decide⟩
def hi2644b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨14,by decide⟩
def hi2644 : CheckedMoment :=
  CheckedMoment.ofBessel hi2644b1 hi2644b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2644 : meanBracketCheck (24883/25000) lo2644 hi2644=true := by decide +kernel
def bracket2644 : MeanBracket := meanBracketOfMoments (24883/25000) lo2644 hi2644 accepted2644
def lo2645b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨18,by decide⟩
def lo2645b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨19,by decide⟩
def lo2645 : CheckedMoment :=
  CheckedMoment.ofBessel lo2645b1 lo2645b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2645b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨23,by decide⟩
def hi2645b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨24,by decide⟩
def hi2645 : CheckedMoment :=
  CheckedMoment.ofBessel hi2645b1 hi2645b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2645 : meanBracketCheck (49767/50000) lo2645 hi2645=true := by decide +kernel
def bracket2645 : MeanBracket := meanBracketOfMoments (49767/50000) lo2645 hi2645 accepted2645
def lo2646b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨28,by decide⟩
def lo2646b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨29,by decide⟩
def lo2646 : CheckedMoment :=
  CheckedMoment.ofBessel lo2646b1 lo2646b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2646b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨33,by decide⟩
def hi2646b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨34,by decide⟩
def hi2646 : CheckedMoment :=
  CheckedMoment.ofBessel hi2646b1 hi2646b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2646 : meanBracketCheck (6221/6250) lo2646 hi2646=true := by decide +kernel
def bracket2646 : MeanBracket := meanBracketOfMoments (6221/6250) lo2646 hi2646 accepted2646
def lo2647b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨38,by decide⟩
def lo2647b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨39,by decide⟩
def lo2647 : CheckedMoment :=
  CheckedMoment.ofBessel lo2647b1 lo2647b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2647b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨43,by decide⟩
def hi2647b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨44,by decide⟩
def hi2647 : CheckedMoment :=
  CheckedMoment.ofBessel hi2647b1 hi2647b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2647 : meanBracketCheck (49769/50000) lo2647 hi2647=true := by decide +kernel
def bracket2647 : MeanBracket := meanBracketOfMoments (49769/50000) lo2647 hi2647 accepted2647
def lo2648b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨48,by decide⟩
def lo2648b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨49,by decide⟩
def lo2648 : CheckedMoment :=
  CheckedMoment.ofBessel lo2648b1 lo2648b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2648b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨53,by decide⟩
def hi2648b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨54,by decide⟩
def hi2648 : CheckedMoment :=
  CheckedMoment.ofBessel hi2648b1 hi2648b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2648 : meanBracketCheck (4977/5000) lo2648 hi2648=true := by decide +kernel
def bracket2648 : MeanBracket := meanBracketOfMoments (4977/5000) lo2648 hi2648 accepted2648
def lo2649b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨58,by decide⟩
def lo2649b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨59,by decide⟩
def lo2649 : CheckedMoment :=
  CheckedMoment.ofBessel lo2649b1 lo2649b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2649b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨63,by decide⟩
def hi2649b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨0,by decide⟩
def hi2649 : CheckedMoment :=
  CheckedMoment.ofBessel hi2649b1 hi2649b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2649 : meanBracketCheck (49771/50000) lo2649 hi2649=true := by decide +kernel
def bracket2649 : MeanBracket := meanBracketOfMoments (49771/50000) lo2649 hi2649 accepted2649
def lo2650b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨4,by decide⟩
def lo2650b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨5,by decide⟩
def lo2650 : CheckedMoment :=
  CheckedMoment.ofBessel lo2650b1 lo2650b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2650b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨9,by decide⟩
def hi2650b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨10,by decide⟩
def hi2650 : CheckedMoment :=
  CheckedMoment.ofBessel hi2650b1 hi2650b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2650 : meanBracketCheck (12443/12500) lo2650 hi2650=true := by decide +kernel
def bracket2650 : MeanBracket := meanBracketOfMoments (12443/12500) lo2650 hi2650 accepted2650
def lo2651b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨14,by decide⟩
def lo2651b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨15,by decide⟩
def lo2651 : CheckedMoment :=
  CheckedMoment.ofBessel lo2651b1 lo2651b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2651b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨19,by decide⟩
def hi2651b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨20,by decide⟩
def hi2651 : CheckedMoment :=
  CheckedMoment.ofBessel hi2651b1 hi2651b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2651 : meanBracketCheck (49773/50000) lo2651 hi2651=true := by decide +kernel
def bracket2651 : MeanBracket := meanBracketOfMoments (49773/50000) lo2651 hi2651 accepted2651
def lo2652b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨24,by decide⟩
def lo2652b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨25,by decide⟩
def lo2652 : CheckedMoment :=
  CheckedMoment.ofBessel lo2652b1 lo2652b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2652b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨29,by decide⟩
def hi2652b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨30,by decide⟩
def hi2652 : CheckedMoment :=
  CheckedMoment.ofBessel hi2652b1 hi2652b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2652 : meanBracketCheck (24887/25000) lo2652 hi2652=true := by decide +kernel
def bracket2652 : MeanBracket := meanBracketOfMoments (24887/25000) lo2652 hi2652 accepted2652
def lo2653b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨34,by decide⟩
def lo2653b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨35,by decide⟩
def lo2653 : CheckedMoment :=
  CheckedMoment.ofBessel lo2653b1 lo2653b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2653b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨39,by decide⟩
def hi2653b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨40,by decide⟩
def hi2653 : CheckedMoment :=
  CheckedMoment.ofBessel hi2653b1 hi2653b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2653 : meanBracketCheck (1991/2000) lo2653 hi2653=true := by decide +kernel
def bracket2653 : MeanBracket := meanBracketOfMoments (1991/2000) lo2653 hi2653 accepted2653
def lo2654b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨44,by decide⟩
def lo2654b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨45,by decide⟩
def lo2654 : CheckedMoment :=
  CheckedMoment.ofBessel lo2654b1 lo2654b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2654b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨49,by decide⟩
def hi2654b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨50,by decide⟩
def hi2654 : CheckedMoment :=
  CheckedMoment.ofBessel hi2654b1 hi2654b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2654 : meanBracketCheck (3111/3125) lo2654 hi2654=true := by decide +kernel
def bracket2654 : MeanBracket := meanBracketOfMoments (3111/3125) lo2654 hi2654 accepted2654
def lo2655b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨54,by decide⟩
def lo2655b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨55,by decide⟩
def lo2655 : CheckedMoment :=
  CheckedMoment.ofBessel lo2655b1 lo2655b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2655b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨59,by decide⟩
def hi2655b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨60,by decide⟩
def hi2655 : CheckedMoment :=
  CheckedMoment.ofBessel hi2655b1 hi2655b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2655 : meanBracketCheck (49777/50000) lo2655 hi2655=true := by decide +kernel
def bracket2655 : MeanBracket := meanBracketOfMoments (49777/50000) lo2655 hi2655 accepted2655
#print axioms bracket2640
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0165
