import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0400
import BecknerOnofri.EntropyScalarCertificate.Bessel0401
import BecknerOnofri.EntropyScalarCertificate.Bessel0402
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0160
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2560b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨0,by decide⟩
def lo2560b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨1,by decide⟩
def lo2560 : CheckedMoment :=
  CheckedMoment.ofBessel lo2560b1 lo2560b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2560b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨5,by decide⟩
def hi2560b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨6,by decide⟩
def hi2560 : CheckedMoment :=
  CheckedMoment.ofBessel hi2560b1 hi2560b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2560 : meanBracketCheck (24841/25000) lo2560 hi2560=true := by decide +kernel
def bracket2560 : MeanBracket := meanBracketOfMoments (24841/25000) lo2560 hi2560 accepted2560
def lo2561b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨10,by decide⟩
def lo2561b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨11,by decide⟩
def lo2561 : CheckedMoment :=
  CheckedMoment.ofBessel lo2561b1 lo2561b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2561b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨15,by decide⟩
def hi2561b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨16,by decide⟩
def hi2561 : CheckedMoment :=
  CheckedMoment.ofBessel hi2561b1 hi2561b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2561 : meanBracketCheck (49683/50000) lo2561 hi2561=true := by decide +kernel
def bracket2561 : MeanBracket := meanBracketOfMoments (49683/50000) lo2561 hi2561 accepted2561
def lo2562b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨20,by decide⟩
def lo2562b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨21,by decide⟩
def lo2562 : CheckedMoment :=
  CheckedMoment.ofBessel lo2562b1 lo2562b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2562b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨25,by decide⟩
def hi2562b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨26,by decide⟩
def hi2562 : CheckedMoment :=
  CheckedMoment.ofBessel hi2562b1 hi2562b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2562 : meanBracketCheck (12421/12500) lo2562 hi2562=true := by decide +kernel
def bracket2562 : MeanBracket := meanBracketOfMoments (12421/12500) lo2562 hi2562 accepted2562
def lo2563b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨30,by decide⟩
def lo2563b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨31,by decide⟩
def lo2563 : CheckedMoment :=
  CheckedMoment.ofBessel lo2563b1 lo2563b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2563b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨35,by decide⟩
def hi2563b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨36,by decide⟩
def hi2563 : CheckedMoment :=
  CheckedMoment.ofBessel hi2563b1 hi2563b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2563 : meanBracketCheck (9937/10000) lo2563 hi2563=true := by decide +kernel
def bracket2563 : MeanBracket := meanBracketOfMoments (9937/10000) lo2563 hi2563 accepted2563
def lo2564b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨40,by decide⟩
def lo2564b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨41,by decide⟩
def lo2564 : CheckedMoment :=
  CheckedMoment.ofBessel lo2564b1 lo2564b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2564b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨45,by decide⟩
def hi2564b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨46,by decide⟩
def hi2564 : CheckedMoment :=
  CheckedMoment.ofBessel hi2564b1 hi2564b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2564 : meanBracketCheck (24843/25000) lo2564 hi2564=true := by decide +kernel
def bracket2564 : MeanBracket := meanBracketOfMoments (24843/25000) lo2564 hi2564 accepted2564
def lo2565b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨50,by decide⟩
def lo2565b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨51,by decide⟩
def lo2565 : CheckedMoment :=
  CheckedMoment.ofBessel lo2565b1 lo2565b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2565b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨55,by decide⟩
def hi2565b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨56,by decide⟩
def hi2565 : CheckedMoment :=
  CheckedMoment.ofBessel hi2565b1 hi2565b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2565 : meanBracketCheck (49687/50000) lo2565 hi2565=true := by decide +kernel
def bracket2565 : MeanBracket := meanBracketOfMoments (49687/50000) lo2565 hi2565 accepted2565
def lo2566b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨60,by decide⟩
def lo2566b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨61,by decide⟩
def lo2566 : CheckedMoment :=
  CheckedMoment.ofBessel lo2566b1 lo2566b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2566b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨1,by decide⟩
def hi2566b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨2,by decide⟩
def hi2566 : CheckedMoment :=
  CheckedMoment.ofBessel hi2566b1 hi2566b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2566 : meanBracketCheck (6211/6250) lo2566 hi2566=true := by decide +kernel
def bracket2566 : MeanBracket := meanBracketOfMoments (6211/6250) lo2566 hi2566 accepted2566
def lo2567b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨6,by decide⟩
def lo2567b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨7,by decide⟩
def lo2567 : CheckedMoment :=
  CheckedMoment.ofBessel lo2567b1 lo2567b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2567b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨11,by decide⟩
def hi2567b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨12,by decide⟩
def hi2567 : CheckedMoment :=
  CheckedMoment.ofBessel hi2567b1 hi2567b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2567 : meanBracketCheck (49689/50000) lo2567 hi2567=true := by decide +kernel
def bracket2567 : MeanBracket := meanBracketOfMoments (49689/50000) lo2567 hi2567 accepted2567
def lo2568b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨16,by decide⟩
def lo2568b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨17,by decide⟩
def lo2568 : CheckedMoment :=
  CheckedMoment.ofBessel lo2568b1 lo2568b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2568b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨21,by decide⟩
def hi2568b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨22,by decide⟩
def hi2568 : CheckedMoment :=
  CheckedMoment.ofBessel hi2568b1 hi2568b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2568 : meanBracketCheck (4969/5000) lo2568 hi2568=true := by decide +kernel
def bracket2568 : MeanBracket := meanBracketOfMoments (4969/5000) lo2568 hi2568 accepted2568
def lo2569b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨26,by decide⟩
def lo2569b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨27,by decide⟩
def lo2569 : CheckedMoment :=
  CheckedMoment.ofBessel lo2569b1 lo2569b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2569b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨31,by decide⟩
def hi2569b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨32,by decide⟩
def hi2569 : CheckedMoment :=
  CheckedMoment.ofBessel hi2569b1 hi2569b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2569 : meanBracketCheck (49691/50000) lo2569 hi2569=true := by decide +kernel
def bracket2569 : MeanBracket := meanBracketOfMoments (49691/50000) lo2569 hi2569 accepted2569
def lo2570b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨36,by decide⟩
def lo2570b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨37,by decide⟩
def lo2570 : CheckedMoment :=
  CheckedMoment.ofBessel lo2570b1 lo2570b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2570b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨41,by decide⟩
def hi2570b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨42,by decide⟩
def hi2570 : CheckedMoment :=
  CheckedMoment.ofBessel hi2570b1 hi2570b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2570 : meanBracketCheck (12423/12500) lo2570 hi2570=true := by decide +kernel
def bracket2570 : MeanBracket := meanBracketOfMoments (12423/12500) lo2570 hi2570 accepted2570
def lo2571b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨46,by decide⟩
def lo2571b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨47,by decide⟩
def lo2571 : CheckedMoment :=
  CheckedMoment.ofBessel lo2571b1 lo2571b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2571b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨51,by decide⟩
def hi2571b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨52,by decide⟩
def hi2571 : CheckedMoment :=
  CheckedMoment.ofBessel hi2571b1 hi2571b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2571 : meanBracketCheck (49693/50000) lo2571 hi2571=true := by decide +kernel
def bracket2571 : MeanBracket := meanBracketOfMoments (49693/50000) lo2571 hi2571 accepted2571
def lo2572b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨56,by decide⟩
def lo2572b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨57,by decide⟩
def lo2572 : CheckedMoment :=
  CheckedMoment.ofBessel lo2572b1 lo2572b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2572b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨61,by decide⟩
def hi2572b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨62,by decide⟩
def hi2572 : CheckedMoment :=
  CheckedMoment.ofBessel hi2572b1 hi2572b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2572 : meanBracketCheck (24847/25000) lo2572 hi2572=true := by decide +kernel
def bracket2572 : MeanBracket := meanBracketOfMoments (24847/25000) lo2572 hi2572 accepted2572
def lo2573b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨2,by decide⟩
def lo2573b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨3,by decide⟩
def lo2573 : CheckedMoment :=
  CheckedMoment.ofBessel lo2573b1 lo2573b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2573b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨7,by decide⟩
def hi2573b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨8,by decide⟩
def hi2573 : CheckedMoment :=
  CheckedMoment.ofBessel hi2573b1 hi2573b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2573 : meanBracketCheck (9939/10000) lo2573 hi2573=true := by decide +kernel
def bracket2573 : MeanBracket := meanBracketOfMoments (9939/10000) lo2573 hi2573 accepted2573
def lo2574b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨12,by decide⟩
def lo2574b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨13,by decide⟩
def lo2574 : CheckedMoment :=
  CheckedMoment.ofBessel lo2574b1 lo2574b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2574b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨17,by decide⟩
def hi2574b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨18,by decide⟩
def hi2574 : CheckedMoment :=
  CheckedMoment.ofBessel hi2574b1 hi2574b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2574 : meanBracketCheck (3106/3125) lo2574 hi2574=true := by decide +kernel
def bracket2574 : MeanBracket := meanBracketOfMoments (3106/3125) lo2574 hi2574 accepted2574
def lo2575b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨22,by decide⟩
def lo2575b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨23,by decide⟩
def lo2575 : CheckedMoment :=
  CheckedMoment.ofBessel lo2575b1 lo2575b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2575b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨27,by decide⟩
def hi2575b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨28,by decide⟩
def hi2575 : CheckedMoment :=
  CheckedMoment.ofBessel hi2575b1 hi2575b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2575 : meanBracketCheck (49697/50000) lo2575 hi2575=true := by decide +kernel
def bracket2575 : MeanBracket := meanBracketOfMoments (49697/50000) lo2575 hi2575 accepted2575
#print axioms bracket2560
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0160
