import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0397
import BecknerOnofri.EntropyScalarCertificate.Bessel0398
import BecknerOnofri.EntropyScalarCertificate.Bessel0399
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0159
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2544b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨32,by decide⟩
def lo2544b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨33,by decide⟩
def lo2544 : CheckedMoment :=
  CheckedMoment.ofBessel lo2544b1 lo2544b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2544b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨37,by decide⟩
def hi2544b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨38,by decide⟩
def hi2544 : CheckedMoment :=
  CheckedMoment.ofBessel hi2544b1 hi2544b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2544 : meanBracketCheck (24833/25000) lo2544 hi2544=true := by decide +kernel
def bracket2544 : MeanBracket := meanBracketOfMoments (24833/25000) lo2544 hi2544 accepted2544
def lo2545b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨42,by decide⟩
def lo2545b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨43,by decide⟩
def lo2545 : CheckedMoment :=
  CheckedMoment.ofBessel lo2545b1 lo2545b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2545b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨47,by decide⟩
def hi2545b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨48,by decide⟩
def hi2545 : CheckedMoment :=
  CheckedMoment.ofBessel hi2545b1 hi2545b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2545 : meanBracketCheck (49667/50000) lo2545 hi2545=true := by decide +kernel
def bracket2545 : MeanBracket := meanBracketOfMoments (49667/50000) lo2545 hi2545 accepted2545
def lo2546b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨52,by decide⟩
def lo2546b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨53,by decide⟩
def lo2546 : CheckedMoment :=
  CheckedMoment.ofBessel lo2546b1 lo2546b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2546b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨57,by decide⟩
def hi2546b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨58,by decide⟩
def hi2546 : CheckedMoment :=
  CheckedMoment.ofBessel hi2546b1 hi2546b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2546 : meanBracketCheck (12417/12500) lo2546 hi2546=true := by decide +kernel
def bracket2546 : MeanBracket := meanBracketOfMoments (12417/12500) lo2546 hi2546 accepted2546
def lo2547b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨62,by decide⟩
def lo2547b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨63,by decide⟩
def lo2547 : CheckedMoment :=
  CheckedMoment.ofBessel lo2547b1 lo2547b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2547b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨3,by decide⟩
def hi2547b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨4,by decide⟩
def hi2547 : CheckedMoment :=
  CheckedMoment.ofBessel hi2547b1 hi2547b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2547 : meanBracketCheck (49669/50000) lo2547 hi2547=true := by decide +kernel
def bracket2547 : MeanBracket := meanBracketOfMoments (49669/50000) lo2547 hi2547 accepted2547
def lo2548b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨8,by decide⟩
def lo2548b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨9,by decide⟩
def lo2548 : CheckedMoment :=
  CheckedMoment.ofBessel lo2548b1 lo2548b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2548b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨13,by decide⟩
def hi2548b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨14,by decide⟩
def hi2548 : CheckedMoment :=
  CheckedMoment.ofBessel hi2548b1 hi2548b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2548 : meanBracketCheck (4967/5000) lo2548 hi2548=true := by decide +kernel
def bracket2548 : MeanBracket := meanBracketOfMoments (4967/5000) lo2548 hi2548 accepted2548
def lo2549b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨18,by decide⟩
def lo2549b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨19,by decide⟩
def lo2549 : CheckedMoment :=
  CheckedMoment.ofBessel lo2549b1 lo2549b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2549b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨23,by decide⟩
def hi2549b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨24,by decide⟩
def hi2549 : CheckedMoment :=
  CheckedMoment.ofBessel hi2549b1 hi2549b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2549 : meanBracketCheck (49671/50000) lo2549 hi2549=true := by decide +kernel
def bracket2549 : MeanBracket := meanBracketOfMoments (49671/50000) lo2549 hi2549 accepted2549
def lo2550b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨28,by decide⟩
def lo2550b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨29,by decide⟩
def lo2550 : CheckedMoment :=
  CheckedMoment.ofBessel lo2550b1 lo2550b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2550b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨33,by decide⟩
def hi2550b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨34,by decide⟩
def hi2550 : CheckedMoment :=
  CheckedMoment.ofBessel hi2550b1 hi2550b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2550 : meanBracketCheck (6209/6250) lo2550 hi2550=true := by decide +kernel
def bracket2550 : MeanBracket := meanBracketOfMoments (6209/6250) lo2550 hi2550 accepted2550
def lo2551b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨38,by decide⟩
def lo2551b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨39,by decide⟩
def lo2551 : CheckedMoment :=
  CheckedMoment.ofBessel lo2551b1 lo2551b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2551b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨43,by decide⟩
def hi2551b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨44,by decide⟩
def hi2551 : CheckedMoment :=
  CheckedMoment.ofBessel hi2551b1 hi2551b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2551 : meanBracketCheck (49673/50000) lo2551 hi2551=true := by decide +kernel
def bracket2551 : MeanBracket := meanBracketOfMoments (49673/50000) lo2551 hi2551 accepted2551
def lo2552b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨48,by decide⟩
def lo2552b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨49,by decide⟩
def lo2552 : CheckedMoment :=
  CheckedMoment.ofBessel lo2552b1 lo2552b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2552b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨53,by decide⟩
def hi2552b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨54,by decide⟩
def hi2552 : CheckedMoment :=
  CheckedMoment.ofBessel hi2552b1 hi2552b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2552 : meanBracketCheck (24837/25000) lo2552 hi2552=true := by decide +kernel
def bracket2552 : MeanBracket := meanBracketOfMoments (24837/25000) lo2552 hi2552 accepted2552
def lo2553b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨58,by decide⟩
def lo2553b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨59,by decide⟩
def lo2553 : CheckedMoment :=
  CheckedMoment.ofBessel lo2553b1 lo2553b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2553b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨63,by decide⟩
def hi2553b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨0,by decide⟩
def hi2553 : CheckedMoment :=
  CheckedMoment.ofBessel hi2553b1 hi2553b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2553 : meanBracketCheck (1987/2000) lo2553 hi2553=true := by decide +kernel
def bracket2553 : MeanBracket := meanBracketOfMoments (1987/2000) lo2553 hi2553 accepted2553
def lo2554b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨4,by decide⟩
def lo2554b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨5,by decide⟩
def lo2554 : CheckedMoment :=
  CheckedMoment.ofBessel lo2554b1 lo2554b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2554b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨9,by decide⟩
def hi2554b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨10,by decide⟩
def hi2554 : CheckedMoment :=
  CheckedMoment.ofBessel hi2554b1 hi2554b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2554 : meanBracketCheck (12419/12500) lo2554 hi2554=true := by decide +kernel
def bracket2554 : MeanBracket := meanBracketOfMoments (12419/12500) lo2554 hi2554 accepted2554
def lo2555b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨14,by decide⟩
def lo2555b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨15,by decide⟩
def lo2555 : CheckedMoment :=
  CheckedMoment.ofBessel lo2555b1 lo2555b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2555b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨19,by decide⟩
def hi2555b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨20,by decide⟩
def hi2555 : CheckedMoment :=
  CheckedMoment.ofBessel hi2555b1 hi2555b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2555 : meanBracketCheck (49677/50000) lo2555 hi2555=true := by decide +kernel
def bracket2555 : MeanBracket := meanBracketOfMoments (49677/50000) lo2555 hi2555 accepted2555
def lo2556b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨24,by decide⟩
def lo2556b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨25,by decide⟩
def lo2556 : CheckedMoment :=
  CheckedMoment.ofBessel lo2556b1 lo2556b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2556b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨29,by decide⟩
def hi2556b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨30,by decide⟩
def hi2556 : CheckedMoment :=
  CheckedMoment.ofBessel hi2556b1 hi2556b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2556 : meanBracketCheck (24839/25000) lo2556 hi2556=true := by decide +kernel
def bracket2556 : MeanBracket := meanBracketOfMoments (24839/25000) lo2556 hi2556 accepted2556
def lo2557b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨34,by decide⟩
def lo2557b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨35,by decide⟩
def lo2557 : CheckedMoment :=
  CheckedMoment.ofBessel lo2557b1 lo2557b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2557b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨39,by decide⟩
def hi2557b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨40,by decide⟩
def hi2557 : CheckedMoment :=
  CheckedMoment.ofBessel hi2557b1 hi2557b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2557 : meanBracketCheck (49679/50000) lo2557 hi2557=true := by decide +kernel
def bracket2557 : MeanBracket := meanBracketOfMoments (49679/50000) lo2557 hi2557 accepted2557
def lo2558b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨44,by decide⟩
def lo2558b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨45,by decide⟩
def lo2558 : CheckedMoment :=
  CheckedMoment.ofBessel lo2558b1 lo2558b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2558b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨49,by decide⟩
def hi2558b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨50,by decide⟩
def hi2558 : CheckedMoment :=
  CheckedMoment.ofBessel hi2558b1 hi2558b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2558 : meanBracketCheck (621/625) lo2558 hi2558=true := by decide +kernel
def bracket2558 : MeanBracket := meanBracketOfMoments (621/625) lo2558 hi2558 accepted2558
def lo2559b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨54,by decide⟩
def lo2559b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨55,by decide⟩
def lo2559 : CheckedMoment :=
  CheckedMoment.ofBessel lo2559b1 lo2559b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2559b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨59,by decide⟩
def hi2559b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨60,by decide⟩
def hi2559 : CheckedMoment :=
  CheckedMoment.ofBessel hi2559b1 hi2559b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2559 : meanBracketCheck (49681/50000) lo2559 hi2559=true := by decide +kernel
def bracket2559 : MeanBracket := meanBracketOfMoments (49681/50000) lo2559 hi2559 accepted2559
#print axioms bracket2544
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0159
