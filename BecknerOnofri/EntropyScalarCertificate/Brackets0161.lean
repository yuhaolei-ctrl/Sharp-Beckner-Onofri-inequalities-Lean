import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0402
import BecknerOnofri.EntropyScalarCertificate.Bessel0403
import BecknerOnofri.EntropyScalarCertificate.Bessel0404
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0161
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2576b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨32,by decide⟩
def lo2576b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨33,by decide⟩
def lo2576 : CheckedMoment :=
  CheckedMoment.ofBessel lo2576b1 lo2576b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2576b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨37,by decide⟩
def hi2576b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨38,by decide⟩
def hi2576 : CheckedMoment :=
  CheckedMoment.ofBessel hi2576b1 hi2576b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2576 : meanBracketCheck (24849/25000) lo2576 hi2576=true := by decide +kernel
def bracket2576 : MeanBracket := meanBracketOfMoments (24849/25000) lo2576 hi2576 accepted2576
def lo2577b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨42,by decide⟩
def lo2577b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨43,by decide⟩
def lo2577 : CheckedMoment :=
  CheckedMoment.ofBessel lo2577b1 lo2577b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2577b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨47,by decide⟩
def hi2577b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨48,by decide⟩
def hi2577 : CheckedMoment :=
  CheckedMoment.ofBessel hi2577b1 hi2577b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2577 : meanBracketCheck (49699/50000) lo2577 hi2577=true := by decide +kernel
def bracket2577 : MeanBracket := meanBracketOfMoments (49699/50000) lo2577 hi2577 accepted2577
def lo2578b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨52,by decide⟩
def lo2578b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨53,by decide⟩
def lo2578 : CheckedMoment :=
  CheckedMoment.ofBessel lo2578b1 lo2578b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2578b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨57,by decide⟩
def hi2578b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨58,by decide⟩
def hi2578 : CheckedMoment :=
  CheckedMoment.ofBessel hi2578b1 hi2578b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2578 : meanBracketCheck (497/500) lo2578 hi2578=true := by decide +kernel
def bracket2578 : MeanBracket := meanBracketOfMoments (497/500) lo2578 hi2578 accepted2578
def lo2579b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨62,by decide⟩
def lo2579b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0402.rows BesselBatch0402.accepted ⟨63,by decide⟩
def lo2579 : CheckedMoment :=
  CheckedMoment.ofBessel lo2579b1 lo2579b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2579b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨3,by decide⟩
def hi2579b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨4,by decide⟩
def hi2579 : CheckedMoment :=
  CheckedMoment.ofBessel hi2579b1 hi2579b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2579 : meanBracketCheck (49701/50000) lo2579 hi2579=true := by decide +kernel
def bracket2579 : MeanBracket := meanBracketOfMoments (49701/50000) lo2579 hi2579 accepted2579
def lo2580b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨8,by decide⟩
def lo2580b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨9,by decide⟩
def lo2580 : CheckedMoment :=
  CheckedMoment.ofBessel lo2580b1 lo2580b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2580b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨13,by decide⟩
def hi2580b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨14,by decide⟩
def hi2580 : CheckedMoment :=
  CheckedMoment.ofBessel hi2580b1 hi2580b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2580 : meanBracketCheck (24851/25000) lo2580 hi2580=true := by decide +kernel
def bracket2580 : MeanBracket := meanBracketOfMoments (24851/25000) lo2580 hi2580 accepted2580
def lo2581b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨18,by decide⟩
def lo2581b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨19,by decide⟩
def lo2581 : CheckedMoment :=
  CheckedMoment.ofBessel lo2581b1 lo2581b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2581b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨23,by decide⟩
def hi2581b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨24,by decide⟩
def hi2581 : CheckedMoment :=
  CheckedMoment.ofBessel hi2581b1 hi2581b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2581 : meanBracketCheck (49703/50000) lo2581 hi2581=true := by decide +kernel
def bracket2581 : MeanBracket := meanBracketOfMoments (49703/50000) lo2581 hi2581 accepted2581
def lo2582b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨28,by decide⟩
def lo2582b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨29,by decide⟩
def lo2582 : CheckedMoment :=
  CheckedMoment.ofBessel lo2582b1 lo2582b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2582b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨33,by decide⟩
def hi2582b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨34,by decide⟩
def hi2582 : CheckedMoment :=
  CheckedMoment.ofBessel hi2582b1 hi2582b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2582 : meanBracketCheck (6213/6250) lo2582 hi2582=true := by decide +kernel
def bracket2582 : MeanBracket := meanBracketOfMoments (6213/6250) lo2582 hi2582 accepted2582
def lo2583b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨38,by decide⟩
def lo2583b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨39,by decide⟩
def lo2583 : CheckedMoment :=
  CheckedMoment.ofBessel lo2583b1 lo2583b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2583b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨43,by decide⟩
def hi2583b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨44,by decide⟩
def hi2583 : CheckedMoment :=
  CheckedMoment.ofBessel hi2583b1 hi2583b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2583 : meanBracketCheck (9941/10000) lo2583 hi2583=true := by decide +kernel
def bracket2583 : MeanBracket := meanBracketOfMoments (9941/10000) lo2583 hi2583 accepted2583
def lo2584b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨48,by decide⟩
def lo2584b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨49,by decide⟩
def lo2584 : CheckedMoment :=
  CheckedMoment.ofBessel lo2584b1 lo2584b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2584b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨53,by decide⟩
def hi2584b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨54,by decide⟩
def hi2584 : CheckedMoment :=
  CheckedMoment.ofBessel hi2584b1 hi2584b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2584 : meanBracketCheck (24853/25000) lo2584 hi2584=true := by decide +kernel
def bracket2584 : MeanBracket := meanBracketOfMoments (24853/25000) lo2584 hi2584 accepted2584
def lo2585b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨58,by decide⟩
def lo2585b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨59,by decide⟩
def lo2585 : CheckedMoment :=
  CheckedMoment.ofBessel lo2585b1 lo2585b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2585b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨63,by decide⟩
def hi2585b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨0,by decide⟩
def hi2585 : CheckedMoment :=
  CheckedMoment.ofBessel hi2585b1 hi2585b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2585 : meanBracketCheck (49707/50000) lo2585 hi2585=true := by decide +kernel
def bracket2585 : MeanBracket := meanBracketOfMoments (49707/50000) lo2585 hi2585 accepted2585
def lo2586b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨4,by decide⟩
def lo2586b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨5,by decide⟩
def lo2586 : CheckedMoment :=
  CheckedMoment.ofBessel lo2586b1 lo2586b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2586b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨9,by decide⟩
def hi2586b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨10,by decide⟩
def hi2586 : CheckedMoment :=
  CheckedMoment.ofBessel hi2586b1 hi2586b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2586 : meanBracketCheck (12427/12500) lo2586 hi2586=true := by decide +kernel
def bracket2586 : MeanBracket := meanBracketOfMoments (12427/12500) lo2586 hi2586 accepted2586
def lo2587b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨14,by decide⟩
def lo2587b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨15,by decide⟩
def lo2587 : CheckedMoment :=
  CheckedMoment.ofBessel lo2587b1 lo2587b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2587b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨19,by decide⟩
def hi2587b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨20,by decide⟩
def hi2587 : CheckedMoment :=
  CheckedMoment.ofBessel hi2587b1 hi2587b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2587 : meanBracketCheck (49709/50000) lo2587 hi2587=true := by decide +kernel
def bracket2587 : MeanBracket := meanBracketOfMoments (49709/50000) lo2587 hi2587 accepted2587
def lo2588b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨24,by decide⟩
def lo2588b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨25,by decide⟩
def lo2588 : CheckedMoment :=
  CheckedMoment.ofBessel lo2588b1 lo2588b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2588b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨29,by decide⟩
def hi2588b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨30,by decide⟩
def hi2588 : CheckedMoment :=
  CheckedMoment.ofBessel hi2588b1 hi2588b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2588 : meanBracketCheck (4971/5000) lo2588 hi2588=true := by decide +kernel
def bracket2588 : MeanBracket := meanBracketOfMoments (4971/5000) lo2588 hi2588 accepted2588
def lo2589b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨34,by decide⟩
def lo2589b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨35,by decide⟩
def lo2589 : CheckedMoment :=
  CheckedMoment.ofBessel lo2589b1 lo2589b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2589b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨39,by decide⟩
def hi2589b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨40,by decide⟩
def hi2589 : CheckedMoment :=
  CheckedMoment.ofBessel hi2589b1 hi2589b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2589 : meanBracketCheck (49711/50000) lo2589 hi2589=true := by decide +kernel
def bracket2589 : MeanBracket := meanBracketOfMoments (49711/50000) lo2589 hi2589 accepted2589
def lo2590b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨44,by decide⟩
def lo2590b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨45,by decide⟩
def lo2590 : CheckedMoment :=
  CheckedMoment.ofBessel lo2590b1 lo2590b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2590b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨49,by decide⟩
def hi2590b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨50,by decide⟩
def hi2590 : CheckedMoment :=
  CheckedMoment.ofBessel hi2590b1 hi2590b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2590 : meanBracketCheck (3107/3125) lo2590 hi2590=true := by decide +kernel
def bracket2590 : MeanBracket := meanBracketOfMoments (3107/3125) lo2590 hi2590 accepted2590
def lo2591b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨54,by decide⟩
def lo2591b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨55,by decide⟩
def lo2591 : CheckedMoment :=
  CheckedMoment.ofBessel lo2591b1 lo2591b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2591b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨59,by decide⟩
def hi2591b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨60,by decide⟩
def hi2591 : CheckedMoment :=
  CheckedMoment.ofBessel hi2591b1 hi2591b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2591 : meanBracketCheck (49713/50000) lo2591 hi2591=true := by decide +kernel
def bracket2591 : MeanBracket := meanBracketOfMoments (49713/50000) lo2591 hi2591 accepted2591
#print axioms bracket2576
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0161
