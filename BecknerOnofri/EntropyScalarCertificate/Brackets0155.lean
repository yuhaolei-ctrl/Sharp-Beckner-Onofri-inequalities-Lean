import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0387
import BecknerOnofri.EntropyScalarCertificate.Bessel0388
import BecknerOnofri.EntropyScalarCertificate.Bessel0389
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0155
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2480b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨32,by decide⟩
def lo2480b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨33,by decide⟩
def lo2480 : CheckedMoment :=
  CheckedMoment.ofBessel lo2480b1 lo2480b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2480b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨37,by decide⟩
def hi2480b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨38,by decide⟩
def hi2480 : CheckedMoment :=
  CheckedMoment.ofBessel hi2480b1 hi2480b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2480 : meanBracketCheck (24801/25000) lo2480 hi2480=true := by decide +kernel
def bracket2480 : MeanBracket := meanBracketOfMoments (24801/25000) lo2480 hi2480 accepted2480
def lo2481b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨42,by decide⟩
def lo2481b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨43,by decide⟩
def lo2481 : CheckedMoment :=
  CheckedMoment.ofBessel lo2481b1 lo2481b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2481b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨47,by decide⟩
def hi2481b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨48,by decide⟩
def hi2481 : CheckedMoment :=
  CheckedMoment.ofBessel hi2481b1 hi2481b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2481 : meanBracketCheck (49603/50000) lo2481 hi2481=true := by decide +kernel
def bracket2481 : MeanBracket := meanBracketOfMoments (49603/50000) lo2481 hi2481 accepted2481
def lo2482b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨52,by decide⟩
def lo2482b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨53,by decide⟩
def lo2482 : CheckedMoment :=
  CheckedMoment.ofBessel lo2482b1 lo2482b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2482b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨57,by decide⟩
def hi2482b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨58,by decide⟩
def hi2482 : CheckedMoment :=
  CheckedMoment.ofBessel hi2482b1 hi2482b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2482 : meanBracketCheck (12401/12500) lo2482 hi2482=true := by decide +kernel
def bracket2482 : MeanBracket := meanBracketOfMoments (12401/12500) lo2482 hi2482 accepted2482
def lo2483b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨62,by decide⟩
def lo2483b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨63,by decide⟩
def lo2483 : CheckedMoment :=
  CheckedMoment.ofBessel lo2483b1 lo2483b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2483b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨3,by decide⟩
def hi2483b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨4,by decide⟩
def hi2483 : CheckedMoment :=
  CheckedMoment.ofBessel hi2483b1 hi2483b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2483 : meanBracketCheck (9921/10000) lo2483 hi2483=true := by decide +kernel
def bracket2483 : MeanBracket := meanBracketOfMoments (9921/10000) lo2483 hi2483 accepted2483
def lo2484b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨8,by decide⟩
def lo2484b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨9,by decide⟩
def lo2484 : CheckedMoment :=
  CheckedMoment.ofBessel lo2484b1 lo2484b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2484b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨13,by decide⟩
def hi2484b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨14,by decide⟩
def hi2484 : CheckedMoment :=
  CheckedMoment.ofBessel hi2484b1 hi2484b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2484 : meanBracketCheck (24803/25000) lo2484 hi2484=true := by decide +kernel
def bracket2484 : MeanBracket := meanBracketOfMoments (24803/25000) lo2484 hi2484 accepted2484
def lo2485b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨18,by decide⟩
def lo2485b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨19,by decide⟩
def lo2485 : CheckedMoment :=
  CheckedMoment.ofBessel lo2485b1 lo2485b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2485b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨23,by decide⟩
def hi2485b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨24,by decide⟩
def hi2485 : CheckedMoment :=
  CheckedMoment.ofBessel hi2485b1 hi2485b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2485 : meanBracketCheck (49607/50000) lo2485 hi2485=true := by decide +kernel
def bracket2485 : MeanBracket := meanBracketOfMoments (49607/50000) lo2485 hi2485 accepted2485
def lo2486b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨28,by decide⟩
def lo2486b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨29,by decide⟩
def lo2486 : CheckedMoment :=
  CheckedMoment.ofBessel lo2486b1 lo2486b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2486b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨33,by decide⟩
def hi2486b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨34,by decide⟩
def hi2486 : CheckedMoment :=
  CheckedMoment.ofBessel hi2486b1 hi2486b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2486 : meanBracketCheck (6201/6250) lo2486 hi2486=true := by decide +kernel
def bracket2486 : MeanBracket := meanBracketOfMoments (6201/6250) lo2486 hi2486 accepted2486
def lo2487b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨38,by decide⟩
def lo2487b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨39,by decide⟩
def lo2487 : CheckedMoment :=
  CheckedMoment.ofBessel lo2487b1 lo2487b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2487b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨43,by decide⟩
def hi2487b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨44,by decide⟩
def hi2487 : CheckedMoment :=
  CheckedMoment.ofBessel hi2487b1 hi2487b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2487 : meanBracketCheck (49609/50000) lo2487 hi2487=true := by decide +kernel
def bracket2487 : MeanBracket := meanBracketOfMoments (49609/50000) lo2487 hi2487 accepted2487
def lo2488b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨48,by decide⟩
def lo2488b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨49,by decide⟩
def lo2488 : CheckedMoment :=
  CheckedMoment.ofBessel lo2488b1 lo2488b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2488b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨53,by decide⟩
def hi2488b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨54,by decide⟩
def hi2488 : CheckedMoment :=
  CheckedMoment.ofBessel hi2488b1 hi2488b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2488 : meanBracketCheck (4961/5000) lo2488 hi2488=true := by decide +kernel
def bracket2488 : MeanBracket := meanBracketOfMoments (4961/5000) lo2488 hi2488 accepted2488
def lo2489b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨58,by decide⟩
def lo2489b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨59,by decide⟩
def lo2489 : CheckedMoment :=
  CheckedMoment.ofBessel lo2489b1 lo2489b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2489b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨63,by decide⟩
def hi2489b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨0,by decide⟩
def hi2489 : CheckedMoment :=
  CheckedMoment.ofBessel hi2489b1 hi2489b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2489 : meanBracketCheck (49611/50000) lo2489 hi2489=true := by decide +kernel
def bracket2489 : MeanBracket := meanBracketOfMoments (49611/50000) lo2489 hi2489 accepted2489
def lo2490b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨4,by decide⟩
def lo2490b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨5,by decide⟩
def lo2490 : CheckedMoment :=
  CheckedMoment.ofBessel lo2490b1 lo2490b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2490b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨9,by decide⟩
def hi2490b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨10,by decide⟩
def hi2490 : CheckedMoment :=
  CheckedMoment.ofBessel hi2490b1 hi2490b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2490 : meanBracketCheck (12403/12500) lo2490 hi2490=true := by decide +kernel
def bracket2490 : MeanBracket := meanBracketOfMoments (12403/12500) lo2490 hi2490 accepted2490
def lo2491b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨14,by decide⟩
def lo2491b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨15,by decide⟩
def lo2491 : CheckedMoment :=
  CheckedMoment.ofBessel lo2491b1 lo2491b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2491b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨19,by decide⟩
def hi2491b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨20,by decide⟩
def hi2491 : CheckedMoment :=
  CheckedMoment.ofBessel hi2491b1 hi2491b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2491 : meanBracketCheck (49613/50000) lo2491 hi2491=true := by decide +kernel
def bracket2491 : MeanBracket := meanBracketOfMoments (49613/50000) lo2491 hi2491 accepted2491
def lo2492b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨24,by decide⟩
def lo2492b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨25,by decide⟩
def lo2492 : CheckedMoment :=
  CheckedMoment.ofBessel lo2492b1 lo2492b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2492b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨29,by decide⟩
def hi2492b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨30,by decide⟩
def hi2492 : CheckedMoment :=
  CheckedMoment.ofBessel hi2492b1 hi2492b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2492 : meanBracketCheck (24807/25000) lo2492 hi2492=true := by decide +kernel
def bracket2492 : MeanBracket := meanBracketOfMoments (24807/25000) lo2492 hi2492 accepted2492
def lo2493b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨34,by decide⟩
def lo2493b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨35,by decide⟩
def lo2493 : CheckedMoment :=
  CheckedMoment.ofBessel lo2493b1 lo2493b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2493b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨39,by decide⟩
def hi2493b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨40,by decide⟩
def hi2493 : CheckedMoment :=
  CheckedMoment.ofBessel hi2493b1 hi2493b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2493 : meanBracketCheck (9923/10000) lo2493 hi2493=true := by decide +kernel
def bracket2493 : MeanBracket := meanBracketOfMoments (9923/10000) lo2493 hi2493 accepted2493
def lo2494b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨44,by decide⟩
def lo2494b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨45,by decide⟩
def lo2494 : CheckedMoment :=
  CheckedMoment.ofBessel lo2494b1 lo2494b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2494b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨49,by decide⟩
def hi2494b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨50,by decide⟩
def hi2494 : CheckedMoment :=
  CheckedMoment.ofBessel hi2494b1 hi2494b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2494 : meanBracketCheck (3101/3125) lo2494 hi2494=true := by decide +kernel
def bracket2494 : MeanBracket := meanBracketOfMoments (3101/3125) lo2494 hi2494 accepted2494
def lo2495b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨54,by decide⟩
def lo2495b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨55,by decide⟩
def lo2495 : CheckedMoment :=
  CheckedMoment.ofBessel lo2495b1 lo2495b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2495b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨59,by decide⟩
def hi2495b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨60,by decide⟩
def hi2495 : CheckedMoment :=
  CheckedMoment.ofBessel hi2495b1 hi2495b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2495 : meanBracketCheck (49617/50000) lo2495 hi2495=true := by decide +kernel
def bracket2495 : MeanBracket := meanBracketOfMoments (49617/50000) lo2495 hi2495 accepted2495
#print axioms bracket2480
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0155
