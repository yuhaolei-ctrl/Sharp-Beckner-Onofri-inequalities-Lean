module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0392
public import BecknerOnofri.EntropyScalarCertificate.Bessel0393
public import BecknerOnofri.EntropyScalarCertificate.Bessel0394

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0157
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2512b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨32,by decide⟩
def lo2512b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨33,by decide⟩
def lo2512 : CheckedMoment :=
  CheckedMoment.ofBessel lo2512b1 lo2512b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2512b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨37,by decide⟩
def hi2512b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨38,by decide⟩
def hi2512 : CheckedMoment :=
  CheckedMoment.ofBessel hi2512b1 hi2512b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2512 : meanBracketCheck (24817/25000) lo2512 hi2512=true := by decide +kernel
def bracket2512 : MeanBracket := meanBracketOfMoments (24817/25000) lo2512 hi2512 accepted2512
def lo2513b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨42,by decide⟩
def lo2513b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨43,by decide⟩
def lo2513 : CheckedMoment :=
  CheckedMoment.ofBessel lo2513b1 lo2513b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2513b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨47,by decide⟩
def hi2513b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨48,by decide⟩
def hi2513 : CheckedMoment :=
  CheckedMoment.ofBessel hi2513b1 hi2513b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2513 : meanBracketCheck (9927/10000) lo2513 hi2513=true := by decide +kernel
def bracket2513 : MeanBracket := meanBracketOfMoments (9927/10000) lo2513 hi2513 accepted2513
def lo2514b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨52,by decide⟩
def lo2514b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨53,by decide⟩
def lo2514 : CheckedMoment :=
  CheckedMoment.ofBessel lo2514b1 lo2514b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2514b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨57,by decide⟩
def hi2514b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨58,by decide⟩
def hi2514 : CheckedMoment :=
  CheckedMoment.ofBessel hi2514b1 hi2514b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2514 : meanBracketCheck (12409/12500) lo2514 hi2514=true := by decide +kernel
def bracket2514 : MeanBracket := meanBracketOfMoments (12409/12500) lo2514 hi2514 accepted2514
def lo2515b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨62,by decide⟩
def lo2515b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨63,by decide⟩
def lo2515 : CheckedMoment :=
  CheckedMoment.ofBessel lo2515b1 lo2515b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2515b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨3,by decide⟩
def hi2515b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨4,by decide⟩
def hi2515 : CheckedMoment :=
  CheckedMoment.ofBessel hi2515b1 hi2515b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2515 : meanBracketCheck (49637/50000) lo2515 hi2515=true := by decide +kernel
def bracket2515 : MeanBracket := meanBracketOfMoments (49637/50000) lo2515 hi2515 accepted2515
def lo2516b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨8,by decide⟩
def lo2516b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨9,by decide⟩
def lo2516 : CheckedMoment :=
  CheckedMoment.ofBessel lo2516b1 lo2516b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2516b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨13,by decide⟩
def hi2516b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨14,by decide⟩
def hi2516 : CheckedMoment :=
  CheckedMoment.ofBessel hi2516b1 hi2516b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2516 : meanBracketCheck (24819/25000) lo2516 hi2516=true := by decide +kernel
def bracket2516 : MeanBracket := meanBracketOfMoments (24819/25000) lo2516 hi2516 accepted2516
def lo2517b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨18,by decide⟩
def lo2517b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨19,by decide⟩
def lo2517 : CheckedMoment :=
  CheckedMoment.ofBessel lo2517b1 lo2517b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2517b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨23,by decide⟩
def hi2517b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨24,by decide⟩
def hi2517 : CheckedMoment :=
  CheckedMoment.ofBessel hi2517b1 hi2517b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2517 : meanBracketCheck (49639/50000) lo2517 hi2517=true := by decide +kernel
def bracket2517 : MeanBracket := meanBracketOfMoments (49639/50000) lo2517 hi2517 accepted2517
def lo2518b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨28,by decide⟩
def lo2518b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨29,by decide⟩
def lo2518 : CheckedMoment :=
  CheckedMoment.ofBessel lo2518b1 lo2518b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2518b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨33,by decide⟩
def hi2518b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨34,by decide⟩
def hi2518 : CheckedMoment :=
  CheckedMoment.ofBessel hi2518b1 hi2518b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2518 : meanBracketCheck (1241/1250) lo2518 hi2518=true := by decide +kernel
def bracket2518 : MeanBracket := meanBracketOfMoments (1241/1250) lo2518 hi2518 accepted2518
def lo2519b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨38,by decide⟩
def lo2519b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨39,by decide⟩
def lo2519 : CheckedMoment :=
  CheckedMoment.ofBessel lo2519b1 lo2519b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2519b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨43,by decide⟩
def hi2519b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨44,by decide⟩
def hi2519 : CheckedMoment :=
  CheckedMoment.ofBessel hi2519b1 hi2519b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2519 : meanBracketCheck (49641/50000) lo2519 hi2519=true := by decide +kernel
def bracket2519 : MeanBracket := meanBracketOfMoments (49641/50000) lo2519 hi2519 accepted2519
def lo2520b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨48,by decide⟩
def lo2520b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨49,by decide⟩
def lo2520 : CheckedMoment :=
  CheckedMoment.ofBessel lo2520b1 lo2520b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2520b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨53,by decide⟩
def hi2520b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨54,by decide⟩
def hi2520 : CheckedMoment :=
  CheckedMoment.ofBessel hi2520b1 hi2520b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2520 : meanBracketCheck (24821/25000) lo2520 hi2520=true := by decide +kernel
def bracket2520 : MeanBracket := meanBracketOfMoments (24821/25000) lo2520 hi2520 accepted2520
def lo2521b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨58,by decide⟩
def lo2521b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨59,by decide⟩
def lo2521 : CheckedMoment :=
  CheckedMoment.ofBessel lo2521b1 lo2521b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2521b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨63,by decide⟩
def hi2521b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨0,by decide⟩
def hi2521 : CheckedMoment :=
  CheckedMoment.ofBessel hi2521b1 hi2521b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2521 : meanBracketCheck (49643/50000) lo2521 hi2521=true := by decide +kernel
def bracket2521 : MeanBracket := meanBracketOfMoments (49643/50000) lo2521 hi2521 accepted2521
def lo2522b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨4,by decide⟩
def lo2522b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨5,by decide⟩
def lo2522 : CheckedMoment :=
  CheckedMoment.ofBessel lo2522b1 lo2522b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2522b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨9,by decide⟩
def hi2522b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨10,by decide⟩
def hi2522 : CheckedMoment :=
  CheckedMoment.ofBessel hi2522b1 hi2522b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2522 : meanBracketCheck (12411/12500) lo2522 hi2522=true := by decide +kernel
def bracket2522 : MeanBracket := meanBracketOfMoments (12411/12500) lo2522 hi2522 accepted2522
def lo2523b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨14,by decide⟩
def lo2523b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨15,by decide⟩
def lo2523 : CheckedMoment :=
  CheckedMoment.ofBessel lo2523b1 lo2523b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2523b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨19,by decide⟩
def hi2523b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨20,by decide⟩
def hi2523 : CheckedMoment :=
  CheckedMoment.ofBessel hi2523b1 hi2523b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2523 : meanBracketCheck (9929/10000) lo2523 hi2523=true := by decide +kernel
def bracket2523 : MeanBracket := meanBracketOfMoments (9929/10000) lo2523 hi2523 accepted2523
def lo2524b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨24,by decide⟩
def lo2524b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨25,by decide⟩
def lo2524 : CheckedMoment :=
  CheckedMoment.ofBessel lo2524b1 lo2524b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2524b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨29,by decide⟩
def hi2524b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨30,by decide⟩
def hi2524 : CheckedMoment :=
  CheckedMoment.ofBessel hi2524b1 hi2524b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2524 : meanBracketCheck (24823/25000) lo2524 hi2524=true := by decide +kernel
def bracket2524 : MeanBracket := meanBracketOfMoments (24823/25000) lo2524 hi2524 accepted2524
def lo2525b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨34,by decide⟩
def lo2525b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨35,by decide⟩
def lo2525 : CheckedMoment :=
  CheckedMoment.ofBessel lo2525b1 lo2525b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2525b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨39,by decide⟩
def hi2525b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨40,by decide⟩
def hi2525 : CheckedMoment :=
  CheckedMoment.ofBessel hi2525b1 hi2525b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2525 : meanBracketCheck (49647/50000) lo2525 hi2525=true := by decide +kernel
def bracket2525 : MeanBracket := meanBracketOfMoments (49647/50000) lo2525 hi2525 accepted2525
def lo2526b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨44,by decide⟩
def lo2526b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨45,by decide⟩
def lo2526 : CheckedMoment :=
  CheckedMoment.ofBessel lo2526b1 lo2526b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2526b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨49,by decide⟩
def hi2526b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨50,by decide⟩
def hi2526 : CheckedMoment :=
  CheckedMoment.ofBessel hi2526b1 hi2526b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2526 : meanBracketCheck (3103/3125) lo2526 hi2526=true := by decide +kernel
def bracket2526 : MeanBracket := meanBracketOfMoments (3103/3125) lo2526 hi2526 accepted2526
def lo2527b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨54,by decide⟩
def lo2527b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨55,by decide⟩
def lo2527 : CheckedMoment :=
  CheckedMoment.ofBessel lo2527b1 lo2527b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2527b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨59,by decide⟩
def hi2527b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨60,by decide⟩
def hi2527 : CheckedMoment :=
  CheckedMoment.ofBessel hi2527b1 hi2527b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2527 : meanBracketCheck (49649/50000) lo2527 hi2527=true := by decide +kernel
def bracket2527 : MeanBracket := meanBracketOfMoments (49649/50000) lo2527 hi2527 accepted2527
#print axioms bracket2512
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0157
