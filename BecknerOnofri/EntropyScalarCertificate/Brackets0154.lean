import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0385
import BecknerOnofri.EntropyScalarCertificate.Bessel0386
import BecknerOnofri.EntropyScalarCertificate.Bessel0387
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0154
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2464b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨0,by decide⟩
def lo2464b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨1,by decide⟩
def lo2464 : CheckedMoment :=
  CheckedMoment.ofBessel lo2464b1 lo2464b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2464b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨5,by decide⟩
def hi2464b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨6,by decide⟩
def hi2464 : CheckedMoment :=
  CheckedMoment.ofBessel hi2464b1 hi2464b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2464 : meanBracketCheck (24793/25000) lo2464 hi2464=true := by decide +kernel
def bracket2464 : MeanBracket := meanBracketOfMoments (24793/25000) lo2464 hi2464 accepted2464
def lo2465b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨10,by decide⟩
def lo2465b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨11,by decide⟩
def lo2465 : CheckedMoment :=
  CheckedMoment.ofBessel lo2465b1 lo2465b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2465b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨15,by decide⟩
def hi2465b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨16,by decide⟩
def hi2465 : CheckedMoment :=
  CheckedMoment.ofBessel hi2465b1 hi2465b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2465 : meanBracketCheck (49587/50000) lo2465 hi2465=true := by decide +kernel
def bracket2465 : MeanBracket := meanBracketOfMoments (49587/50000) lo2465 hi2465 accepted2465
def lo2466b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨20,by decide⟩
def lo2466b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨21,by decide⟩
def lo2466 : CheckedMoment :=
  CheckedMoment.ofBessel lo2466b1 lo2466b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2466b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨25,by decide⟩
def hi2466b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨26,by decide⟩
def hi2466 : CheckedMoment :=
  CheckedMoment.ofBessel hi2466b1 hi2466b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2466 : meanBracketCheck (12397/12500) lo2466 hi2466=true := by decide +kernel
def bracket2466 : MeanBracket := meanBracketOfMoments (12397/12500) lo2466 hi2466 accepted2466
def lo2467b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨30,by decide⟩
def lo2467b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨31,by decide⟩
def lo2467 : CheckedMoment :=
  CheckedMoment.ofBessel lo2467b1 lo2467b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2467b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨35,by decide⟩
def hi2467b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨36,by decide⟩
def hi2467 : CheckedMoment :=
  CheckedMoment.ofBessel hi2467b1 hi2467b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2467 : meanBracketCheck (49589/50000) lo2467 hi2467=true := by decide +kernel
def bracket2467 : MeanBracket := meanBracketOfMoments (49589/50000) lo2467 hi2467 accepted2467
def lo2468b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨40,by decide⟩
def lo2468b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨41,by decide⟩
def lo2468 : CheckedMoment :=
  CheckedMoment.ofBessel lo2468b1 lo2468b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2468b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨45,by decide⟩
def hi2468b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨46,by decide⟩
def hi2468 : CheckedMoment :=
  CheckedMoment.ofBessel hi2468b1 hi2468b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2468 : meanBracketCheck (4959/5000) lo2468 hi2468=true := by decide +kernel
def bracket2468 : MeanBracket := meanBracketOfMoments (4959/5000) lo2468 hi2468 accepted2468
def lo2469b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨50,by decide⟩
def lo2469b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨51,by decide⟩
def lo2469 : CheckedMoment :=
  CheckedMoment.ofBessel lo2469b1 lo2469b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2469b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨55,by decide⟩
def hi2469b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨56,by decide⟩
def hi2469 : CheckedMoment :=
  CheckedMoment.ofBessel hi2469b1 hi2469b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2469 : meanBracketCheck (49591/50000) lo2469 hi2469=true := by decide +kernel
def bracket2469 : MeanBracket := meanBracketOfMoments (49591/50000) lo2469 hi2469 accepted2469
def lo2470b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨60,by decide⟩
def lo2470b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0385.rows BesselBatch0385.accepted ⟨61,by decide⟩
def lo2470 : CheckedMoment :=
  CheckedMoment.ofBessel lo2470b1 lo2470b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2470b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨1,by decide⟩
def hi2470b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨2,by decide⟩
def hi2470 : CheckedMoment :=
  CheckedMoment.ofBessel hi2470b1 hi2470b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2470 : meanBracketCheck (6199/6250) lo2470 hi2470=true := by decide +kernel
def bracket2470 : MeanBracket := meanBracketOfMoments (6199/6250) lo2470 hi2470 accepted2470
def lo2471b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨6,by decide⟩
def lo2471b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨7,by decide⟩
def lo2471 : CheckedMoment :=
  CheckedMoment.ofBessel lo2471b1 lo2471b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2471b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨11,by decide⟩
def hi2471b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨12,by decide⟩
def hi2471 : CheckedMoment :=
  CheckedMoment.ofBessel hi2471b1 hi2471b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2471 : meanBracketCheck (49593/50000) lo2471 hi2471=true := by decide +kernel
def bracket2471 : MeanBracket := meanBracketOfMoments (49593/50000) lo2471 hi2471 accepted2471
def lo2472b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨16,by decide⟩
def lo2472b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨17,by decide⟩
def lo2472 : CheckedMoment :=
  CheckedMoment.ofBessel lo2472b1 lo2472b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2472b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨21,by decide⟩
def hi2472b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨22,by decide⟩
def hi2472 : CheckedMoment :=
  CheckedMoment.ofBessel hi2472b1 hi2472b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2472 : meanBracketCheck (24797/25000) lo2472 hi2472=true := by decide +kernel
def bracket2472 : MeanBracket := meanBracketOfMoments (24797/25000) lo2472 hi2472 accepted2472
def lo2473b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨26,by decide⟩
def lo2473b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨27,by decide⟩
def lo2473 : CheckedMoment :=
  CheckedMoment.ofBessel lo2473b1 lo2473b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2473b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨31,by decide⟩
def hi2473b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨32,by decide⟩
def hi2473 : CheckedMoment :=
  CheckedMoment.ofBessel hi2473b1 hi2473b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2473 : meanBracketCheck (9919/10000) lo2473 hi2473=true := by decide +kernel
def bracket2473 : MeanBracket := meanBracketOfMoments (9919/10000) lo2473 hi2473 accepted2473
def lo2474b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨36,by decide⟩
def lo2474b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨37,by decide⟩
def lo2474 : CheckedMoment :=
  CheckedMoment.ofBessel lo2474b1 lo2474b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2474b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨41,by decide⟩
def hi2474b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨42,by decide⟩
def hi2474 : CheckedMoment :=
  CheckedMoment.ofBessel hi2474b1 hi2474b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2474 : meanBracketCheck (12399/12500) lo2474 hi2474=true := by decide +kernel
def bracket2474 : MeanBracket := meanBracketOfMoments (12399/12500) lo2474 hi2474 accepted2474
def lo2475b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨46,by decide⟩
def lo2475b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨47,by decide⟩
def lo2475 : CheckedMoment :=
  CheckedMoment.ofBessel lo2475b1 lo2475b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2475b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨51,by decide⟩
def hi2475b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨52,by decide⟩
def hi2475 : CheckedMoment :=
  CheckedMoment.ofBessel hi2475b1 hi2475b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2475 : meanBracketCheck (49597/50000) lo2475 hi2475=true := by decide +kernel
def bracket2475 : MeanBracket := meanBracketOfMoments (49597/50000) lo2475 hi2475 accepted2475
def lo2476b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨56,by decide⟩
def lo2476b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨57,by decide⟩
def lo2476 : CheckedMoment :=
  CheckedMoment.ofBessel lo2476b1 lo2476b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2476b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨61,by decide⟩
def hi2476b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨62,by decide⟩
def hi2476 : CheckedMoment :=
  CheckedMoment.ofBessel hi2476b1 hi2476b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2476 : meanBracketCheck (24799/25000) lo2476 hi2476=true := by decide +kernel
def bracket2476 : MeanBracket := meanBracketOfMoments (24799/25000) lo2476 hi2476 accepted2476
def lo2477b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨2,by decide⟩
def lo2477b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨3,by decide⟩
def lo2477 : CheckedMoment :=
  CheckedMoment.ofBessel lo2477b1 lo2477b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2477b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨7,by decide⟩
def hi2477b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨8,by decide⟩
def hi2477 : CheckedMoment :=
  CheckedMoment.ofBessel hi2477b1 hi2477b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2477 : meanBracketCheck (49599/50000) lo2477 hi2477=true := by decide +kernel
def bracket2477 : MeanBracket := meanBracketOfMoments (49599/50000) lo2477 hi2477 accepted2477
def lo2478b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨12,by decide⟩
def lo2478b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨13,by decide⟩
def lo2478 : CheckedMoment :=
  CheckedMoment.ofBessel lo2478b1 lo2478b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2478b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨17,by decide⟩
def hi2478b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨18,by decide⟩
def hi2478 : CheckedMoment :=
  CheckedMoment.ofBessel hi2478b1 hi2478b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2478 : meanBracketCheck (124/125) lo2478 hi2478=true := by decide +kernel
def bracket2478 : MeanBracket := meanBracketOfMoments (124/125) lo2478 hi2478 accepted2478
def lo2479b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨22,by decide⟩
def lo2479b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨23,by decide⟩
def lo2479 : CheckedMoment :=
  CheckedMoment.ofBessel lo2479b1 lo2479b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2479b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨27,by decide⟩
def hi2479b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨28,by decide⟩
def hi2479 : CheckedMoment :=
  CheckedMoment.ofBessel hi2479b1 hi2479b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2479 : meanBracketCheck (49601/50000) lo2479 hi2479=true := by decide +kernel
def bracket2479 : MeanBracket := meanBracketOfMoments (49601/50000) lo2479 hi2479 accepted2479
#print axioms bracket2464
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0154
