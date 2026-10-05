import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0395
import BecknerOnofri.EntropyScalarCertificate.Bessel0396
import BecknerOnofri.EntropyScalarCertificate.Bessel0397
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0158
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2528b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨0,by decide⟩
def lo2528b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨1,by decide⟩
def lo2528 : CheckedMoment :=
  CheckedMoment.ofBessel lo2528b1 lo2528b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2528b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨5,by decide⟩
def hi2528b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨6,by decide⟩
def hi2528 : CheckedMoment :=
  CheckedMoment.ofBessel hi2528b1 hi2528b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2528 : meanBracketCheck (993/1000) lo2528 hi2528=true := by decide +kernel
def bracket2528 : MeanBracket := meanBracketOfMoments (993/1000) lo2528 hi2528 accepted2528
def lo2529b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨10,by decide⟩
def lo2529b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨11,by decide⟩
def lo2529 : CheckedMoment :=
  CheckedMoment.ofBessel lo2529b1 lo2529b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2529b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨15,by decide⟩
def hi2529b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨16,by decide⟩
def hi2529 : CheckedMoment :=
  CheckedMoment.ofBessel hi2529b1 hi2529b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2529 : meanBracketCheck (49651/50000) lo2529 hi2529=true := by decide +kernel
def bracket2529 : MeanBracket := meanBracketOfMoments (49651/50000) lo2529 hi2529 accepted2529
def lo2530b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨20,by decide⟩
def lo2530b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨21,by decide⟩
def lo2530 : CheckedMoment :=
  CheckedMoment.ofBessel lo2530b1 lo2530b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2530b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨25,by decide⟩
def hi2530b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨26,by decide⟩
def hi2530 : CheckedMoment :=
  CheckedMoment.ofBessel hi2530b1 hi2530b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2530 : meanBracketCheck (12413/12500) lo2530 hi2530=true := by decide +kernel
def bracket2530 : MeanBracket := meanBracketOfMoments (12413/12500) lo2530 hi2530 accepted2530
def lo2531b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨30,by decide⟩
def lo2531b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨31,by decide⟩
def lo2531 : CheckedMoment :=
  CheckedMoment.ofBessel lo2531b1 lo2531b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2531b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨35,by decide⟩
def hi2531b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨36,by decide⟩
def hi2531 : CheckedMoment :=
  CheckedMoment.ofBessel hi2531b1 hi2531b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2531 : meanBracketCheck (49653/50000) lo2531 hi2531=true := by decide +kernel
def bracket2531 : MeanBracket := meanBracketOfMoments (49653/50000) lo2531 hi2531 accepted2531
def lo2532b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨40,by decide⟩
def lo2532b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨41,by decide⟩
def lo2532 : CheckedMoment :=
  CheckedMoment.ofBessel lo2532b1 lo2532b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2532b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨45,by decide⟩
def hi2532b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨46,by decide⟩
def hi2532 : CheckedMoment :=
  CheckedMoment.ofBessel hi2532b1 hi2532b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2532 : meanBracketCheck (24827/25000) lo2532 hi2532=true := by decide +kernel
def bracket2532 : MeanBracket := meanBracketOfMoments (24827/25000) lo2532 hi2532 accepted2532
def lo2533b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨50,by decide⟩
def lo2533b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨51,by decide⟩
def lo2533 : CheckedMoment :=
  CheckedMoment.ofBessel lo2533b1 lo2533b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2533b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨55,by decide⟩
def hi2533b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨56,by decide⟩
def hi2533 : CheckedMoment :=
  CheckedMoment.ofBessel hi2533b1 hi2533b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2533 : meanBracketCheck (9931/10000) lo2533 hi2533=true := by decide +kernel
def bracket2533 : MeanBracket := meanBracketOfMoments (9931/10000) lo2533 hi2533 accepted2533
def lo2534b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨60,by decide⟩
def lo2534b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨61,by decide⟩
def lo2534 : CheckedMoment :=
  CheckedMoment.ofBessel lo2534b1 lo2534b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2534b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨1,by decide⟩
def hi2534b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨2,by decide⟩
def hi2534 : CheckedMoment :=
  CheckedMoment.ofBessel hi2534b1 hi2534b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2534 : meanBracketCheck (6207/6250) lo2534 hi2534=true := by decide +kernel
def bracket2534 : MeanBracket := meanBracketOfMoments (6207/6250) lo2534 hi2534 accepted2534
def lo2535b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨6,by decide⟩
def lo2535b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨7,by decide⟩
def lo2535 : CheckedMoment :=
  CheckedMoment.ofBessel lo2535b1 lo2535b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2535b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨11,by decide⟩
def hi2535b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨12,by decide⟩
def hi2535 : CheckedMoment :=
  CheckedMoment.ofBessel hi2535b1 hi2535b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2535 : meanBracketCheck (49657/50000) lo2535 hi2535=true := by decide +kernel
def bracket2535 : MeanBracket := meanBracketOfMoments (49657/50000) lo2535 hi2535 accepted2535
def lo2536b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨16,by decide⟩
def lo2536b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨17,by decide⟩
def lo2536 : CheckedMoment :=
  CheckedMoment.ofBessel lo2536b1 lo2536b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2536b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨21,by decide⟩
def hi2536b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨22,by decide⟩
def hi2536 : CheckedMoment :=
  CheckedMoment.ofBessel hi2536b1 hi2536b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2536 : meanBracketCheck (24829/25000) lo2536 hi2536=true := by decide +kernel
def bracket2536 : MeanBracket := meanBracketOfMoments (24829/25000) lo2536 hi2536 accepted2536
def lo2537b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨26,by decide⟩
def lo2537b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨27,by decide⟩
def lo2537 : CheckedMoment :=
  CheckedMoment.ofBessel lo2537b1 lo2537b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2537b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨31,by decide⟩
def hi2537b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨32,by decide⟩
def hi2537 : CheckedMoment :=
  CheckedMoment.ofBessel hi2537b1 hi2537b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2537 : meanBracketCheck (49659/50000) lo2537 hi2537=true := by decide +kernel
def bracket2537 : MeanBracket := meanBracketOfMoments (49659/50000) lo2537 hi2537 accepted2537
def lo2538b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨36,by decide⟩
def lo2538b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨37,by decide⟩
def lo2538 : CheckedMoment :=
  CheckedMoment.ofBessel lo2538b1 lo2538b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2538b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨41,by decide⟩
def hi2538b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨42,by decide⟩
def hi2538 : CheckedMoment :=
  CheckedMoment.ofBessel hi2538b1 hi2538b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2538 : meanBracketCheck (2483/2500) lo2538 hi2538=true := by decide +kernel
def bracket2538 : MeanBracket := meanBracketOfMoments (2483/2500) lo2538 hi2538 accepted2538
def lo2539b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨46,by decide⟩
def lo2539b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨47,by decide⟩
def lo2539 : CheckedMoment :=
  CheckedMoment.ofBessel lo2539b1 lo2539b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2539b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨51,by decide⟩
def hi2539b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨52,by decide⟩
def hi2539 : CheckedMoment :=
  CheckedMoment.ofBessel hi2539b1 hi2539b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2539 : meanBracketCheck (49661/50000) lo2539 hi2539=true := by decide +kernel
def bracket2539 : MeanBracket := meanBracketOfMoments (49661/50000) lo2539 hi2539 accepted2539
def lo2540b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨56,by decide⟩
def lo2540b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨57,by decide⟩
def lo2540 : CheckedMoment :=
  CheckedMoment.ofBessel lo2540b1 lo2540b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2540b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨61,by decide⟩
def hi2540b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨62,by decide⟩
def hi2540 : CheckedMoment :=
  CheckedMoment.ofBessel hi2540b1 hi2540b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2540 : meanBracketCheck (24831/25000) lo2540 hi2540=true := by decide +kernel
def bracket2540 : MeanBracket := meanBracketOfMoments (24831/25000) lo2540 hi2540 accepted2540
def lo2541b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨2,by decide⟩
def lo2541b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨3,by decide⟩
def lo2541 : CheckedMoment :=
  CheckedMoment.ofBessel lo2541b1 lo2541b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2541b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨7,by decide⟩
def hi2541b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨8,by decide⟩
def hi2541 : CheckedMoment :=
  CheckedMoment.ofBessel hi2541b1 hi2541b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2541 : meanBracketCheck (49663/50000) lo2541 hi2541=true := by decide +kernel
def bracket2541 : MeanBracket := meanBracketOfMoments (49663/50000) lo2541 hi2541 accepted2541
def lo2542b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨12,by decide⟩
def lo2542b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨13,by decide⟩
def lo2542 : CheckedMoment :=
  CheckedMoment.ofBessel lo2542b1 lo2542b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2542b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨17,by decide⟩
def hi2542b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨18,by decide⟩
def hi2542 : CheckedMoment :=
  CheckedMoment.ofBessel hi2542b1 hi2542b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2542 : meanBracketCheck (3104/3125) lo2542 hi2542=true := by decide +kernel
def bracket2542 : MeanBracket := meanBracketOfMoments (3104/3125) lo2542 hi2542 accepted2542
def lo2543b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨22,by decide⟩
def lo2543b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨23,by decide⟩
def lo2543 : CheckedMoment :=
  CheckedMoment.ofBessel lo2543b1 lo2543b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2543b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨27,by decide⟩
def hi2543b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨28,by decide⟩
def hi2543 : CheckedMoment :=
  CheckedMoment.ofBessel hi2543b1 hi2543b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2543 : meanBracketCheck (9933/10000) lo2543 hi2543=true := by decide +kernel
def bracket2543 : MeanBracket := meanBracketOfMoments (9933/10000) lo2543 hi2543 accepted2543
#print axioms bracket2528
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0158
