module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0405
public import BecknerOnofri.EntropyScalarCertificate.Bessel0406
public import BecknerOnofri.EntropyScalarCertificate.Bessel0407

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0162
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2592b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨0,by decide⟩
def lo2592b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨1,by decide⟩
def lo2592 : CheckedMoment :=
  CheckedMoment.ofBessel lo2592b1 lo2592b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2592b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨5,by decide⟩
def hi2592b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨6,by decide⟩
def hi2592 : CheckedMoment :=
  CheckedMoment.ofBessel hi2592b1 hi2592b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2592 : meanBracketCheck (24857/25000) lo2592 hi2592=true := by decide +kernel
def bracket2592 : MeanBracket := meanBracketOfMoments (24857/25000) lo2592 hi2592 accepted2592
def lo2593b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨10,by decide⟩
def lo2593b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨11,by decide⟩
def lo2593 : CheckedMoment :=
  CheckedMoment.ofBessel lo2593b1 lo2593b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2593b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨15,by decide⟩
def hi2593b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨16,by decide⟩
def hi2593 : CheckedMoment :=
  CheckedMoment.ofBessel hi2593b1 hi2593b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2593 : meanBracketCheck (9943/10000) lo2593 hi2593=true := by decide +kernel
def bracket2593 : MeanBracket := meanBracketOfMoments (9943/10000) lo2593 hi2593 accepted2593
def lo2594b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨20,by decide⟩
def lo2594b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨21,by decide⟩
def lo2594 : CheckedMoment :=
  CheckedMoment.ofBessel lo2594b1 lo2594b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2594b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨25,by decide⟩
def hi2594b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨26,by decide⟩
def hi2594 : CheckedMoment :=
  CheckedMoment.ofBessel hi2594b1 hi2594b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2594 : meanBracketCheck (12429/12500) lo2594 hi2594=true := by decide +kernel
def bracket2594 : MeanBracket := meanBracketOfMoments (12429/12500) lo2594 hi2594 accepted2594
def lo2595b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨30,by decide⟩
def lo2595b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨31,by decide⟩
def lo2595 : CheckedMoment :=
  CheckedMoment.ofBessel lo2595b1 lo2595b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2595b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨35,by decide⟩
def hi2595b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨36,by decide⟩
def hi2595 : CheckedMoment :=
  CheckedMoment.ofBessel hi2595b1 hi2595b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2595 : meanBracketCheck (49717/50000) lo2595 hi2595=true := by decide +kernel
def bracket2595 : MeanBracket := meanBracketOfMoments (49717/50000) lo2595 hi2595 accepted2595
def lo2596b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨40,by decide⟩
def lo2596b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨41,by decide⟩
def lo2596 : CheckedMoment :=
  CheckedMoment.ofBessel lo2596b1 lo2596b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2596b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨45,by decide⟩
def hi2596b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨46,by decide⟩
def hi2596 : CheckedMoment :=
  CheckedMoment.ofBessel hi2596b1 hi2596b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2596 : meanBracketCheck (24859/25000) lo2596 hi2596=true := by decide +kernel
def bracket2596 : MeanBracket := meanBracketOfMoments (24859/25000) lo2596 hi2596 accepted2596
def lo2597b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨50,by decide⟩
def lo2597b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨51,by decide⟩
def lo2597 : CheckedMoment :=
  CheckedMoment.ofBessel lo2597b1 lo2597b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2597b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨55,by decide⟩
def hi2597b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨56,by decide⟩
def hi2597 : CheckedMoment :=
  CheckedMoment.ofBessel hi2597b1 hi2597b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2597 : meanBracketCheck (49719/50000) lo2597 hi2597=true := by decide +kernel
def bracket2597 : MeanBracket := meanBracketOfMoments (49719/50000) lo2597 hi2597 accepted2597
def lo2598b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨60,by decide⟩
def lo2598b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨61,by decide⟩
def lo2598 : CheckedMoment :=
  CheckedMoment.ofBessel lo2598b1 lo2598b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2598b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨1,by decide⟩
def hi2598b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨2,by decide⟩
def hi2598 : CheckedMoment :=
  CheckedMoment.ofBessel hi2598b1 hi2598b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2598 : meanBracketCheck (1243/1250) lo2598 hi2598=true := by decide +kernel
def bracket2598 : MeanBracket := meanBracketOfMoments (1243/1250) lo2598 hi2598 accepted2598
def lo2599b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨6,by decide⟩
def lo2599b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨7,by decide⟩
def lo2599 : CheckedMoment :=
  CheckedMoment.ofBessel lo2599b1 lo2599b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2599b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨11,by decide⟩
def hi2599b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨12,by decide⟩
def hi2599 : CheckedMoment :=
  CheckedMoment.ofBessel hi2599b1 hi2599b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2599 : meanBracketCheck (49721/50000) lo2599 hi2599=true := by decide +kernel
def bracket2599 : MeanBracket := meanBracketOfMoments (49721/50000) lo2599 hi2599 accepted2599
def lo2600b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨16,by decide⟩
def lo2600b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨17,by decide⟩
def lo2600 : CheckedMoment :=
  CheckedMoment.ofBessel lo2600b1 lo2600b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2600b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨21,by decide⟩
def hi2600b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨22,by decide⟩
def hi2600 : CheckedMoment :=
  CheckedMoment.ofBessel hi2600b1 hi2600b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2600 : meanBracketCheck (24861/25000) lo2600 hi2600=true := by decide +kernel
def bracket2600 : MeanBracket := meanBracketOfMoments (24861/25000) lo2600 hi2600 accepted2600
def lo2601b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨26,by decide⟩
def lo2601b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨27,by decide⟩
def lo2601 : CheckedMoment :=
  CheckedMoment.ofBessel lo2601b1 lo2601b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2601b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨31,by decide⟩
def hi2601b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨32,by decide⟩
def hi2601 : CheckedMoment :=
  CheckedMoment.ofBessel hi2601b1 hi2601b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2601 : meanBracketCheck (49723/50000) lo2601 hi2601=true := by decide +kernel
def bracket2601 : MeanBracket := meanBracketOfMoments (49723/50000) lo2601 hi2601 accepted2601
def lo2602b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨36,by decide⟩
def lo2602b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨37,by decide⟩
def lo2602 : CheckedMoment :=
  CheckedMoment.ofBessel lo2602b1 lo2602b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2602b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨41,by decide⟩
def hi2602b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨42,by decide⟩
def hi2602 : CheckedMoment :=
  CheckedMoment.ofBessel hi2602b1 hi2602b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2602 : meanBracketCheck (12431/12500) lo2602 hi2602=true := by decide +kernel
def bracket2602 : MeanBracket := meanBracketOfMoments (12431/12500) lo2602 hi2602 accepted2602
def lo2603b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨46,by decide⟩
def lo2603b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨47,by decide⟩
def lo2603 : CheckedMoment :=
  CheckedMoment.ofBessel lo2603b1 lo2603b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2603b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨51,by decide⟩
def hi2603b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨52,by decide⟩
def hi2603 : CheckedMoment :=
  CheckedMoment.ofBessel hi2603b1 hi2603b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2603 : meanBracketCheck (1989/2000) lo2603 hi2603=true := by decide +kernel
def bracket2603 : MeanBracket := meanBracketOfMoments (1989/2000) lo2603 hi2603 accepted2603
def lo2604b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨56,by decide⟩
def lo2604b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨57,by decide⟩
def lo2604 : CheckedMoment :=
  CheckedMoment.ofBessel lo2604b1 lo2604b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2604b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨61,by decide⟩
def hi2604b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨62,by decide⟩
def hi2604 : CheckedMoment :=
  CheckedMoment.ofBessel hi2604b1 hi2604b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2604 : meanBracketCheck (24863/25000) lo2604 hi2604=true := by decide +kernel
def bracket2604 : MeanBracket := meanBracketOfMoments (24863/25000) lo2604 hi2604 accepted2604
def lo2605b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨2,by decide⟩
def lo2605b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨3,by decide⟩
def lo2605 : CheckedMoment :=
  CheckedMoment.ofBessel lo2605b1 lo2605b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2605b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨7,by decide⟩
def hi2605b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨8,by decide⟩
def hi2605 : CheckedMoment :=
  CheckedMoment.ofBessel hi2605b1 hi2605b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2605 : meanBracketCheck (49727/50000) lo2605 hi2605=true := by decide +kernel
def bracket2605 : MeanBracket := meanBracketOfMoments (49727/50000) lo2605 hi2605 accepted2605
def lo2606b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨12,by decide⟩
def lo2606b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨13,by decide⟩
def lo2606 : CheckedMoment :=
  CheckedMoment.ofBessel lo2606b1 lo2606b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2606b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨17,by decide⟩
def hi2606b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨18,by decide⟩
def hi2606 : CheckedMoment :=
  CheckedMoment.ofBessel hi2606b1 hi2606b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2606 : meanBracketCheck (3108/3125) lo2606 hi2606=true := by decide +kernel
def bracket2606 : MeanBracket := meanBracketOfMoments (3108/3125) lo2606 hi2606 accepted2606
def lo2607b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨22,by decide⟩
def lo2607b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨23,by decide⟩
def lo2607 : CheckedMoment :=
  CheckedMoment.ofBessel lo2607b1 lo2607b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2607b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨27,by decide⟩
def hi2607b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨28,by decide⟩
def hi2607 : CheckedMoment :=
  CheckedMoment.ofBessel hi2607b1 hi2607b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2607 : meanBracketCheck (49729/50000) lo2607 hi2607=true := by decide +kernel
def bracket2607 : MeanBracket := meanBracketOfMoments (49729/50000) lo2607 hi2607 accepted2607
#print axioms bracket2592
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0162
