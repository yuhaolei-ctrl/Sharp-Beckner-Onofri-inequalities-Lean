module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0407
public import BecknerOnofri.EntropyScalarCertificate.Bessel0408
public import BecknerOnofri.EntropyScalarCertificate.Bessel0409

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0163
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2608b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨32,by decide⟩
def lo2608b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨33,by decide⟩
def lo2608 : CheckedMoment :=
  CheckedMoment.ofBessel lo2608b1 lo2608b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2608b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨37,by decide⟩
def hi2608b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨38,by decide⟩
def hi2608 : CheckedMoment :=
  CheckedMoment.ofBessel hi2608b1 hi2608b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2608 : meanBracketCheck (4973/5000) lo2608 hi2608=true := by decide +kernel
def bracket2608 : MeanBracket := meanBracketOfMoments (4973/5000) lo2608 hi2608 accepted2608
def lo2609b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨42,by decide⟩
def lo2609b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨43,by decide⟩
def lo2609 : CheckedMoment :=
  CheckedMoment.ofBessel lo2609b1 lo2609b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2609b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨47,by decide⟩
def hi2609b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨48,by decide⟩
def hi2609 : CheckedMoment :=
  CheckedMoment.ofBessel hi2609b1 hi2609b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2609 : meanBracketCheck (49731/50000) lo2609 hi2609=true := by decide +kernel
def bracket2609 : MeanBracket := meanBracketOfMoments (49731/50000) lo2609 hi2609 accepted2609
def lo2610b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨52,by decide⟩
def lo2610b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨53,by decide⟩
def lo2610 : CheckedMoment :=
  CheckedMoment.ofBessel lo2610b1 lo2610b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2610b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨57,by decide⟩
def hi2610b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨58,by decide⟩
def hi2610 : CheckedMoment :=
  CheckedMoment.ofBessel hi2610b1 hi2610b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2610 : meanBracketCheck (12433/12500) lo2610 hi2610=true := by decide +kernel
def bracket2610 : MeanBracket := meanBracketOfMoments (12433/12500) lo2610 hi2610 accepted2610
def lo2611b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨62,by decide⟩
def lo2611b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨63,by decide⟩
def lo2611 : CheckedMoment :=
  CheckedMoment.ofBessel lo2611b1 lo2611b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2611b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨3,by decide⟩
def hi2611b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨4,by decide⟩
def hi2611 : CheckedMoment :=
  CheckedMoment.ofBessel hi2611b1 hi2611b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2611 : meanBracketCheck (49733/50000) lo2611 hi2611=true := by decide +kernel
def bracket2611 : MeanBracket := meanBracketOfMoments (49733/50000) lo2611 hi2611 accepted2611
def lo2612b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨8,by decide⟩
def lo2612b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨9,by decide⟩
def lo2612 : CheckedMoment :=
  CheckedMoment.ofBessel lo2612b1 lo2612b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2612b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨13,by decide⟩
def hi2612b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨14,by decide⟩
def hi2612 : CheckedMoment :=
  CheckedMoment.ofBessel hi2612b1 hi2612b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2612 : meanBracketCheck (24867/25000) lo2612 hi2612=true := by decide +kernel
def bracket2612 : MeanBracket := meanBracketOfMoments (24867/25000) lo2612 hi2612 accepted2612
def lo2613b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨18,by decide⟩
def lo2613b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨19,by decide⟩
def lo2613 : CheckedMoment :=
  CheckedMoment.ofBessel lo2613b1 lo2613b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2613b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨23,by decide⟩
def hi2613b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨24,by decide⟩
def hi2613 : CheckedMoment :=
  CheckedMoment.ofBessel hi2613b1 hi2613b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2613 : meanBracketCheck (9947/10000) lo2613 hi2613=true := by decide +kernel
def bracket2613 : MeanBracket := meanBracketOfMoments (9947/10000) lo2613 hi2613 accepted2613
def lo2614b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨28,by decide⟩
def lo2614b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨29,by decide⟩
def lo2614 : CheckedMoment :=
  CheckedMoment.ofBessel lo2614b1 lo2614b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2614b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨33,by decide⟩
def hi2614b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨34,by decide⟩
def hi2614 : CheckedMoment :=
  CheckedMoment.ofBessel hi2614b1 hi2614b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2614 : meanBracketCheck (6217/6250) lo2614 hi2614=true := by decide +kernel
def bracket2614 : MeanBracket := meanBracketOfMoments (6217/6250) lo2614 hi2614 accepted2614
def lo2615b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨38,by decide⟩
def lo2615b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨39,by decide⟩
def lo2615 : CheckedMoment :=
  CheckedMoment.ofBessel lo2615b1 lo2615b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2615b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨43,by decide⟩
def hi2615b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨44,by decide⟩
def hi2615 : CheckedMoment :=
  CheckedMoment.ofBessel hi2615b1 hi2615b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2615 : meanBracketCheck (49737/50000) lo2615 hi2615=true := by decide +kernel
def bracket2615 : MeanBracket := meanBracketOfMoments (49737/50000) lo2615 hi2615 accepted2615
def lo2616b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨48,by decide⟩
def lo2616b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨49,by decide⟩
def lo2616 : CheckedMoment :=
  CheckedMoment.ofBessel lo2616b1 lo2616b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2616b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨53,by decide⟩
def hi2616b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨54,by decide⟩
def hi2616 : CheckedMoment :=
  CheckedMoment.ofBessel hi2616b1 hi2616b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2616 : meanBracketCheck (24869/25000) lo2616 hi2616=true := by decide +kernel
def bracket2616 : MeanBracket := meanBracketOfMoments (24869/25000) lo2616 hi2616 accepted2616
def lo2617b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨58,by decide⟩
def lo2617b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨59,by decide⟩
def lo2617 : CheckedMoment :=
  CheckedMoment.ofBessel lo2617b1 lo2617b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2617b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨63,by decide⟩
def hi2617b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨0,by decide⟩
def hi2617 : CheckedMoment :=
  CheckedMoment.ofBessel hi2617b1 hi2617b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2617 : meanBracketCheck (49739/50000) lo2617 hi2617=true := by decide +kernel
def bracket2617 : MeanBracket := meanBracketOfMoments (49739/50000) lo2617 hi2617 accepted2617
def lo2618b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨4,by decide⟩
def lo2618b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨5,by decide⟩
def lo2618 : CheckedMoment :=
  CheckedMoment.ofBessel lo2618b1 lo2618b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2618b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨9,by decide⟩
def hi2618b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨10,by decide⟩
def hi2618 : CheckedMoment :=
  CheckedMoment.ofBessel hi2618b1 hi2618b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2618 : meanBracketCheck (2487/2500) lo2618 hi2618=true := by decide +kernel
def bracket2618 : MeanBracket := meanBracketOfMoments (2487/2500) lo2618 hi2618 accepted2618
def lo2619b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨14,by decide⟩
def lo2619b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨15,by decide⟩
def lo2619 : CheckedMoment :=
  CheckedMoment.ofBessel lo2619b1 lo2619b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2619b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨19,by decide⟩
def hi2619b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨20,by decide⟩
def hi2619 : CheckedMoment :=
  CheckedMoment.ofBessel hi2619b1 hi2619b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2619 : meanBracketCheck (49741/50000) lo2619 hi2619=true := by decide +kernel
def bracket2619 : MeanBracket := meanBracketOfMoments (49741/50000) lo2619 hi2619 accepted2619
def lo2620b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨24,by decide⟩
def lo2620b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨25,by decide⟩
def lo2620 : CheckedMoment :=
  CheckedMoment.ofBessel lo2620b1 lo2620b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2620b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨29,by decide⟩
def hi2620b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨30,by decide⟩
def hi2620 : CheckedMoment :=
  CheckedMoment.ofBessel hi2620b1 hi2620b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2620 : meanBracketCheck (24871/25000) lo2620 hi2620=true := by decide +kernel
def bracket2620 : MeanBracket := meanBracketOfMoments (24871/25000) lo2620 hi2620 accepted2620
def lo2621b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨34,by decide⟩
def lo2621b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨35,by decide⟩
def lo2621 : CheckedMoment :=
  CheckedMoment.ofBessel lo2621b1 lo2621b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2621b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨39,by decide⟩
def hi2621b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨40,by decide⟩
def hi2621 : CheckedMoment :=
  CheckedMoment.ofBessel hi2621b1 hi2621b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2621 : meanBracketCheck (49743/50000) lo2621 hi2621=true := by decide +kernel
def bracket2621 : MeanBracket := meanBracketOfMoments (49743/50000) lo2621 hi2621 accepted2621
def lo2622b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨44,by decide⟩
def lo2622b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨45,by decide⟩
def lo2622 : CheckedMoment :=
  CheckedMoment.ofBessel lo2622b1 lo2622b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2622b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨49,by decide⟩
def hi2622b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨50,by decide⟩
def hi2622 : CheckedMoment :=
  CheckedMoment.ofBessel hi2622b1 hi2622b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2622 : meanBracketCheck (3109/3125) lo2622 hi2622=true := by decide +kernel
def bracket2622 : MeanBracket := meanBracketOfMoments (3109/3125) lo2622 hi2622 accepted2622
def lo2623b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨54,by decide⟩
def lo2623b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨55,by decide⟩
def lo2623 : CheckedMoment :=
  CheckedMoment.ofBessel lo2623b1 lo2623b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2623b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨59,by decide⟩
def hi2623b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨60,by decide⟩
def hi2623 : CheckedMoment :=
  CheckedMoment.ofBessel hi2623b1 hi2623b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2623 : meanBracketCheck (9949/10000) lo2623 hi2623=true := by decide +kernel
def bracket2623 : MeanBracket := meanBracketOfMoments (9949/10000) lo2623 hi2623 accepted2623
#print axioms bracket2608
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0163
