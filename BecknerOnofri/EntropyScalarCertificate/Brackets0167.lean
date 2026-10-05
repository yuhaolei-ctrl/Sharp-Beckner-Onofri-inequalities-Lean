module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0417
public import BecknerOnofri.EntropyScalarCertificate.Bessel0418
public import BecknerOnofri.EntropyScalarCertificate.Bessel0419

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0167
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2672b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨32,by decide⟩
def lo2672b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨33,by decide⟩
def lo2672 : CheckedMoment :=
  CheckedMoment.ofBessel lo2672b1 lo2672b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2672b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨37,by decide⟩
def hi2672b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨38,by decide⟩
def hi2672 : CheckedMoment :=
  CheckedMoment.ofBessel hi2672b1 hi2672b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2672 : meanBracketCheck (24897/25000) lo2672 hi2672=true := by decide +kernel
def bracket2672 : MeanBracket := meanBracketOfMoments (24897/25000) lo2672 hi2672 accepted2672
def lo2673b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨42,by decide⟩
def lo2673b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨43,by decide⟩
def lo2673 : CheckedMoment :=
  CheckedMoment.ofBessel lo2673b1 lo2673b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2673b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨47,by decide⟩
def hi2673b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨48,by decide⟩
def hi2673 : CheckedMoment :=
  CheckedMoment.ofBessel hi2673b1 hi2673b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2673 : meanBracketCheck (9959/10000) lo2673 hi2673=true := by decide +kernel
def bracket2673 : MeanBracket := meanBracketOfMoments (9959/10000) lo2673 hi2673 accepted2673
def lo2674b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨52,by decide⟩
def lo2674b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨53,by decide⟩
def lo2674 : CheckedMoment :=
  CheckedMoment.ofBessel lo2674b1 lo2674b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2674b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨57,by decide⟩
def hi2674b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨58,by decide⟩
def hi2674 : CheckedMoment :=
  CheckedMoment.ofBessel hi2674b1 hi2674b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2674 : meanBracketCheck (12449/12500) lo2674 hi2674=true := by decide +kernel
def bracket2674 : MeanBracket := meanBracketOfMoments (12449/12500) lo2674 hi2674 accepted2674
def lo2675b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨62,by decide⟩
def lo2675b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨63,by decide⟩
def lo2675 : CheckedMoment :=
  CheckedMoment.ofBessel lo2675b1 lo2675b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2675b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨3,by decide⟩
def hi2675b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨4,by decide⟩
def hi2675 : CheckedMoment :=
  CheckedMoment.ofBessel hi2675b1 hi2675b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2675 : meanBracketCheck (49797/50000) lo2675 hi2675=true := by decide +kernel
def bracket2675 : MeanBracket := meanBracketOfMoments (49797/50000) lo2675 hi2675 accepted2675
def lo2676b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨8,by decide⟩
def lo2676b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨9,by decide⟩
def lo2676 : CheckedMoment :=
  CheckedMoment.ofBessel lo2676b1 lo2676b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2676b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨13,by decide⟩
def hi2676b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨14,by decide⟩
def hi2676 : CheckedMoment :=
  CheckedMoment.ofBessel hi2676b1 hi2676b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2676 : meanBracketCheck (24899/25000) lo2676 hi2676=true := by decide +kernel
def bracket2676 : MeanBracket := meanBracketOfMoments (24899/25000) lo2676 hi2676 accepted2676
def lo2677b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨18,by decide⟩
def lo2677b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨19,by decide⟩
def lo2677 : CheckedMoment :=
  CheckedMoment.ofBessel lo2677b1 lo2677b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2677b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨23,by decide⟩
def hi2677b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨24,by decide⟩
def hi2677 : CheckedMoment :=
  CheckedMoment.ofBessel hi2677b1 hi2677b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2677 : meanBracketCheck (49799/50000) lo2677 hi2677=true := by decide +kernel
def bracket2677 : MeanBracket := meanBracketOfMoments (49799/50000) lo2677 hi2677 accepted2677
def lo2678b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨28,by decide⟩
def lo2678b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨29,by decide⟩
def lo2678 : CheckedMoment :=
  CheckedMoment.ofBessel lo2678b1 lo2678b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2678b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨33,by decide⟩
def hi2678b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨34,by decide⟩
def hi2678 : CheckedMoment :=
  CheckedMoment.ofBessel hi2678b1 hi2678b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2678 : meanBracketCheck (249/250) lo2678 hi2678=true := by decide +kernel
def bracket2678 : MeanBracket := meanBracketOfMoments (249/250) lo2678 hi2678 accepted2678
def lo2679b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨38,by decide⟩
def lo2679b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨39,by decide⟩
def lo2679 : CheckedMoment :=
  CheckedMoment.ofBessel lo2679b1 lo2679b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2679b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨43,by decide⟩
def hi2679b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨44,by decide⟩
def hi2679 : CheckedMoment :=
  CheckedMoment.ofBessel hi2679b1 hi2679b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2679 : meanBracketCheck (49801/50000) lo2679 hi2679=true := by decide +kernel
def bracket2679 : MeanBracket := meanBracketOfMoments (49801/50000) lo2679 hi2679 accepted2679
def lo2680b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨48,by decide⟩
def lo2680b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨49,by decide⟩
def lo2680 : CheckedMoment :=
  CheckedMoment.ofBessel lo2680b1 lo2680b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2680b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨53,by decide⟩
def hi2680b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨54,by decide⟩
def hi2680 : CheckedMoment :=
  CheckedMoment.ofBessel hi2680b1 hi2680b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2680 : meanBracketCheck (24901/25000) lo2680 hi2680=true := by decide +kernel
def bracket2680 : MeanBracket := meanBracketOfMoments (24901/25000) lo2680 hi2680 accepted2680
def lo2681b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨58,by decide⟩
def lo2681b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨59,by decide⟩
def lo2681 : CheckedMoment :=
  CheckedMoment.ofBessel lo2681b1 lo2681b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2681b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨63,by decide⟩
def hi2681b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨0,by decide⟩
def hi2681 : CheckedMoment :=
  CheckedMoment.ofBessel hi2681b1 hi2681b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2681 : meanBracketCheck (49803/50000) lo2681 hi2681=true := by decide +kernel
def bracket2681 : MeanBracket := meanBracketOfMoments (49803/50000) lo2681 hi2681 accepted2681
def lo2682b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨4,by decide⟩
def lo2682b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨5,by decide⟩
def lo2682 : CheckedMoment :=
  CheckedMoment.ofBessel lo2682b1 lo2682b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2682b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨9,by decide⟩
def hi2682b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨10,by decide⟩
def hi2682 : CheckedMoment :=
  CheckedMoment.ofBessel hi2682b1 hi2682b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2682 : meanBracketCheck (12451/12500) lo2682 hi2682=true := by decide +kernel
def bracket2682 : MeanBracket := meanBracketOfMoments (12451/12500) lo2682 hi2682 accepted2682
def lo2683b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨14,by decide⟩
def lo2683b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨15,by decide⟩
def lo2683 : CheckedMoment :=
  CheckedMoment.ofBessel lo2683b1 lo2683b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2683b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨19,by decide⟩
def hi2683b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨20,by decide⟩
def hi2683 : CheckedMoment :=
  CheckedMoment.ofBessel hi2683b1 hi2683b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2683 : meanBracketCheck (9961/10000) lo2683 hi2683=true := by decide +kernel
def bracket2683 : MeanBracket := meanBracketOfMoments (9961/10000) lo2683 hi2683 accepted2683
def lo2684b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨24,by decide⟩
def lo2684b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨25,by decide⟩
def lo2684 : CheckedMoment :=
  CheckedMoment.ofBessel lo2684b1 lo2684b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2684b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨29,by decide⟩
def hi2684b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨30,by decide⟩
def hi2684 : CheckedMoment :=
  CheckedMoment.ofBessel hi2684b1 hi2684b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2684 : meanBracketCheck (24903/25000) lo2684 hi2684=true := by decide +kernel
def bracket2684 : MeanBracket := meanBracketOfMoments (24903/25000) lo2684 hi2684 accepted2684
def lo2685b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨34,by decide⟩
def lo2685b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨35,by decide⟩
def lo2685 : CheckedMoment :=
  CheckedMoment.ofBessel lo2685b1 lo2685b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2685b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨39,by decide⟩
def hi2685b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨40,by decide⟩
def hi2685 : CheckedMoment :=
  CheckedMoment.ofBessel hi2685b1 hi2685b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2685 : meanBracketCheck (49807/50000) lo2685 hi2685=true := by decide +kernel
def bracket2685 : MeanBracket := meanBracketOfMoments (49807/50000) lo2685 hi2685 accepted2685
def lo2686b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨44,by decide⟩
def lo2686b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨45,by decide⟩
def lo2686 : CheckedMoment :=
  CheckedMoment.ofBessel lo2686b1 lo2686b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2686b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨49,by decide⟩
def hi2686b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨50,by decide⟩
def hi2686 : CheckedMoment :=
  CheckedMoment.ofBessel hi2686b1 hi2686b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2686 : meanBracketCheck (3113/3125) lo2686 hi2686=true := by decide +kernel
def bracket2686 : MeanBracket := meanBracketOfMoments (3113/3125) lo2686 hi2686 accepted2686
def lo2687b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨54,by decide⟩
def lo2687b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨55,by decide⟩
def lo2687 : CheckedMoment :=
  CheckedMoment.ofBessel lo2687b1 lo2687b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2687b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨59,by decide⟩
def hi2687b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨60,by decide⟩
def hi2687 : CheckedMoment :=
  CheckedMoment.ofBessel hi2687b1 hi2687b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2687 : meanBracketCheck (49809/50000) lo2687 hi2687=true := by decide +kernel
def bracket2687 : MeanBracket := meanBracketOfMoments (49809/50000) lo2687 hi2687 accepted2687
#print axioms bracket2672
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0167
