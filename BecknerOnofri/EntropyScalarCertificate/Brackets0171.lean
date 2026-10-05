module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0427
public import BecknerOnofri.EntropyScalarCertificate.Bessel0428
public import BecknerOnofri.EntropyScalarCertificate.Bessel0429

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0171
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2736b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨32,by decide⟩
def lo2736b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨33,by decide⟩
def lo2736 : CheckedMoment :=
  CheckedMoment.ofBessel lo2736b1 lo2736b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2736b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨37,by decide⟩
def hi2736b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨38,by decide⟩
def hi2736 : CheckedMoment :=
  CheckedMoment.ofBessel hi2736b1 hi2736b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2736 : meanBracketCheck (12463/12500) lo2736 hi2736=true := by decide +kernel
def bracket2736 : MeanBracket := meanBracketOfMoments (12463/12500) lo2736 hi2736 accepted2736
def lo2737b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨42,by decide⟩
def lo2737b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨43,by decide⟩
def lo2737 : CheckedMoment :=
  CheckedMoment.ofBessel lo2737b1 lo2737b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2737b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨47,by decide⟩
def hi2737b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨48,by decide⟩
def hi2737 : CheckedMoment :=
  CheckedMoment.ofBessel hi2737b1 hi2737b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2737 : meanBracketCheck (199409/200000) lo2737 hi2737=true := by decide +kernel
def bracket2737 : MeanBracket := meanBracketOfMoments (199409/200000) lo2737 hi2737 accepted2737
def lo2738b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨52,by decide⟩
def lo2738b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨53,by decide⟩
def lo2738 : CheckedMoment :=
  CheckedMoment.ofBessel lo2738b1 lo2738b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2738b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨57,by decide⟩
def hi2738b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨58,by decide⟩
def hi2738 : CheckedMoment :=
  CheckedMoment.ofBessel hi2738b1 hi2738b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2738 : meanBracketCheck (19941/20000) lo2738 hi2738=true := by decide +kernel
def bracket2738 : MeanBracket := meanBracketOfMoments (19941/20000) lo2738 hi2738 accepted2738
def lo2739b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨62,by decide⟩
def lo2739b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨63,by decide⟩
def lo2739 : CheckedMoment :=
  CheckedMoment.ofBessel lo2739b1 lo2739b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2739b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨3,by decide⟩
def hi2739b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨4,by decide⟩
def hi2739 : CheckedMoment :=
  CheckedMoment.ofBessel hi2739b1 hi2739b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2739 : meanBracketCheck (199411/200000) lo2739 hi2739=true := by decide +kernel
def bracket2739 : MeanBracket := meanBracketOfMoments (199411/200000) lo2739 hi2739 accepted2739
def lo2740b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨8,by decide⟩
def lo2740b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨9,by decide⟩
def lo2740 : CheckedMoment :=
  CheckedMoment.ofBessel lo2740b1 lo2740b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2740b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨13,by decide⟩
def hi2740b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨14,by decide⟩
def hi2740 : CheckedMoment :=
  CheckedMoment.ofBessel hi2740b1 hi2740b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2740 : meanBracketCheck (49853/50000) lo2740 hi2740=true := by decide +kernel
def bracket2740 : MeanBracket := meanBracketOfMoments (49853/50000) lo2740 hi2740 accepted2740
def lo2741b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨18,by decide⟩
def lo2741b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨19,by decide⟩
def lo2741 : CheckedMoment :=
  CheckedMoment.ofBessel lo2741b1 lo2741b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2741b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨23,by decide⟩
def hi2741b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨24,by decide⟩
def hi2741 : CheckedMoment :=
  CheckedMoment.ofBessel hi2741b1 hi2741b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2741 : meanBracketCheck (199413/200000) lo2741 hi2741=true := by decide +kernel
def bracket2741 : MeanBracket := meanBracketOfMoments (199413/200000) lo2741 hi2741 accepted2741
def lo2742b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨28,by decide⟩
def lo2742b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨29,by decide⟩
def lo2742 : CheckedMoment :=
  CheckedMoment.ofBessel lo2742b1 lo2742b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2742b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨33,by decide⟩
def hi2742b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨34,by decide⟩
def hi2742 : CheckedMoment :=
  CheckedMoment.ofBessel hi2742b1 hi2742b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2742 : meanBracketCheck (99707/100000) lo2742 hi2742=true := by decide +kernel
def bracket2742 : MeanBracket := meanBracketOfMoments (99707/100000) lo2742 hi2742 accepted2742
def lo2743b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨38,by decide⟩
def lo2743b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨39,by decide⟩
def lo2743 : CheckedMoment :=
  CheckedMoment.ofBessel lo2743b1 lo2743b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2743b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨43,by decide⟩
def hi2743b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨44,by decide⟩
def hi2743 : CheckedMoment :=
  CheckedMoment.ofBessel hi2743b1 hi2743b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2743 : meanBracketCheck (39883/40000) lo2743 hi2743=true := by decide +kernel
def bracket2743 : MeanBracket := meanBracketOfMoments (39883/40000) lo2743 hi2743 accepted2743
def lo2744b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨48,by decide⟩
def lo2744b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨49,by decide⟩
def lo2744 : CheckedMoment :=
  CheckedMoment.ofBessel lo2744b1 lo2744b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2744b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨53,by decide⟩
def hi2744b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨54,by decide⟩
def hi2744 : CheckedMoment :=
  CheckedMoment.ofBessel hi2744b1 hi2744b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2744 : meanBracketCheck (24927/25000) lo2744 hi2744=true := by decide +kernel
def bracket2744 : MeanBracket := meanBracketOfMoments (24927/25000) lo2744 hi2744 accepted2744
def lo2745b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨58,by decide⟩
def lo2745b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨59,by decide⟩
def lo2745 : CheckedMoment :=
  CheckedMoment.ofBessel lo2745b1 lo2745b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2745b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨63,by decide⟩
def hi2745b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨0,by decide⟩
def hi2745 : CheckedMoment :=
  CheckedMoment.ofBessel hi2745b1 hi2745b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2745 : meanBracketCheck (199417/200000) lo2745 hi2745=true := by decide +kernel
def bracket2745 : MeanBracket := meanBracketOfMoments (199417/200000) lo2745 hi2745 accepted2745
def lo2746b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨4,by decide⟩
def lo2746b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨5,by decide⟩
def lo2746 : CheckedMoment :=
  CheckedMoment.ofBessel lo2746b1 lo2746b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2746b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨9,by decide⟩
def hi2746b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨10,by decide⟩
def hi2746 : CheckedMoment :=
  CheckedMoment.ofBessel hi2746b1 hi2746b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2746 : meanBracketCheck (99709/100000) lo2746 hi2746=true := by decide +kernel
def bracket2746 : MeanBracket := meanBracketOfMoments (99709/100000) lo2746 hi2746 accepted2746
def lo2747b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨14,by decide⟩
def lo2747b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨15,by decide⟩
def lo2747 : CheckedMoment :=
  CheckedMoment.ofBessel lo2747b1 lo2747b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2747b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨19,by decide⟩
def hi2747b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨20,by decide⟩
def hi2747 : CheckedMoment :=
  CheckedMoment.ofBessel hi2747b1 hi2747b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2747 : meanBracketCheck (199419/200000) lo2747 hi2747=true := by decide +kernel
def bracket2747 : MeanBracket := meanBracketOfMoments (199419/200000) lo2747 hi2747 accepted2747
def lo2748b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨24,by decide⟩
def lo2748b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨25,by decide⟩
def lo2748 : CheckedMoment :=
  CheckedMoment.ofBessel lo2748b1 lo2748b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2748b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨29,by decide⟩
def hi2748b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨30,by decide⟩
def hi2748 : CheckedMoment :=
  CheckedMoment.ofBessel hi2748b1 hi2748b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2748 : meanBracketCheck (9971/10000) lo2748 hi2748=true := by decide +kernel
def bracket2748 : MeanBracket := meanBracketOfMoments (9971/10000) lo2748 hi2748 accepted2748
def lo2749b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨34,by decide⟩
def lo2749b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨35,by decide⟩
def lo2749 : CheckedMoment :=
  CheckedMoment.ofBessel lo2749b1 lo2749b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2749b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨39,by decide⟩
def hi2749b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨40,by decide⟩
def hi2749 : CheckedMoment :=
  CheckedMoment.ofBessel hi2749b1 hi2749b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2749 : meanBracketCheck (199421/200000) lo2749 hi2749=true := by decide +kernel
def bracket2749 : MeanBracket := meanBracketOfMoments (199421/200000) lo2749 hi2749 accepted2749
def lo2750b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨44,by decide⟩
def lo2750b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨45,by decide⟩
def lo2750 : CheckedMoment :=
  CheckedMoment.ofBessel lo2750b1 lo2750b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2750b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨49,by decide⟩
def hi2750b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨50,by decide⟩
def hi2750 : CheckedMoment :=
  CheckedMoment.ofBessel hi2750b1 hi2750b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2750 : meanBracketCheck (99711/100000) lo2750 hi2750=true := by decide +kernel
def bracket2750 : MeanBracket := meanBracketOfMoments (99711/100000) lo2750 hi2750 accepted2750
def lo2751b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨54,by decide⟩
def lo2751b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨55,by decide⟩
def lo2751 : CheckedMoment :=
  CheckedMoment.ofBessel lo2751b1 lo2751b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2751b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨59,by decide⟩
def hi2751b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨60,by decide⟩
def hi2751 : CheckedMoment :=
  CheckedMoment.ofBessel hi2751b1 hi2751b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2751 : meanBracketCheck (199423/200000) lo2751 hi2751=true := by decide +kernel
def bracket2751 : MeanBracket := meanBracketOfMoments (199423/200000) lo2751 hi2751 accepted2751
#print axioms bracket2736
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0171
