module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0432
public import BecknerOnofri.EntropyScalarCertificate.Bessel0433
public import BecknerOnofri.EntropyScalarCertificate.Bessel0434

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0173
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2768b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨32,by decide⟩
def lo2768b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨33,by decide⟩
def lo2768 : CheckedMoment :=
  CheckedMoment.ofBessel lo2768b1 lo2768b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2768b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨37,by decide⟩
def hi2768b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨38,by decide⟩
def hi2768 : CheckedMoment :=
  CheckedMoment.ofBessel hi2768b1 hi2768b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2768 : meanBracketCheck (2493/2500) lo2768 hi2768=true := by decide +kernel
def bracket2768 : MeanBracket := meanBracketOfMoments (2493/2500) lo2768 hi2768 accepted2768
def lo2769b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨42,by decide⟩
def lo2769b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨43,by decide⟩
def lo2769 : CheckedMoment :=
  CheckedMoment.ofBessel lo2769b1 lo2769b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2769b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨47,by decide⟩
def hi2769b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨48,by decide⟩
def hi2769 : CheckedMoment :=
  CheckedMoment.ofBessel hi2769b1 hi2769b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2769 : meanBracketCheck (199441/200000) lo2769 hi2769=true := by decide +kernel
def bracket2769 : MeanBracket := meanBracketOfMoments (199441/200000) lo2769 hi2769 accepted2769
def lo2770b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨52,by decide⟩
def lo2770b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨53,by decide⟩
def lo2770 : CheckedMoment :=
  CheckedMoment.ofBessel lo2770b1 lo2770b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2770b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨57,by decide⟩
def hi2770b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨58,by decide⟩
def hi2770 : CheckedMoment :=
  CheckedMoment.ofBessel hi2770b1 hi2770b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2770 : meanBracketCheck (99721/100000) lo2770 hi2770=true := by decide +kernel
def bracket2770 : MeanBracket := meanBracketOfMoments (99721/100000) lo2770 hi2770 accepted2770
def lo2771b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨62,by decide⟩
def lo2771b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨63,by decide⟩
def lo2771 : CheckedMoment :=
  CheckedMoment.ofBessel lo2771b1 lo2771b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2771b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨3,by decide⟩
def hi2771b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨4,by decide⟩
def hi2771 : CheckedMoment :=
  CheckedMoment.ofBessel hi2771b1 hi2771b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2771 : meanBracketCheck (199443/200000) lo2771 hi2771=true := by decide +kernel
def bracket2771 : MeanBracket := meanBracketOfMoments (199443/200000) lo2771 hi2771 accepted2771
def lo2772b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨8,by decide⟩
def lo2772b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨9,by decide⟩
def lo2772 : CheckedMoment :=
  CheckedMoment.ofBessel lo2772b1 lo2772b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2772b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨13,by decide⟩
def hi2772b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨14,by decide⟩
def hi2772 : CheckedMoment :=
  CheckedMoment.ofBessel hi2772b1 hi2772b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2772 : meanBracketCheck (49861/50000) lo2772 hi2772=true := by decide +kernel
def bracket2772 : MeanBracket := meanBracketOfMoments (49861/50000) lo2772 hi2772 accepted2772
def lo2773b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨18,by decide⟩
def lo2773b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨19,by decide⟩
def lo2773 : CheckedMoment :=
  CheckedMoment.ofBessel lo2773b1 lo2773b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2773b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨23,by decide⟩
def hi2773b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨24,by decide⟩
def hi2773 : CheckedMoment :=
  CheckedMoment.ofBessel hi2773b1 hi2773b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2773 : meanBracketCheck (39889/40000) lo2773 hi2773=true := by decide +kernel
def bracket2773 : MeanBracket := meanBracketOfMoments (39889/40000) lo2773 hi2773 accepted2773
def lo2774b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨28,by decide⟩
def lo2774b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨29,by decide⟩
def lo2774 : CheckedMoment :=
  CheckedMoment.ofBessel lo2774b1 lo2774b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2774b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨33,by decide⟩
def hi2774b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨34,by decide⟩
def hi2774 : CheckedMoment :=
  CheckedMoment.ofBessel hi2774b1 hi2774b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2774 : meanBracketCheck (99723/100000) lo2774 hi2774=true := by decide +kernel
def bracket2774 : MeanBracket := meanBracketOfMoments (99723/100000) lo2774 hi2774 accepted2774
def lo2775b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨38,by decide⟩
def lo2775b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨39,by decide⟩
def lo2775 : CheckedMoment :=
  CheckedMoment.ofBessel lo2775b1 lo2775b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2775b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨43,by decide⟩
def hi2775b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨44,by decide⟩
def hi2775 : CheckedMoment :=
  CheckedMoment.ofBessel hi2775b1 hi2775b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2775 : meanBracketCheck (199447/200000) lo2775 hi2775=true := by decide +kernel
def bracket2775 : MeanBracket := meanBracketOfMoments (199447/200000) lo2775 hi2775 accepted2775
def lo2776b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨48,by decide⟩
def lo2776b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨49,by decide⟩
def lo2776 : CheckedMoment :=
  CheckedMoment.ofBessel lo2776b1 lo2776b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2776b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨53,by decide⟩
def hi2776b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨54,by decide⟩
def hi2776 : CheckedMoment :=
  CheckedMoment.ofBessel hi2776b1 hi2776b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2776 : meanBracketCheck (24931/25000) lo2776 hi2776=true := by decide +kernel
def bracket2776 : MeanBracket := meanBracketOfMoments (24931/25000) lo2776 hi2776 accepted2776
def lo2777b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨58,by decide⟩
def lo2777b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨59,by decide⟩
def lo2777 : CheckedMoment :=
  CheckedMoment.ofBessel lo2777b1 lo2777b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2777b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨63,by decide⟩
def hi2777b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨0,by decide⟩
def hi2777 : CheckedMoment :=
  CheckedMoment.ofBessel hi2777b1 hi2777b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2777 : meanBracketCheck (199449/200000) lo2777 hi2777=true := by decide +kernel
def bracket2777 : MeanBracket := meanBracketOfMoments (199449/200000) lo2777 hi2777 accepted2777
def lo2778b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨4,by decide⟩
def lo2778b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨5,by decide⟩
def lo2778 : CheckedMoment :=
  CheckedMoment.ofBessel lo2778b1 lo2778b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2778b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨9,by decide⟩
def hi2778b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨10,by decide⟩
def hi2778 : CheckedMoment :=
  CheckedMoment.ofBessel hi2778b1 hi2778b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2778 : meanBracketCheck (3989/4000) lo2778 hi2778=true := by decide +kernel
def bracket2778 : MeanBracket := meanBracketOfMoments (3989/4000) lo2778 hi2778 accepted2778
def lo2779b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨14,by decide⟩
def lo2779b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨15,by decide⟩
def lo2779 : CheckedMoment :=
  CheckedMoment.ofBessel lo2779b1 lo2779b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2779b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨19,by decide⟩
def hi2779b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨20,by decide⟩
def hi2779 : CheckedMoment :=
  CheckedMoment.ofBessel hi2779b1 hi2779b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2779 : meanBracketCheck (199451/200000) lo2779 hi2779=true := by decide +kernel
def bracket2779 : MeanBracket := meanBracketOfMoments (199451/200000) lo2779 hi2779 accepted2779
def lo2780b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨24,by decide⟩
def lo2780b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨25,by decide⟩
def lo2780 : CheckedMoment :=
  CheckedMoment.ofBessel lo2780b1 lo2780b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2780b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨29,by decide⟩
def hi2780b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨30,by decide⟩
def hi2780 : CheckedMoment :=
  CheckedMoment.ofBessel hi2780b1 hi2780b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2780 : meanBracketCheck (49863/50000) lo2780 hi2780=true := by decide +kernel
def bracket2780 : MeanBracket := meanBracketOfMoments (49863/50000) lo2780 hi2780 accepted2780
def lo2781b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨34,by decide⟩
def lo2781b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨35,by decide⟩
def lo2781 : CheckedMoment :=
  CheckedMoment.ofBessel lo2781b1 lo2781b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2781b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨39,by decide⟩
def hi2781b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨40,by decide⟩
def hi2781 : CheckedMoment :=
  CheckedMoment.ofBessel hi2781b1 hi2781b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2781 : meanBracketCheck (199453/200000) lo2781 hi2781=true := by decide +kernel
def bracket2781 : MeanBracket := meanBracketOfMoments (199453/200000) lo2781 hi2781 accepted2781
def lo2782b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨44,by decide⟩
def lo2782b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨45,by decide⟩
def lo2782 : CheckedMoment :=
  CheckedMoment.ofBessel lo2782b1 lo2782b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2782b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨49,by decide⟩
def hi2782b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨50,by decide⟩
def hi2782 : CheckedMoment :=
  CheckedMoment.ofBessel hi2782b1 hi2782b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2782 : meanBracketCheck (99727/100000) lo2782 hi2782=true := by decide +kernel
def bracket2782 : MeanBracket := meanBracketOfMoments (99727/100000) lo2782 hi2782 accepted2782
def lo2783b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨54,by decide⟩
def lo2783b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨55,by decide⟩
def lo2783 : CheckedMoment :=
  CheckedMoment.ofBessel lo2783b1 lo2783b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2783b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨59,by decide⟩
def hi2783b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨60,by decide⟩
def hi2783 : CheckedMoment :=
  CheckedMoment.ofBessel hi2783b1 hi2783b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2783 : meanBracketCheck (39891/40000) lo2783 hi2783=true := by decide +kernel
def bracket2783 : MeanBracket := meanBracketOfMoments (39891/40000) lo2783 hi2783 accepted2783
#print axioms bracket2768
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0173
