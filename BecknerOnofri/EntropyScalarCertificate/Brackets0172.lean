module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0430
public import BecknerOnofri.EntropyScalarCertificate.Bessel0431
public import BecknerOnofri.EntropyScalarCertificate.Bessel0432

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0172
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2752b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨0,by decide⟩
def lo2752b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨1,by decide⟩
def lo2752 : CheckedMoment :=
  CheckedMoment.ofBessel lo2752b1 lo2752b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2752b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨5,by decide⟩
def hi2752b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨6,by decide⟩
def hi2752 : CheckedMoment :=
  CheckedMoment.ofBessel hi2752b1 hi2752b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2752 : meanBracketCheck (3116/3125) lo2752 hi2752=true := by decide +kernel
def bracket2752 : MeanBracket := meanBracketOfMoments (3116/3125) lo2752 hi2752 accepted2752
def lo2753b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨10,by decide⟩
def lo2753b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨11,by decide⟩
def lo2753 : CheckedMoment :=
  CheckedMoment.ofBessel lo2753b1 lo2753b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2753b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨15,by decide⟩
def hi2753b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨16,by decide⟩
def hi2753 : CheckedMoment :=
  CheckedMoment.ofBessel hi2753b1 hi2753b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2753 : meanBracketCheck (7977/8000) lo2753 hi2753=true := by decide +kernel
def bracket2753 : MeanBracket := meanBracketOfMoments (7977/8000) lo2753 hi2753 accepted2753
def lo2754b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨20,by decide⟩
def lo2754b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨21,by decide⟩
def lo2754 : CheckedMoment :=
  CheckedMoment.ofBessel lo2754b1 lo2754b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2754b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨25,by decide⟩
def hi2754b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨26,by decide⟩
def hi2754 : CheckedMoment :=
  CheckedMoment.ofBessel hi2754b1 hi2754b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2754 : meanBracketCheck (99713/100000) lo2754 hi2754=true := by decide +kernel
def bracket2754 : MeanBracket := meanBracketOfMoments (99713/100000) lo2754 hi2754 accepted2754
def lo2755b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨30,by decide⟩
def lo2755b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨31,by decide⟩
def lo2755 : CheckedMoment :=
  CheckedMoment.ofBessel lo2755b1 lo2755b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2755b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨35,by decide⟩
def hi2755b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨36,by decide⟩
def hi2755 : CheckedMoment :=
  CheckedMoment.ofBessel hi2755b1 hi2755b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2755 : meanBracketCheck (199427/200000) lo2755 hi2755=true := by decide +kernel
def bracket2755 : MeanBracket := meanBracketOfMoments (199427/200000) lo2755 hi2755 accepted2755
def lo2756b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨40,by decide⟩
def lo2756b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨41,by decide⟩
def lo2756 : CheckedMoment :=
  CheckedMoment.ofBessel lo2756b1 lo2756b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2756b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨45,by decide⟩
def hi2756b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨46,by decide⟩
def hi2756 : CheckedMoment :=
  CheckedMoment.ofBessel hi2756b1 hi2756b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2756 : meanBracketCheck (49857/50000) lo2756 hi2756=true := by decide +kernel
def bracket2756 : MeanBracket := meanBracketOfMoments (49857/50000) lo2756 hi2756 accepted2756
def lo2757b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨50,by decide⟩
def lo2757b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨51,by decide⟩
def lo2757 : CheckedMoment :=
  CheckedMoment.ofBessel lo2757b1 lo2757b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2757b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨55,by decide⟩
def hi2757b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨56,by decide⟩
def hi2757 : CheckedMoment :=
  CheckedMoment.ofBessel hi2757b1 hi2757b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2757 : meanBracketCheck (199429/200000) lo2757 hi2757=true := by decide +kernel
def bracket2757 : MeanBracket := meanBracketOfMoments (199429/200000) lo2757 hi2757 accepted2757
def lo2758b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨60,by decide⟩
def lo2758b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨61,by decide⟩
def lo2758 : CheckedMoment :=
  CheckedMoment.ofBessel lo2758b1 lo2758b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2758b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨1,by decide⟩
def hi2758b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨2,by decide⟩
def hi2758 : CheckedMoment :=
  CheckedMoment.ofBessel hi2758b1 hi2758b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2758 : meanBracketCheck (19943/20000) lo2758 hi2758=true := by decide +kernel
def bracket2758 : MeanBracket := meanBracketOfMoments (19943/20000) lo2758 hi2758 accepted2758
def lo2759b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨6,by decide⟩
def lo2759b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨7,by decide⟩
def lo2759 : CheckedMoment :=
  CheckedMoment.ofBessel lo2759b1 lo2759b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2759b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨11,by decide⟩
def hi2759b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨12,by decide⟩
def hi2759 : CheckedMoment :=
  CheckedMoment.ofBessel hi2759b1 hi2759b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2759 : meanBracketCheck (199431/200000) lo2759 hi2759=true := by decide +kernel
def bracket2759 : MeanBracket := meanBracketOfMoments (199431/200000) lo2759 hi2759 accepted2759
def lo2760b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨16,by decide⟩
def lo2760b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨17,by decide⟩
def lo2760 : CheckedMoment :=
  CheckedMoment.ofBessel lo2760b1 lo2760b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2760b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨21,by decide⟩
def hi2760b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨22,by decide⟩
def hi2760 : CheckedMoment :=
  CheckedMoment.ofBessel hi2760b1 hi2760b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2760 : meanBracketCheck (24929/25000) lo2760 hi2760=true := by decide +kernel
def bracket2760 : MeanBracket := meanBracketOfMoments (24929/25000) lo2760 hi2760 accepted2760
def lo2761b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨26,by decide⟩
def lo2761b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨27,by decide⟩
def lo2761 : CheckedMoment :=
  CheckedMoment.ofBessel lo2761b1 lo2761b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2761b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨31,by decide⟩
def hi2761b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨32,by decide⟩
def hi2761 : CheckedMoment :=
  CheckedMoment.ofBessel hi2761b1 hi2761b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2761 : meanBracketCheck (199433/200000) lo2761 hi2761=true := by decide +kernel
def bracket2761 : MeanBracket := meanBracketOfMoments (199433/200000) lo2761 hi2761 accepted2761
def lo2762b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨36,by decide⟩
def lo2762b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨37,by decide⟩
def lo2762 : CheckedMoment :=
  CheckedMoment.ofBessel lo2762b1 lo2762b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2762b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨41,by decide⟩
def hi2762b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨42,by decide⟩
def hi2762 : CheckedMoment :=
  CheckedMoment.ofBessel hi2762b1 hi2762b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2762 : meanBracketCheck (99717/100000) lo2762 hi2762=true := by decide +kernel
def bracket2762 : MeanBracket := meanBracketOfMoments (99717/100000) lo2762 hi2762 accepted2762
def lo2763b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨46,by decide⟩
def lo2763b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨47,by decide⟩
def lo2763 : CheckedMoment :=
  CheckedMoment.ofBessel lo2763b1 lo2763b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2763b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨51,by decide⟩
def hi2763b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨52,by decide⟩
def hi2763 : CheckedMoment :=
  CheckedMoment.ofBessel hi2763b1 hi2763b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2763 : meanBracketCheck (39887/40000) lo2763 hi2763=true := by decide +kernel
def bracket2763 : MeanBracket := meanBracketOfMoments (39887/40000) lo2763 hi2763 accepted2763
def lo2764b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨56,by decide⟩
def lo2764b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨57,by decide⟩
def lo2764 : CheckedMoment :=
  CheckedMoment.ofBessel lo2764b1 lo2764b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2764b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨61,by decide⟩
def hi2764b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨62,by decide⟩
def hi2764 : CheckedMoment :=
  CheckedMoment.ofBessel hi2764b1 hi2764b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2764 : meanBracketCheck (49859/50000) lo2764 hi2764=true := by decide +kernel
def bracket2764 : MeanBracket := meanBracketOfMoments (49859/50000) lo2764 hi2764 accepted2764
def lo2765b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨2,by decide⟩
def lo2765b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨3,by decide⟩
def lo2765 : CheckedMoment :=
  CheckedMoment.ofBessel lo2765b1 lo2765b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2765b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨7,by decide⟩
def hi2765b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨8,by decide⟩
def hi2765 : CheckedMoment :=
  CheckedMoment.ofBessel hi2765b1 hi2765b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2765 : meanBracketCheck (199437/200000) lo2765 hi2765=true := by decide +kernel
def bracket2765 : MeanBracket := meanBracketOfMoments (199437/200000) lo2765 hi2765 accepted2765
def lo2766b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨12,by decide⟩
def lo2766b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨13,by decide⟩
def lo2766 : CheckedMoment :=
  CheckedMoment.ofBessel lo2766b1 lo2766b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2766b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨17,by decide⟩
def hi2766b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨18,by decide⟩
def hi2766 : CheckedMoment :=
  CheckedMoment.ofBessel hi2766b1 hi2766b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2766 : meanBracketCheck (99719/100000) lo2766 hi2766=true := by decide +kernel
def bracket2766 : MeanBracket := meanBracketOfMoments (99719/100000) lo2766 hi2766 accepted2766
def lo2767b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨22,by decide⟩
def lo2767b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨23,by decide⟩
def lo2767 : CheckedMoment :=
  CheckedMoment.ofBessel lo2767b1 lo2767b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2767b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨27,by decide⟩
def hi2767b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0432.rows BesselBatch0432.accepted ⟨28,by decide⟩
def hi2767 : CheckedMoment :=
  CheckedMoment.ofBessel hi2767b1 hi2767b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2767 : meanBracketCheck (199439/200000) lo2767 hi2767=true := by decide +kernel
def bracket2767 : MeanBracket := meanBracketOfMoments (199439/200000) lo2767 hi2767 accepted2767
#print axioms bracket2752
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0172
