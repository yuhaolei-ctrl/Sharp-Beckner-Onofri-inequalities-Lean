module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0105
public import BecknerOnofri.EntropyScalarCertificate.Bessel0106
public import BecknerOnofri.EntropyScalarCertificate.Bessel0107

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0042
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0672b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨0,by decide⟩
def lo0672b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨1,by decide⟩
def lo0672 : CheckedMoment :=
  CheckedMoment.ofBessel lo0672b1 lo0672b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0672b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨5,by decide⟩
def hi0672b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨6,by decide⟩
def hi0672 : CheckedMoment :=
  CheckedMoment.ofBessel hi0672b1 hi0672b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0672 : meanBracketCheck (1909/10000) lo0672 hi0672=true := by decide +kernel
def bracket0672 : MeanBracket := meanBracketOfMoments (1909/10000) lo0672 hi0672 accepted0672
def lo0673b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨10,by decide⟩
def lo0673b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨11,by decide⟩
def lo0673 : CheckedMoment :=
  CheckedMoment.ofBessel lo0673b1 lo0673b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0673b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨15,by decide⟩
def hi0673b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨16,by decide⟩
def hi0673 : CheckedMoment :=
  CheckedMoment.ofBessel hi0673b1 hi0673b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0673 : meanBracketCheck (1911/10000) lo0673 hi0673=true := by decide +kernel
def bracket0673 : MeanBracket := meanBracketOfMoments (1911/10000) lo0673 hi0673 accepted0673
def lo0674b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨20,by decide⟩
def lo0674b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨21,by decide⟩
def lo0674 : CheckedMoment :=
  CheckedMoment.ofBessel lo0674b1 lo0674b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0674b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨25,by decide⟩
def hi0674b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨26,by decide⟩
def hi0674 : CheckedMoment :=
  CheckedMoment.ofBessel hi0674b1 hi0674b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0674 : meanBracketCheck (1913/10000) lo0674 hi0674=true := by decide +kernel
def bracket0674 : MeanBracket := meanBracketOfMoments (1913/10000) lo0674 hi0674 accepted0674
def lo0675b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨30,by decide⟩
def lo0675b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨31,by decide⟩
def lo0675 : CheckedMoment :=
  CheckedMoment.ofBessel lo0675b1 lo0675b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0675b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨35,by decide⟩
def hi0675b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨36,by decide⟩
def hi0675 : CheckedMoment :=
  CheckedMoment.ofBessel hi0675b1 hi0675b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0675 : meanBracketCheck (383/2000) lo0675 hi0675=true := by decide +kernel
def bracket0675 : MeanBracket := meanBracketOfMoments (383/2000) lo0675 hi0675 accepted0675
def lo0676b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨40,by decide⟩
def lo0676b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨41,by decide⟩
def lo0676 : CheckedMoment :=
  CheckedMoment.ofBessel lo0676b1 lo0676b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0676b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨45,by decide⟩
def hi0676b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨46,by decide⟩
def hi0676 : CheckedMoment :=
  CheckedMoment.ofBessel hi0676b1 hi0676b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0676 : meanBracketCheck (1917/10000) lo0676 hi0676=true := by decide +kernel
def bracket0676 : MeanBracket := meanBracketOfMoments (1917/10000) lo0676 hi0676 accepted0676
def lo0677b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨50,by decide⟩
def lo0677b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨51,by decide⟩
def lo0677 : CheckedMoment :=
  CheckedMoment.ofBessel lo0677b1 lo0677b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0677b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨55,by decide⟩
def hi0677b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨56,by decide⟩
def hi0677 : CheckedMoment :=
  CheckedMoment.ofBessel hi0677b1 hi0677b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0677 : meanBracketCheck (1919/10000) lo0677 hi0677=true := by decide +kernel
def bracket0677 : MeanBracket := meanBracketOfMoments (1919/10000) lo0677 hi0677 accepted0677
def lo0678b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨60,by decide⟩
def lo0678b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨61,by decide⟩
def lo0678 : CheckedMoment :=
  CheckedMoment.ofBessel lo0678b1 lo0678b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0678b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨1,by decide⟩
def hi0678b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨2,by decide⟩
def hi0678 : CheckedMoment :=
  CheckedMoment.ofBessel hi0678b1 hi0678b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0678 : meanBracketCheck (1921/10000) lo0678 hi0678=true := by decide +kernel
def bracket0678 : MeanBracket := meanBracketOfMoments (1921/10000) lo0678 hi0678 accepted0678
def lo0679b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨6,by decide⟩
def lo0679b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨7,by decide⟩
def lo0679 : CheckedMoment :=
  CheckedMoment.ofBessel lo0679b1 lo0679b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0679b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨11,by decide⟩
def hi0679b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨12,by decide⟩
def hi0679 : CheckedMoment :=
  CheckedMoment.ofBessel hi0679b1 hi0679b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0679 : meanBracketCheck (1923/10000) lo0679 hi0679=true := by decide +kernel
def bracket0679 : MeanBracket := meanBracketOfMoments (1923/10000) lo0679 hi0679 accepted0679
def lo0680b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨16,by decide⟩
def lo0680b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨17,by decide⟩
def lo0680 : CheckedMoment :=
  CheckedMoment.ofBessel lo0680b1 lo0680b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0680b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨21,by decide⟩
def hi0680b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨22,by decide⟩
def hi0680 : CheckedMoment :=
  CheckedMoment.ofBessel hi0680b1 hi0680b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0680 : meanBracketCheck (77/400) lo0680 hi0680=true := by decide +kernel
def bracket0680 : MeanBracket := meanBracketOfMoments (77/400) lo0680 hi0680 accepted0680
def lo0681b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨26,by decide⟩
def lo0681b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨27,by decide⟩
def lo0681 : CheckedMoment :=
  CheckedMoment.ofBessel lo0681b1 lo0681b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0681b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨31,by decide⟩
def hi0681b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨32,by decide⟩
def hi0681 : CheckedMoment :=
  CheckedMoment.ofBessel hi0681b1 hi0681b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0681 : meanBracketCheck (1927/10000) lo0681 hi0681=true := by decide +kernel
def bracket0681 : MeanBracket := meanBracketOfMoments (1927/10000) lo0681 hi0681 accepted0681
def lo0682b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨36,by decide⟩
def lo0682b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨37,by decide⟩
def lo0682 : CheckedMoment :=
  CheckedMoment.ofBessel lo0682b1 lo0682b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0682b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨41,by decide⟩
def hi0682b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨42,by decide⟩
def hi0682 : CheckedMoment :=
  CheckedMoment.ofBessel hi0682b1 hi0682b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0682 : meanBracketCheck (1929/10000) lo0682 hi0682=true := by decide +kernel
def bracket0682 : MeanBracket := meanBracketOfMoments (1929/10000) lo0682 hi0682 accepted0682
def lo0683b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨46,by decide⟩
def lo0683b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨47,by decide⟩
def lo0683 : CheckedMoment :=
  CheckedMoment.ofBessel lo0683b1 lo0683b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0683b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨51,by decide⟩
def hi0683b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨52,by decide⟩
def hi0683 : CheckedMoment :=
  CheckedMoment.ofBessel hi0683b1 hi0683b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0683 : meanBracketCheck (1931/10000) lo0683 hi0683=true := by decide +kernel
def bracket0683 : MeanBracket := meanBracketOfMoments (1931/10000) lo0683 hi0683 accepted0683
def lo0684b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨56,by decide⟩
def lo0684b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨57,by decide⟩
def lo0684 : CheckedMoment :=
  CheckedMoment.ofBessel lo0684b1 lo0684b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0684b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨61,by decide⟩
def hi0684b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨62,by decide⟩
def hi0684 : CheckedMoment :=
  CheckedMoment.ofBessel hi0684b1 hi0684b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0684 : meanBracketCheck (1933/10000) lo0684 hi0684=true := by decide +kernel
def bracket0684 : MeanBracket := meanBracketOfMoments (1933/10000) lo0684 hi0684 accepted0684
def lo0685b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨2,by decide⟩
def lo0685b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨3,by decide⟩
def lo0685 : CheckedMoment :=
  CheckedMoment.ofBessel lo0685b1 lo0685b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0685b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨7,by decide⟩
def hi0685b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨8,by decide⟩
def hi0685 : CheckedMoment :=
  CheckedMoment.ofBessel hi0685b1 hi0685b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0685 : meanBracketCheck (387/2000) lo0685 hi0685=true := by decide +kernel
def bracket0685 : MeanBracket := meanBracketOfMoments (387/2000) lo0685 hi0685 accepted0685
def lo0686b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨12,by decide⟩
def lo0686b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨13,by decide⟩
def lo0686 : CheckedMoment :=
  CheckedMoment.ofBessel lo0686b1 lo0686b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0686b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨17,by decide⟩
def hi0686b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨18,by decide⟩
def hi0686 : CheckedMoment :=
  CheckedMoment.ofBessel hi0686b1 hi0686b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0686 : meanBracketCheck (1937/10000) lo0686 hi0686=true := by decide +kernel
def bracket0686 : MeanBracket := meanBracketOfMoments (1937/10000) lo0686 hi0686 accepted0686
def lo0687b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨22,by decide⟩
def lo0687b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨23,by decide⟩
def lo0687 : CheckedMoment :=
  CheckedMoment.ofBessel lo0687b1 lo0687b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0687b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨27,by decide⟩
def hi0687b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0107.rows BesselBatch0107.accepted ⟨28,by decide⟩
def hi0687 : CheckedMoment :=
  CheckedMoment.ofBessel hi0687b1 hi0687b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0687 : meanBracketCheck (1939/10000) lo0687 hi0687=true := by decide +kernel
def bracket0687 : MeanBracket := meanBracketOfMoments (1939/10000) lo0687 hi0687 accepted0687
#print axioms bracket0672
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0042
