module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0122
public import BecknerOnofri.EntropyScalarCertificate.Bessel0123
public import BecknerOnofri.EntropyScalarCertificate.Bessel0124

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0049
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0784b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨32,by decide⟩
def lo0784b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨33,by decide⟩
def lo0784 : CheckedMoment :=
  CheckedMoment.ofBessel lo0784b1 lo0784b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0784b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨37,by decide⟩
def hi0784b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨38,by decide⟩
def hi0784 : CheckedMoment :=
  CheckedMoment.ofBessel hi0784b1 hi0784b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0784 : meanBracketCheck (133/500) lo0784 hi0784=true := by decide +kernel
def bracket0784 : MeanBracket := meanBracketOfMoments (133/500) lo0784 hi0784 accepted0784
def lo0785b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨42,by decide⟩
def lo0785b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨43,by decide⟩
def lo0785 : CheckedMoment :=
  CheckedMoment.ofBessel lo0785b1 lo0785b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0785b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨47,by decide⟩
def hi0785b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨48,by decide⟩
def hi0785 : CheckedMoment :=
  CheckedMoment.ofBessel hi0785b1 hi0785b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0785 : meanBracketCheck (267/1000) lo0785 hi0785=true := by decide +kernel
def bracket0785 : MeanBracket := meanBracketOfMoments (267/1000) lo0785 hi0785 accepted0785
def lo0786b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨52,by decide⟩
def lo0786b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨53,by decide⟩
def lo0786 : CheckedMoment :=
  CheckedMoment.ofBessel lo0786b1 lo0786b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0786b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨57,by decide⟩
def hi0786b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨58,by decide⟩
def hi0786 : CheckedMoment :=
  CheckedMoment.ofBessel hi0786b1 hi0786b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0786 : meanBracketCheck (67/250) lo0786 hi0786=true := by decide +kernel
def bracket0786 : MeanBracket := meanBracketOfMoments (67/250) lo0786 hi0786 accepted0786
def lo0787b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨62,by decide⟩
def lo0787b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨63,by decide⟩
def lo0787 : CheckedMoment :=
  CheckedMoment.ofBessel lo0787b1 lo0787b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0787b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨3,by decide⟩
def hi0787b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨4,by decide⟩
def hi0787 : CheckedMoment :=
  CheckedMoment.ofBessel hi0787b1 hi0787b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0787 : meanBracketCheck (269/1000) lo0787 hi0787=true := by decide +kernel
def bracket0787 : MeanBracket := meanBracketOfMoments (269/1000) lo0787 hi0787 accepted0787
def lo0788b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨8,by decide⟩
def lo0788b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨9,by decide⟩
def lo0788 : CheckedMoment :=
  CheckedMoment.ofBessel lo0788b1 lo0788b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0788b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨13,by decide⟩
def hi0788b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨14,by decide⟩
def hi0788 : CheckedMoment :=
  CheckedMoment.ofBessel hi0788b1 hi0788b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0788 : meanBracketCheck (27/100) lo0788 hi0788=true := by decide +kernel
def bracket0788 : MeanBracket := meanBracketOfMoments (27/100) lo0788 hi0788 accepted0788
def lo0789b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨18,by decide⟩
def lo0789b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨19,by decide⟩
def lo0789 : CheckedMoment :=
  CheckedMoment.ofBessel lo0789b1 lo0789b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0789b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨23,by decide⟩
def hi0789b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨24,by decide⟩
def hi0789 : CheckedMoment :=
  CheckedMoment.ofBessel hi0789b1 hi0789b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0789 : meanBracketCheck (271/1000) lo0789 hi0789=true := by decide +kernel
def bracket0789 : MeanBracket := meanBracketOfMoments (271/1000) lo0789 hi0789 accepted0789
def lo0790b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨28,by decide⟩
def lo0790b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨29,by decide⟩
def lo0790 : CheckedMoment :=
  CheckedMoment.ofBessel lo0790b1 lo0790b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0790b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨33,by decide⟩
def hi0790b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨34,by decide⟩
def hi0790 : CheckedMoment :=
  CheckedMoment.ofBessel hi0790b1 hi0790b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0790 : meanBracketCheck (34/125) lo0790 hi0790=true := by decide +kernel
def bracket0790 : MeanBracket := meanBracketOfMoments (34/125) lo0790 hi0790 accepted0790
def lo0791b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨38,by decide⟩
def lo0791b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨39,by decide⟩
def lo0791 : CheckedMoment :=
  CheckedMoment.ofBessel lo0791b1 lo0791b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0791b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨43,by decide⟩
def hi0791b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨44,by decide⟩
def hi0791 : CheckedMoment :=
  CheckedMoment.ofBessel hi0791b1 hi0791b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0791 : meanBracketCheck (273/1000) lo0791 hi0791=true := by decide +kernel
def bracket0791 : MeanBracket := meanBracketOfMoments (273/1000) lo0791 hi0791 accepted0791
def lo0792b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨48,by decide⟩
def lo0792b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨49,by decide⟩
def lo0792 : CheckedMoment :=
  CheckedMoment.ofBessel lo0792b1 lo0792b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0792b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨53,by decide⟩
def hi0792b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨54,by decide⟩
def hi0792 : CheckedMoment :=
  CheckedMoment.ofBessel hi0792b1 hi0792b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0792 : meanBracketCheck (137/500) lo0792 hi0792=true := by decide +kernel
def bracket0792 : MeanBracket := meanBracketOfMoments (137/500) lo0792 hi0792 accepted0792
def lo0793b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨58,by decide⟩
def lo0793b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨59,by decide⟩
def lo0793 : CheckedMoment :=
  CheckedMoment.ofBessel lo0793b1 lo0793b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0793b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨63,by decide⟩
def hi0793b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨0,by decide⟩
def hi0793 : CheckedMoment :=
  CheckedMoment.ofBessel hi0793b1 hi0793b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0793 : meanBracketCheck (11/40) lo0793 hi0793=true := by decide +kernel
def bracket0793 : MeanBracket := meanBracketOfMoments (11/40) lo0793 hi0793 accepted0793
def lo0794b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨4,by decide⟩
def lo0794b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨5,by decide⟩
def lo0794 : CheckedMoment :=
  CheckedMoment.ofBessel lo0794b1 lo0794b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0794b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨9,by decide⟩
def hi0794b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨10,by decide⟩
def hi0794 : CheckedMoment :=
  CheckedMoment.ofBessel hi0794b1 hi0794b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0794 : meanBracketCheck (69/250) lo0794 hi0794=true := by decide +kernel
def bracket0794 : MeanBracket := meanBracketOfMoments (69/250) lo0794 hi0794 accepted0794
def lo0795b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨14,by decide⟩
def lo0795b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨15,by decide⟩
def lo0795 : CheckedMoment :=
  CheckedMoment.ofBessel lo0795b1 lo0795b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0795b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨19,by decide⟩
def hi0795b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨20,by decide⟩
def hi0795 : CheckedMoment :=
  CheckedMoment.ofBessel hi0795b1 hi0795b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0795 : meanBracketCheck (277/1000) lo0795 hi0795=true := by decide +kernel
def bracket0795 : MeanBracket := meanBracketOfMoments (277/1000) lo0795 hi0795 accepted0795
def lo0796b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨24,by decide⟩
def lo0796b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨25,by decide⟩
def lo0796 : CheckedMoment :=
  CheckedMoment.ofBessel lo0796b1 lo0796b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0796b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨29,by decide⟩
def hi0796b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨30,by decide⟩
def hi0796 : CheckedMoment :=
  CheckedMoment.ofBessel hi0796b1 hi0796b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0796 : meanBracketCheck (139/500) lo0796 hi0796=true := by decide +kernel
def bracket0796 : MeanBracket := meanBracketOfMoments (139/500) lo0796 hi0796 accepted0796
def lo0797b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨34,by decide⟩
def lo0797b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨35,by decide⟩
def lo0797 : CheckedMoment :=
  CheckedMoment.ofBessel lo0797b1 lo0797b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0797b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨39,by decide⟩
def hi0797b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨40,by decide⟩
def hi0797 : CheckedMoment :=
  CheckedMoment.ofBessel hi0797b1 hi0797b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0797 : meanBracketCheck (279/1000) lo0797 hi0797=true := by decide +kernel
def bracket0797 : MeanBracket := meanBracketOfMoments (279/1000) lo0797 hi0797 accepted0797
def lo0798b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨44,by decide⟩
def lo0798b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨45,by decide⟩
def lo0798 : CheckedMoment :=
  CheckedMoment.ofBessel lo0798b1 lo0798b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0798b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨49,by decide⟩
def hi0798b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨50,by decide⟩
def hi0798 : CheckedMoment :=
  CheckedMoment.ofBessel hi0798b1 hi0798b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0798 : meanBracketCheck (7/25) lo0798 hi0798=true := by decide +kernel
def bracket0798 : MeanBracket := meanBracketOfMoments (7/25) lo0798 hi0798 accepted0798
def lo0799b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨54,by decide⟩
def lo0799b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨55,by decide⟩
def lo0799 : CheckedMoment :=
  CheckedMoment.ofBessel lo0799b1 lo0799b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0799b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨59,by decide⟩
def hi0799b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0124.rows BesselBatch0124.accepted ⟨60,by decide⟩
def hi0799 : CheckedMoment :=
  CheckedMoment.ofBessel hi0799b1 hi0799b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0799 : meanBracketCheck (281/1000) lo0799 hi0799=true := by decide +kernel
def bracket0799 : MeanBracket := meanBracketOfMoments (281/1000) lo0799 hi0799 accepted0799
#print axioms bracket0784
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0049
