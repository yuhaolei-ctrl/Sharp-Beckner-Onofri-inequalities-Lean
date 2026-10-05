module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0120
public import BecknerOnofri.EntropyScalarCertificate.Bessel0121
public import BecknerOnofri.EntropyScalarCertificate.Bessel0122

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0048
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0768b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨0,by decide⟩
def lo0768b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨1,by decide⟩
def lo0768 : CheckedMoment :=
  CheckedMoment.ofBessel lo0768b1 lo0768b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0768b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨5,by decide⟩
def hi0768b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨6,by decide⟩
def hi0768 : CheckedMoment :=
  CheckedMoment.ofBessel hi0768b1 hi0768b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0768 : meanBracketCheck (1/4) lo0768 hi0768=true := by decide +kernel
def bracket0768 : MeanBracket := meanBracketOfMoments (1/4) lo0768 hi0768 accepted0768
def lo0769b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨10,by decide⟩
def lo0769b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨11,by decide⟩
def lo0769 : CheckedMoment :=
  CheckedMoment.ofBessel lo0769b1 lo0769b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0769b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨15,by decide⟩
def hi0769b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨16,by decide⟩
def hi0769 : CheckedMoment :=
  CheckedMoment.ofBessel hi0769b1 hi0769b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0769 : meanBracketCheck (251/1000) lo0769 hi0769=true := by decide +kernel
def bracket0769 : MeanBracket := meanBracketOfMoments (251/1000) lo0769 hi0769 accepted0769
def lo0770b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨20,by decide⟩
def lo0770b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨21,by decide⟩
def lo0770 : CheckedMoment :=
  CheckedMoment.ofBessel lo0770b1 lo0770b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0770b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨25,by decide⟩
def hi0770b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨26,by decide⟩
def hi0770 : CheckedMoment :=
  CheckedMoment.ofBessel hi0770b1 hi0770b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0770 : meanBracketCheck (63/250) lo0770 hi0770=true := by decide +kernel
def bracket0770 : MeanBracket := meanBracketOfMoments (63/250) lo0770 hi0770 accepted0770
def lo0771b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨30,by decide⟩
def lo0771b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨31,by decide⟩
def lo0771 : CheckedMoment :=
  CheckedMoment.ofBessel lo0771b1 lo0771b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0771b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨35,by decide⟩
def hi0771b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨36,by decide⟩
def hi0771 : CheckedMoment :=
  CheckedMoment.ofBessel hi0771b1 hi0771b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0771 : meanBracketCheck (253/1000) lo0771 hi0771=true := by decide +kernel
def bracket0771 : MeanBracket := meanBracketOfMoments (253/1000) lo0771 hi0771 accepted0771
def lo0772b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨40,by decide⟩
def lo0772b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨41,by decide⟩
def lo0772 : CheckedMoment :=
  CheckedMoment.ofBessel lo0772b1 lo0772b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0772b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨45,by decide⟩
def hi0772b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨46,by decide⟩
def hi0772 : CheckedMoment :=
  CheckedMoment.ofBessel hi0772b1 hi0772b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0772 : meanBracketCheck (127/500) lo0772 hi0772=true := by decide +kernel
def bracket0772 : MeanBracket := meanBracketOfMoments (127/500) lo0772 hi0772 accepted0772
def lo0773b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨50,by decide⟩
def lo0773b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨51,by decide⟩
def lo0773 : CheckedMoment :=
  CheckedMoment.ofBessel lo0773b1 lo0773b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0773b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨55,by decide⟩
def hi0773b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨56,by decide⟩
def hi0773 : CheckedMoment :=
  CheckedMoment.ofBessel hi0773b1 hi0773b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0773 : meanBracketCheck (51/200) lo0773 hi0773=true := by decide +kernel
def bracket0773 : MeanBracket := meanBracketOfMoments (51/200) lo0773 hi0773 accepted0773
def lo0774b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨60,by decide⟩
def lo0774b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨61,by decide⟩
def lo0774 : CheckedMoment :=
  CheckedMoment.ofBessel lo0774b1 lo0774b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0774b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨1,by decide⟩
def hi0774b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨2,by decide⟩
def hi0774 : CheckedMoment :=
  CheckedMoment.ofBessel hi0774b1 hi0774b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0774 : meanBracketCheck (32/125) lo0774 hi0774=true := by decide +kernel
def bracket0774 : MeanBracket := meanBracketOfMoments (32/125) lo0774 hi0774 accepted0774
def lo0775b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨6,by decide⟩
def lo0775b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨7,by decide⟩
def lo0775 : CheckedMoment :=
  CheckedMoment.ofBessel lo0775b1 lo0775b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0775b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨11,by decide⟩
def hi0775b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨12,by decide⟩
def hi0775 : CheckedMoment :=
  CheckedMoment.ofBessel hi0775b1 hi0775b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0775 : meanBracketCheck (257/1000) lo0775 hi0775=true := by decide +kernel
def bracket0775 : MeanBracket := meanBracketOfMoments (257/1000) lo0775 hi0775 accepted0775
def lo0776b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨16,by decide⟩
def lo0776b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨17,by decide⟩
def lo0776 : CheckedMoment :=
  CheckedMoment.ofBessel lo0776b1 lo0776b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0776b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨21,by decide⟩
def hi0776b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨22,by decide⟩
def hi0776 : CheckedMoment :=
  CheckedMoment.ofBessel hi0776b1 hi0776b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0776 : meanBracketCheck (129/500) lo0776 hi0776=true := by decide +kernel
def bracket0776 : MeanBracket := meanBracketOfMoments (129/500) lo0776 hi0776 accepted0776
def lo0777b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨26,by decide⟩
def lo0777b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨27,by decide⟩
def lo0777 : CheckedMoment :=
  CheckedMoment.ofBessel lo0777b1 lo0777b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0777b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨31,by decide⟩
def hi0777b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨32,by decide⟩
def hi0777 : CheckedMoment :=
  CheckedMoment.ofBessel hi0777b1 hi0777b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0777 : meanBracketCheck (259/1000) lo0777 hi0777=true := by decide +kernel
def bracket0777 : MeanBracket := meanBracketOfMoments (259/1000) lo0777 hi0777 accepted0777
def lo0778b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨36,by decide⟩
def lo0778b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨37,by decide⟩
def lo0778 : CheckedMoment :=
  CheckedMoment.ofBessel lo0778b1 lo0778b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0778b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨41,by decide⟩
def hi0778b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨42,by decide⟩
def hi0778 : CheckedMoment :=
  CheckedMoment.ofBessel hi0778b1 hi0778b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0778 : meanBracketCheck (13/50) lo0778 hi0778=true := by decide +kernel
def bracket0778 : MeanBracket := meanBracketOfMoments (13/50) lo0778 hi0778 accepted0778
def lo0779b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨46,by decide⟩
def lo0779b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨47,by decide⟩
def lo0779 : CheckedMoment :=
  CheckedMoment.ofBessel lo0779b1 lo0779b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0779b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨51,by decide⟩
def hi0779b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨52,by decide⟩
def hi0779 : CheckedMoment :=
  CheckedMoment.ofBessel hi0779b1 hi0779b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0779 : meanBracketCheck (261/1000) lo0779 hi0779=true := by decide +kernel
def bracket0779 : MeanBracket := meanBracketOfMoments (261/1000) lo0779 hi0779 accepted0779
def lo0780b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨56,by decide⟩
def lo0780b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨57,by decide⟩
def lo0780 : CheckedMoment :=
  CheckedMoment.ofBessel lo0780b1 lo0780b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0780b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨61,by decide⟩
def hi0780b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨62,by decide⟩
def hi0780 : CheckedMoment :=
  CheckedMoment.ofBessel hi0780b1 hi0780b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0780 : meanBracketCheck (131/500) lo0780 hi0780=true := by decide +kernel
def bracket0780 : MeanBracket := meanBracketOfMoments (131/500) lo0780 hi0780 accepted0780
def lo0781b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨2,by decide⟩
def lo0781b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨3,by decide⟩
def lo0781 : CheckedMoment :=
  CheckedMoment.ofBessel lo0781b1 lo0781b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0781b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨7,by decide⟩
def hi0781b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨8,by decide⟩
def hi0781 : CheckedMoment :=
  CheckedMoment.ofBessel hi0781b1 hi0781b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0781 : meanBracketCheck (263/1000) lo0781 hi0781=true := by decide +kernel
def bracket0781 : MeanBracket := meanBracketOfMoments (263/1000) lo0781 hi0781 accepted0781
def lo0782b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨12,by decide⟩
def lo0782b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨13,by decide⟩
def lo0782 : CheckedMoment :=
  CheckedMoment.ofBessel lo0782b1 lo0782b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0782b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨17,by decide⟩
def hi0782b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨18,by decide⟩
def hi0782 : CheckedMoment :=
  CheckedMoment.ofBessel hi0782b1 hi0782b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0782 : meanBracketCheck (33/125) lo0782 hi0782=true := by decide +kernel
def bracket0782 : MeanBracket := meanBracketOfMoments (33/125) lo0782 hi0782 accepted0782
def lo0783b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨22,by decide⟩
def lo0783b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨23,by decide⟩
def lo0783 : CheckedMoment :=
  CheckedMoment.ofBessel lo0783b1 lo0783b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0783b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨27,by decide⟩
def hi0783b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨28,by decide⟩
def hi0783 : CheckedMoment :=
  CheckedMoment.ofBessel hi0783b1 hi0783b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0783 : meanBracketCheck (53/200) lo0783 hi0783=true := by decide +kernel
def bracket0783 : MeanBracket := meanBracketOfMoments (53/200) lo0783 hi0783 accepted0783
#print axioms bracket0768
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0048
