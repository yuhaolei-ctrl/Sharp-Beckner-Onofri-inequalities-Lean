import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0117
import BecknerOnofri.EntropyScalarCertificate.Bessel0118
import BecknerOnofri.EntropyScalarCertificate.Bessel0119
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0047
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0752b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨32,by decide⟩
def lo0752b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨33,by decide⟩
def lo0752 : CheckedMoment :=
  CheckedMoment.ofBessel lo0752b1 lo0752b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0752b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨37,by decide⟩
def hi0752b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨38,by decide⟩
def hi0752 : CheckedMoment :=
  CheckedMoment.ofBessel hi0752b1 hi0752b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0752 : meanBracketCheck (117/500) lo0752 hi0752=true := by decide +kernel
def bracket0752 : MeanBracket := meanBracketOfMoments (117/500) lo0752 hi0752 accepted0752
def lo0753b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨42,by decide⟩
def lo0753b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨43,by decide⟩
def lo0753 : CheckedMoment :=
  CheckedMoment.ofBessel lo0753b1 lo0753b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0753b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨47,by decide⟩
def hi0753b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨48,by decide⟩
def hi0753 : CheckedMoment :=
  CheckedMoment.ofBessel hi0753b1 hi0753b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0753 : meanBracketCheck (47/200) lo0753 hi0753=true := by decide +kernel
def bracket0753 : MeanBracket := meanBracketOfMoments (47/200) lo0753 hi0753 accepted0753
def lo0754b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨52,by decide⟩
def lo0754b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨53,by decide⟩
def lo0754 : CheckedMoment :=
  CheckedMoment.ofBessel lo0754b1 lo0754b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0754b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨57,by decide⟩
def hi0754b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨58,by decide⟩
def hi0754 : CheckedMoment :=
  CheckedMoment.ofBessel hi0754b1 hi0754b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0754 : meanBracketCheck (59/250) lo0754 hi0754=true := by decide +kernel
def bracket0754 : MeanBracket := meanBracketOfMoments (59/250) lo0754 hi0754 accepted0754
def lo0755b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨62,by decide⟩
def lo0755b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨63,by decide⟩
def lo0755 : CheckedMoment :=
  CheckedMoment.ofBessel lo0755b1 lo0755b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0755b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨3,by decide⟩
def hi0755b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨4,by decide⟩
def hi0755 : CheckedMoment :=
  CheckedMoment.ofBessel hi0755b1 hi0755b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0755 : meanBracketCheck (237/1000) lo0755 hi0755=true := by decide +kernel
def bracket0755 : MeanBracket := meanBracketOfMoments (237/1000) lo0755 hi0755 accepted0755
def lo0756b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨8,by decide⟩
def lo0756b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨9,by decide⟩
def lo0756 : CheckedMoment :=
  CheckedMoment.ofBessel lo0756b1 lo0756b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0756b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨13,by decide⟩
def hi0756b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨14,by decide⟩
def hi0756 : CheckedMoment :=
  CheckedMoment.ofBessel hi0756b1 hi0756b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0756 : meanBracketCheck (119/500) lo0756 hi0756=true := by decide +kernel
def bracket0756 : MeanBracket := meanBracketOfMoments (119/500) lo0756 hi0756 accepted0756
def lo0757b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨18,by decide⟩
def lo0757b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨19,by decide⟩
def lo0757 : CheckedMoment :=
  CheckedMoment.ofBessel lo0757b1 lo0757b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0757b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨23,by decide⟩
def hi0757b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨24,by decide⟩
def hi0757 : CheckedMoment :=
  CheckedMoment.ofBessel hi0757b1 hi0757b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0757 : meanBracketCheck (239/1000) lo0757 hi0757=true := by decide +kernel
def bracket0757 : MeanBracket := meanBracketOfMoments (239/1000) lo0757 hi0757 accepted0757
def lo0758b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨28,by decide⟩
def lo0758b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨29,by decide⟩
def lo0758 : CheckedMoment :=
  CheckedMoment.ofBessel lo0758b1 lo0758b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0758b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨33,by decide⟩
def hi0758b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨34,by decide⟩
def hi0758 : CheckedMoment :=
  CheckedMoment.ofBessel hi0758b1 hi0758b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0758 : meanBracketCheck (6/25) lo0758 hi0758=true := by decide +kernel
def bracket0758 : MeanBracket := meanBracketOfMoments (6/25) lo0758 hi0758 accepted0758
def lo0759b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨38,by decide⟩
def lo0759b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨39,by decide⟩
def lo0759 : CheckedMoment :=
  CheckedMoment.ofBessel lo0759b1 lo0759b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0759b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨43,by decide⟩
def hi0759b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨44,by decide⟩
def hi0759 : CheckedMoment :=
  CheckedMoment.ofBessel hi0759b1 hi0759b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0759 : meanBracketCheck (241/1000) lo0759 hi0759=true := by decide +kernel
def bracket0759 : MeanBracket := meanBracketOfMoments (241/1000) lo0759 hi0759 accepted0759
def lo0760b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨48,by decide⟩
def lo0760b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨49,by decide⟩
def lo0760 : CheckedMoment :=
  CheckedMoment.ofBessel lo0760b1 lo0760b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0760b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨53,by decide⟩
def hi0760b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨54,by decide⟩
def hi0760 : CheckedMoment :=
  CheckedMoment.ofBessel hi0760b1 hi0760b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0760 : meanBracketCheck (121/500) lo0760 hi0760=true := by decide +kernel
def bracket0760 : MeanBracket := meanBracketOfMoments (121/500) lo0760 hi0760 accepted0760
def lo0761b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨58,by decide⟩
def lo0761b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨59,by decide⟩
def lo0761 : CheckedMoment :=
  CheckedMoment.ofBessel lo0761b1 lo0761b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0761b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨63,by decide⟩
def hi0761b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨0,by decide⟩
def hi0761 : CheckedMoment :=
  CheckedMoment.ofBessel hi0761b1 hi0761b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0761 : meanBracketCheck (243/1000) lo0761 hi0761=true := by decide +kernel
def bracket0761 : MeanBracket := meanBracketOfMoments (243/1000) lo0761 hi0761 accepted0761
def lo0762b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨4,by decide⟩
def lo0762b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨5,by decide⟩
def lo0762 : CheckedMoment :=
  CheckedMoment.ofBessel lo0762b1 lo0762b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0762b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨9,by decide⟩
def hi0762b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨10,by decide⟩
def hi0762 : CheckedMoment :=
  CheckedMoment.ofBessel hi0762b1 hi0762b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0762 : meanBracketCheck (61/250) lo0762 hi0762=true := by decide +kernel
def bracket0762 : MeanBracket := meanBracketOfMoments (61/250) lo0762 hi0762 accepted0762
def lo0763b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨14,by decide⟩
def lo0763b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨15,by decide⟩
def lo0763 : CheckedMoment :=
  CheckedMoment.ofBessel lo0763b1 lo0763b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0763b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨19,by decide⟩
def hi0763b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨20,by decide⟩
def hi0763 : CheckedMoment :=
  CheckedMoment.ofBessel hi0763b1 hi0763b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0763 : meanBracketCheck (49/200) lo0763 hi0763=true := by decide +kernel
def bracket0763 : MeanBracket := meanBracketOfMoments (49/200) lo0763 hi0763 accepted0763
def lo0764b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨24,by decide⟩
def lo0764b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨25,by decide⟩
def lo0764 : CheckedMoment :=
  CheckedMoment.ofBessel lo0764b1 lo0764b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0764b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨29,by decide⟩
def hi0764b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨30,by decide⟩
def hi0764 : CheckedMoment :=
  CheckedMoment.ofBessel hi0764b1 hi0764b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0764 : meanBracketCheck (123/500) lo0764 hi0764=true := by decide +kernel
def bracket0764 : MeanBracket := meanBracketOfMoments (123/500) lo0764 hi0764 accepted0764
def lo0765b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨34,by decide⟩
def lo0765b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨35,by decide⟩
def lo0765 : CheckedMoment :=
  CheckedMoment.ofBessel lo0765b1 lo0765b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0765b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨39,by decide⟩
def hi0765b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨40,by decide⟩
def hi0765 : CheckedMoment :=
  CheckedMoment.ofBessel hi0765b1 hi0765b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0765 : meanBracketCheck (247/1000) lo0765 hi0765=true := by decide +kernel
def bracket0765 : MeanBracket := meanBracketOfMoments (247/1000) lo0765 hi0765 accepted0765
def lo0766b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨44,by decide⟩
def lo0766b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨45,by decide⟩
def lo0766 : CheckedMoment :=
  CheckedMoment.ofBessel lo0766b1 lo0766b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0766b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨49,by decide⟩
def hi0766b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨50,by decide⟩
def hi0766 : CheckedMoment :=
  CheckedMoment.ofBessel hi0766b1 hi0766b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0766 : meanBracketCheck (31/125) lo0766 hi0766=true := by decide +kernel
def bracket0766 : MeanBracket := meanBracketOfMoments (31/125) lo0766 hi0766 accepted0766
def lo0767b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨54,by decide⟩
def lo0767b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨55,by decide⟩
def lo0767 : CheckedMoment :=
  CheckedMoment.ofBessel lo0767b1 lo0767b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0767b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨59,by decide⟩
def hi0767b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0119.rows BesselBatch0119.accepted ⟨60,by decide⟩
def hi0767 : CheckedMoment :=
  CheckedMoment.ofBessel hi0767b1 hi0767b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0767 : meanBracketCheck (249/1000) lo0767 hi0767=true := by decide +kernel
def bracket0767 : MeanBracket := meanBracketOfMoments (249/1000) lo0767 hi0767 accepted0767
#print axioms bracket0752
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0047
