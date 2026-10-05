import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0102
import BecknerOnofri.EntropyScalarCertificate.Bessel0103
import BecknerOnofri.EntropyScalarCertificate.Bessel0104
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0041
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0656b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨32,by decide⟩
def lo0656b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨33,by decide⟩
def lo0656 : CheckedMoment :=
  CheckedMoment.ofBessel lo0656b1 lo0656b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0656b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨37,by decide⟩
def hi0656b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨38,by decide⟩
def hi0656 : CheckedMoment :=
  CheckedMoment.ofBessel hi0656b1 hi0656b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0656 : meanBracketCheck (1877/10000) lo0656 hi0656=true := by decide +kernel
def bracket0656 : MeanBracket := meanBracketOfMoments (1877/10000) lo0656 hi0656 accepted0656
def lo0657b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨42,by decide⟩
def lo0657b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨43,by decide⟩
def lo0657 : CheckedMoment :=
  CheckedMoment.ofBessel lo0657b1 lo0657b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0657b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨47,by decide⟩
def hi0657b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨48,by decide⟩
def hi0657 : CheckedMoment :=
  CheckedMoment.ofBessel hi0657b1 hi0657b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0657 : meanBracketCheck (1879/10000) lo0657 hi0657=true := by decide +kernel
def bracket0657 : MeanBracket := meanBracketOfMoments (1879/10000) lo0657 hi0657 accepted0657
def lo0658b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨52,by decide⟩
def lo0658b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨53,by decide⟩
def lo0658 : CheckedMoment :=
  CheckedMoment.ofBessel lo0658b1 lo0658b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0658b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨57,by decide⟩
def hi0658b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨58,by decide⟩
def hi0658 : CheckedMoment :=
  CheckedMoment.ofBessel hi0658b1 hi0658b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0658 : meanBracketCheck (1881/10000) lo0658 hi0658=true := by decide +kernel
def bracket0658 : MeanBracket := meanBracketOfMoments (1881/10000) lo0658 hi0658 accepted0658
def lo0659b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨62,by decide⟩
def lo0659b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨63,by decide⟩
def lo0659 : CheckedMoment :=
  CheckedMoment.ofBessel lo0659b1 lo0659b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0659b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨3,by decide⟩
def hi0659b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨4,by decide⟩
def hi0659 : CheckedMoment :=
  CheckedMoment.ofBessel hi0659b1 hi0659b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0659 : meanBracketCheck (1883/10000) lo0659 hi0659=true := by decide +kernel
def bracket0659 : MeanBracket := meanBracketOfMoments (1883/10000) lo0659 hi0659 accepted0659
def lo0660b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨8,by decide⟩
def lo0660b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨9,by decide⟩
def lo0660 : CheckedMoment :=
  CheckedMoment.ofBessel lo0660b1 lo0660b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0660b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨13,by decide⟩
def hi0660b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨14,by decide⟩
def hi0660 : CheckedMoment :=
  CheckedMoment.ofBessel hi0660b1 hi0660b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0660 : meanBracketCheck (377/2000) lo0660 hi0660=true := by decide +kernel
def bracket0660 : MeanBracket := meanBracketOfMoments (377/2000) lo0660 hi0660 accepted0660
def lo0661b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨18,by decide⟩
def lo0661b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨19,by decide⟩
def lo0661 : CheckedMoment :=
  CheckedMoment.ofBessel lo0661b1 lo0661b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0661b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨23,by decide⟩
def hi0661b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨24,by decide⟩
def hi0661 : CheckedMoment :=
  CheckedMoment.ofBessel hi0661b1 hi0661b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0661 : meanBracketCheck (1887/10000) lo0661 hi0661=true := by decide +kernel
def bracket0661 : MeanBracket := meanBracketOfMoments (1887/10000) lo0661 hi0661 accepted0661
def lo0662b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨28,by decide⟩
def lo0662b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨29,by decide⟩
def lo0662 : CheckedMoment :=
  CheckedMoment.ofBessel lo0662b1 lo0662b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0662b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨33,by decide⟩
def hi0662b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨34,by decide⟩
def hi0662 : CheckedMoment :=
  CheckedMoment.ofBessel hi0662b1 hi0662b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0662 : meanBracketCheck (1889/10000) lo0662 hi0662=true := by decide +kernel
def bracket0662 : MeanBracket := meanBracketOfMoments (1889/10000) lo0662 hi0662 accepted0662
def lo0663b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨38,by decide⟩
def lo0663b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨39,by decide⟩
def lo0663 : CheckedMoment :=
  CheckedMoment.ofBessel lo0663b1 lo0663b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0663b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨43,by decide⟩
def hi0663b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨44,by decide⟩
def hi0663 : CheckedMoment :=
  CheckedMoment.ofBessel hi0663b1 hi0663b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0663 : meanBracketCheck (1891/10000) lo0663 hi0663=true := by decide +kernel
def bracket0663 : MeanBracket := meanBracketOfMoments (1891/10000) lo0663 hi0663 accepted0663
def lo0664b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨48,by decide⟩
def lo0664b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨49,by decide⟩
def lo0664 : CheckedMoment :=
  CheckedMoment.ofBessel lo0664b1 lo0664b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0664b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨53,by decide⟩
def hi0664b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨54,by decide⟩
def hi0664 : CheckedMoment :=
  CheckedMoment.ofBessel hi0664b1 hi0664b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0664 : meanBracketCheck (1893/10000) lo0664 hi0664=true := by decide +kernel
def bracket0664 : MeanBracket := meanBracketOfMoments (1893/10000) lo0664 hi0664 accepted0664
def lo0665b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨58,by decide⟩
def lo0665b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨59,by decide⟩
def lo0665 : CheckedMoment :=
  CheckedMoment.ofBessel lo0665b1 lo0665b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0665b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨63,by decide⟩
def hi0665b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨0,by decide⟩
def hi0665 : CheckedMoment :=
  CheckedMoment.ofBessel hi0665b1 hi0665b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0665 : meanBracketCheck (379/2000) lo0665 hi0665=true := by decide +kernel
def bracket0665 : MeanBracket := meanBracketOfMoments (379/2000) lo0665 hi0665 accepted0665
def lo0666b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨4,by decide⟩
def lo0666b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨5,by decide⟩
def lo0666 : CheckedMoment :=
  CheckedMoment.ofBessel lo0666b1 lo0666b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0666b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨9,by decide⟩
def hi0666b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨10,by decide⟩
def hi0666 : CheckedMoment :=
  CheckedMoment.ofBessel hi0666b1 hi0666b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0666 : meanBracketCheck (1897/10000) lo0666 hi0666=true := by decide +kernel
def bracket0666 : MeanBracket := meanBracketOfMoments (1897/10000) lo0666 hi0666 accepted0666
def lo0667b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨14,by decide⟩
def lo0667b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨15,by decide⟩
def lo0667 : CheckedMoment :=
  CheckedMoment.ofBessel lo0667b1 lo0667b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0667b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨19,by decide⟩
def hi0667b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨20,by decide⟩
def hi0667 : CheckedMoment :=
  CheckedMoment.ofBessel hi0667b1 hi0667b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0667 : meanBracketCheck (1899/10000) lo0667 hi0667=true := by decide +kernel
def bracket0667 : MeanBracket := meanBracketOfMoments (1899/10000) lo0667 hi0667 accepted0667
def lo0668b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨24,by decide⟩
def lo0668b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨25,by decide⟩
def lo0668 : CheckedMoment :=
  CheckedMoment.ofBessel lo0668b1 lo0668b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0668b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨29,by decide⟩
def hi0668b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨30,by decide⟩
def hi0668 : CheckedMoment :=
  CheckedMoment.ofBessel hi0668b1 hi0668b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0668 : meanBracketCheck (1901/10000) lo0668 hi0668=true := by decide +kernel
def bracket0668 : MeanBracket := meanBracketOfMoments (1901/10000) lo0668 hi0668 accepted0668
def lo0669b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨34,by decide⟩
def lo0669b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨35,by decide⟩
def lo0669 : CheckedMoment :=
  CheckedMoment.ofBessel lo0669b1 lo0669b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0669b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨39,by decide⟩
def hi0669b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨40,by decide⟩
def hi0669 : CheckedMoment :=
  CheckedMoment.ofBessel hi0669b1 hi0669b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0669 : meanBracketCheck (1903/10000) lo0669 hi0669=true := by decide +kernel
def bracket0669 : MeanBracket := meanBracketOfMoments (1903/10000) lo0669 hi0669 accepted0669
def lo0670b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨44,by decide⟩
def lo0670b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨45,by decide⟩
def lo0670 : CheckedMoment :=
  CheckedMoment.ofBessel lo0670b1 lo0670b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0670b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨49,by decide⟩
def hi0670b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨50,by decide⟩
def hi0670 : CheckedMoment :=
  CheckedMoment.ofBessel hi0670b1 hi0670b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0670 : meanBracketCheck (381/2000) lo0670 hi0670=true := by decide +kernel
def bracket0670 : MeanBracket := meanBracketOfMoments (381/2000) lo0670 hi0670 accepted0670
def lo0671b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨54,by decide⟩
def lo0671b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨55,by decide⟩
def lo0671 : CheckedMoment :=
  CheckedMoment.ofBessel lo0671b1 lo0671b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0671b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨59,by decide⟩
def hi0671b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨60,by decide⟩
def hi0671 : CheckedMoment :=
  CheckedMoment.ofBessel hi0671b1 hi0671b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0671 : meanBracketCheck (1907/10000) lo0671 hi0671=true := by decide +kernel
def bracket0671 : MeanBracket := meanBracketOfMoments (1907/10000) lo0671 hi0671 accepted0671
#print axioms bracket0656
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0041
