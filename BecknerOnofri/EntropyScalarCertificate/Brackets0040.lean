import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0100
import BecknerOnofri.EntropyScalarCertificate.Bessel0101
import BecknerOnofri.EntropyScalarCertificate.Bessel0102
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0040
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0640b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨0,by decide⟩
def lo0640b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨1,by decide⟩
def lo0640 : CheckedMoment :=
  CheckedMoment.ofBessel lo0640b1 lo0640b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0640b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨5,by decide⟩
def hi0640b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨6,by decide⟩
def hi0640 : CheckedMoment :=
  CheckedMoment.ofBessel hi0640b1 hi0640b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0640 : meanBracketCheck (369/2000) lo0640 hi0640=true := by decide +kernel
def bracket0640 : MeanBracket := meanBracketOfMoments (369/2000) lo0640 hi0640 accepted0640
def lo0641b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨10,by decide⟩
def lo0641b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨11,by decide⟩
def lo0641 : CheckedMoment :=
  CheckedMoment.ofBessel lo0641b1 lo0641b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0641b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨15,by decide⟩
def hi0641b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨16,by decide⟩
def hi0641 : CheckedMoment :=
  CheckedMoment.ofBessel hi0641b1 hi0641b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0641 : meanBracketCheck (1847/10000) lo0641 hi0641=true := by decide +kernel
def bracket0641 : MeanBracket := meanBracketOfMoments (1847/10000) lo0641 hi0641 accepted0641
def lo0642b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨20,by decide⟩
def lo0642b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨21,by decide⟩
def lo0642 : CheckedMoment :=
  CheckedMoment.ofBessel lo0642b1 lo0642b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0642b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨25,by decide⟩
def hi0642b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨26,by decide⟩
def hi0642 : CheckedMoment :=
  CheckedMoment.ofBessel hi0642b1 hi0642b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0642 : meanBracketCheck (1849/10000) lo0642 hi0642=true := by decide +kernel
def bracket0642 : MeanBracket := meanBracketOfMoments (1849/10000) lo0642 hi0642 accepted0642
def lo0643b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨30,by decide⟩
def lo0643b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨31,by decide⟩
def lo0643 : CheckedMoment :=
  CheckedMoment.ofBessel lo0643b1 lo0643b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0643b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨35,by decide⟩
def hi0643b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨36,by decide⟩
def hi0643 : CheckedMoment :=
  CheckedMoment.ofBessel hi0643b1 hi0643b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0643 : meanBracketCheck (1851/10000) lo0643 hi0643=true := by decide +kernel
def bracket0643 : MeanBracket := meanBracketOfMoments (1851/10000) lo0643 hi0643 accepted0643
def lo0644b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨40,by decide⟩
def lo0644b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨41,by decide⟩
def lo0644 : CheckedMoment :=
  CheckedMoment.ofBessel lo0644b1 lo0644b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0644b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨45,by decide⟩
def hi0644b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨46,by decide⟩
def hi0644 : CheckedMoment :=
  CheckedMoment.ofBessel hi0644b1 hi0644b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0644 : meanBracketCheck (1853/10000) lo0644 hi0644=true := by decide +kernel
def bracket0644 : MeanBracket := meanBracketOfMoments (1853/10000) lo0644 hi0644 accepted0644
def lo0645b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨50,by decide⟩
def lo0645b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨51,by decide⟩
def lo0645 : CheckedMoment :=
  CheckedMoment.ofBessel lo0645b1 lo0645b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0645b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨55,by decide⟩
def hi0645b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨56,by decide⟩
def hi0645 : CheckedMoment :=
  CheckedMoment.ofBessel hi0645b1 hi0645b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0645 : meanBracketCheck (371/2000) lo0645 hi0645=true := by decide +kernel
def bracket0645 : MeanBracket := meanBracketOfMoments (371/2000) lo0645 hi0645 accepted0645
def lo0646b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨60,by decide⟩
def lo0646b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨61,by decide⟩
def lo0646 : CheckedMoment :=
  CheckedMoment.ofBessel lo0646b1 lo0646b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0646b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨1,by decide⟩
def hi0646b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨2,by decide⟩
def hi0646 : CheckedMoment :=
  CheckedMoment.ofBessel hi0646b1 hi0646b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0646 : meanBracketCheck (1857/10000) lo0646 hi0646=true := by decide +kernel
def bracket0646 : MeanBracket := meanBracketOfMoments (1857/10000) lo0646 hi0646 accepted0646
def lo0647b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨6,by decide⟩
def lo0647b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨7,by decide⟩
def lo0647 : CheckedMoment :=
  CheckedMoment.ofBessel lo0647b1 lo0647b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0647b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨11,by decide⟩
def hi0647b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨12,by decide⟩
def hi0647 : CheckedMoment :=
  CheckedMoment.ofBessel hi0647b1 hi0647b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0647 : meanBracketCheck (1859/10000) lo0647 hi0647=true := by decide +kernel
def bracket0647 : MeanBracket := meanBracketOfMoments (1859/10000) lo0647 hi0647 accepted0647
def lo0648b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨16,by decide⟩
def lo0648b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨17,by decide⟩
def lo0648 : CheckedMoment :=
  CheckedMoment.ofBessel lo0648b1 lo0648b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0648b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨21,by decide⟩
def hi0648b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨22,by decide⟩
def hi0648 : CheckedMoment :=
  CheckedMoment.ofBessel hi0648b1 hi0648b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0648 : meanBracketCheck (1861/10000) lo0648 hi0648=true := by decide +kernel
def bracket0648 : MeanBracket := meanBracketOfMoments (1861/10000) lo0648 hi0648 accepted0648
def lo0649b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨26,by decide⟩
def lo0649b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨27,by decide⟩
def lo0649 : CheckedMoment :=
  CheckedMoment.ofBessel lo0649b1 lo0649b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0649b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨31,by decide⟩
def hi0649b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨32,by decide⟩
def hi0649 : CheckedMoment :=
  CheckedMoment.ofBessel hi0649b1 hi0649b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0649 : meanBracketCheck (1863/10000) lo0649 hi0649=true := by decide +kernel
def bracket0649 : MeanBracket := meanBracketOfMoments (1863/10000) lo0649 hi0649 accepted0649
def lo0650b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨36,by decide⟩
def lo0650b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨37,by decide⟩
def lo0650 : CheckedMoment :=
  CheckedMoment.ofBessel lo0650b1 lo0650b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0650b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨41,by decide⟩
def hi0650b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨42,by decide⟩
def hi0650 : CheckedMoment :=
  CheckedMoment.ofBessel hi0650b1 hi0650b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0650 : meanBracketCheck (373/2000) lo0650 hi0650=true := by decide +kernel
def bracket0650 : MeanBracket := meanBracketOfMoments (373/2000) lo0650 hi0650 accepted0650
def lo0651b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨46,by decide⟩
def lo0651b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨47,by decide⟩
def lo0651 : CheckedMoment :=
  CheckedMoment.ofBessel lo0651b1 lo0651b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0651b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨51,by decide⟩
def hi0651b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨52,by decide⟩
def hi0651 : CheckedMoment :=
  CheckedMoment.ofBessel hi0651b1 hi0651b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0651 : meanBracketCheck (1867/10000) lo0651 hi0651=true := by decide +kernel
def bracket0651 : MeanBracket := meanBracketOfMoments (1867/10000) lo0651 hi0651 accepted0651
def lo0652b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨56,by decide⟩
def lo0652b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨57,by decide⟩
def lo0652 : CheckedMoment :=
  CheckedMoment.ofBessel lo0652b1 lo0652b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0652b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨61,by decide⟩
def hi0652b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨62,by decide⟩
def hi0652 : CheckedMoment :=
  CheckedMoment.ofBessel hi0652b1 hi0652b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0652 : meanBracketCheck (1869/10000) lo0652 hi0652=true := by decide +kernel
def bracket0652 : MeanBracket := meanBracketOfMoments (1869/10000) lo0652 hi0652 accepted0652
def lo0653b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨2,by decide⟩
def lo0653b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨3,by decide⟩
def lo0653 : CheckedMoment :=
  CheckedMoment.ofBessel lo0653b1 lo0653b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0653b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨7,by decide⟩
def hi0653b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨8,by decide⟩
def hi0653 : CheckedMoment :=
  CheckedMoment.ofBessel hi0653b1 hi0653b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0653 : meanBracketCheck (1871/10000) lo0653 hi0653=true := by decide +kernel
def bracket0653 : MeanBracket := meanBracketOfMoments (1871/10000) lo0653 hi0653 accepted0653
def lo0654b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨12,by decide⟩
def lo0654b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨13,by decide⟩
def lo0654 : CheckedMoment :=
  CheckedMoment.ofBessel lo0654b1 lo0654b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0654b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨17,by decide⟩
def hi0654b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨18,by decide⟩
def hi0654 : CheckedMoment :=
  CheckedMoment.ofBessel hi0654b1 hi0654b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0654 : meanBracketCheck (1873/10000) lo0654 hi0654=true := by decide +kernel
def bracket0654 : MeanBracket := meanBracketOfMoments (1873/10000) lo0654 hi0654 accepted0654
def lo0655b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨22,by decide⟩
def lo0655b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨23,by decide⟩
def lo0655 : CheckedMoment :=
  CheckedMoment.ofBessel lo0655b1 lo0655b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0655b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨27,by decide⟩
def hi0655b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0102.rows BesselBatch0102.accepted ⟨28,by decide⟩
def hi0655 : CheckedMoment :=
  CheckedMoment.ofBessel hi0655b1 hi0655b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0655 : meanBracketCheck (3/16) lo0655 hi0655=true := by decide +kernel
def bracket0655 : MeanBracket := meanBracketOfMoments (3/16) lo0655 hi0655 accepted0655
#print axioms bracket0640
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0040
