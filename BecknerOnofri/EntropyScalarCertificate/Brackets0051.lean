import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0127
import BecknerOnofri.EntropyScalarCertificate.Bessel0128
import BecknerOnofri.EntropyScalarCertificate.Bessel0129
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0051
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0816b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨32,by decide⟩
def lo0816b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨33,by decide⟩
def lo0816 : CheckedMoment :=
  CheckedMoment.ofBessel lo0816b1 lo0816b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0816b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨37,by decide⟩
def hi0816b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨38,by decide⟩
def hi0816 : CheckedMoment :=
  CheckedMoment.ofBessel hi0816b1 hi0816b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0816 : meanBracketCheck (149/500) lo0816 hi0816=true := by decide +kernel
def bracket0816 : MeanBracket := meanBracketOfMoments (149/500) lo0816 hi0816 accepted0816
def lo0817b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨42,by decide⟩
def lo0817b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨43,by decide⟩
def lo0817 : CheckedMoment :=
  CheckedMoment.ofBessel lo0817b1 lo0817b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0817b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨47,by decide⟩
def hi0817b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨48,by decide⟩
def hi0817 : CheckedMoment :=
  CheckedMoment.ofBessel hi0817b1 hi0817b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0817 : meanBracketCheck (299/1000) lo0817 hi0817=true := by decide +kernel
def bracket0817 : MeanBracket := meanBracketOfMoments (299/1000) lo0817 hi0817 accepted0817
def lo0818b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨52,by decide⟩
def lo0818b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨53,by decide⟩
def lo0818 : CheckedMoment :=
  CheckedMoment.ofBessel lo0818b1 lo0818b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0818b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨57,by decide⟩
def hi0818b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨58,by decide⟩
def hi0818 : CheckedMoment :=
  CheckedMoment.ofBessel hi0818b1 hi0818b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0818 : meanBracketCheck (3/10) lo0818 hi0818=true := by decide +kernel
def bracket0818 : MeanBracket := meanBracketOfMoments (3/10) lo0818 hi0818 accepted0818
def lo0819b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨62,by decide⟩
def lo0819b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨63,by decide⟩
def lo0819 : CheckedMoment :=
  CheckedMoment.ofBessel lo0819b1 lo0819b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0819b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨3,by decide⟩
def hi0819b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨4,by decide⟩
def hi0819 : CheckedMoment :=
  CheckedMoment.ofBessel hi0819b1 hi0819b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0819 : meanBracketCheck (301/1000) lo0819 hi0819=true := by decide +kernel
def bracket0819 : MeanBracket := meanBracketOfMoments (301/1000) lo0819 hi0819 accepted0819
def lo0820b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨8,by decide⟩
def lo0820b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨9,by decide⟩
def lo0820 : CheckedMoment :=
  CheckedMoment.ofBessel lo0820b1 lo0820b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0820b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨13,by decide⟩
def hi0820b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨14,by decide⟩
def hi0820 : CheckedMoment :=
  CheckedMoment.ofBessel hi0820b1 hi0820b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0820 : meanBracketCheck (151/500) lo0820 hi0820=true := by decide +kernel
def bracket0820 : MeanBracket := meanBracketOfMoments (151/500) lo0820 hi0820 accepted0820
def lo0821b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨18,by decide⟩
def lo0821b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨19,by decide⟩
def lo0821 : CheckedMoment :=
  CheckedMoment.ofBessel lo0821b1 lo0821b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0821b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨23,by decide⟩
def hi0821b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨24,by decide⟩
def hi0821 : CheckedMoment :=
  CheckedMoment.ofBessel hi0821b1 hi0821b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0821 : meanBracketCheck (303/1000) lo0821 hi0821=true := by decide +kernel
def bracket0821 : MeanBracket := meanBracketOfMoments (303/1000) lo0821 hi0821 accepted0821
def lo0822b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨28,by decide⟩
def lo0822b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨29,by decide⟩
def lo0822 : CheckedMoment :=
  CheckedMoment.ofBessel lo0822b1 lo0822b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0822b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨33,by decide⟩
def hi0822b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨34,by decide⟩
def hi0822 : CheckedMoment :=
  CheckedMoment.ofBessel hi0822b1 hi0822b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0822 : meanBracketCheck (38/125) lo0822 hi0822=true := by decide +kernel
def bracket0822 : MeanBracket := meanBracketOfMoments (38/125) lo0822 hi0822 accepted0822
def lo0823b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨38,by decide⟩
def lo0823b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨39,by decide⟩
def lo0823 : CheckedMoment :=
  CheckedMoment.ofBessel lo0823b1 lo0823b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0823b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨43,by decide⟩
def hi0823b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨44,by decide⟩
def hi0823 : CheckedMoment :=
  CheckedMoment.ofBessel hi0823b1 hi0823b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0823 : meanBracketCheck (61/200) lo0823 hi0823=true := by decide +kernel
def bracket0823 : MeanBracket := meanBracketOfMoments (61/200) lo0823 hi0823 accepted0823
def lo0824b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨48,by decide⟩
def lo0824b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨49,by decide⟩
def lo0824 : CheckedMoment :=
  CheckedMoment.ofBessel lo0824b1 lo0824b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0824b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨53,by decide⟩
def hi0824b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨54,by decide⟩
def hi0824 : CheckedMoment :=
  CheckedMoment.ofBessel hi0824b1 hi0824b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0824 : meanBracketCheck (153/500) lo0824 hi0824=true := by decide +kernel
def bracket0824 : MeanBracket := meanBracketOfMoments (153/500) lo0824 hi0824 accepted0824
def lo0825b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨58,by decide⟩
def lo0825b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨59,by decide⟩
def lo0825 : CheckedMoment :=
  CheckedMoment.ofBessel lo0825b1 lo0825b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0825b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨63,by decide⟩
def hi0825b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨0,by decide⟩
def hi0825 : CheckedMoment :=
  CheckedMoment.ofBessel hi0825b1 hi0825b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0825 : meanBracketCheck (307/1000) lo0825 hi0825=true := by decide +kernel
def bracket0825 : MeanBracket := meanBracketOfMoments (307/1000) lo0825 hi0825 accepted0825
def lo0826b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨4,by decide⟩
def lo0826b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨5,by decide⟩
def lo0826 : CheckedMoment :=
  CheckedMoment.ofBessel lo0826b1 lo0826b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0826b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨9,by decide⟩
def hi0826b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨10,by decide⟩
def hi0826 : CheckedMoment :=
  CheckedMoment.ofBessel hi0826b1 hi0826b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0826 : meanBracketCheck (77/250) lo0826 hi0826=true := by decide +kernel
def bracket0826 : MeanBracket := meanBracketOfMoments (77/250) lo0826 hi0826 accepted0826
def lo0827b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨14,by decide⟩
def lo0827b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨15,by decide⟩
def lo0827 : CheckedMoment :=
  CheckedMoment.ofBessel lo0827b1 lo0827b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0827b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨19,by decide⟩
def hi0827b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨20,by decide⟩
def hi0827 : CheckedMoment :=
  CheckedMoment.ofBessel hi0827b1 hi0827b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0827 : meanBracketCheck (309/1000) lo0827 hi0827=true := by decide +kernel
def bracket0827 : MeanBracket := meanBracketOfMoments (309/1000) lo0827 hi0827 accepted0827
def lo0828b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨24,by decide⟩
def lo0828b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨25,by decide⟩
def lo0828 : CheckedMoment :=
  CheckedMoment.ofBessel lo0828b1 lo0828b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0828b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨29,by decide⟩
def hi0828b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨30,by decide⟩
def hi0828 : CheckedMoment :=
  CheckedMoment.ofBessel hi0828b1 hi0828b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0828 : meanBracketCheck (31/100) lo0828 hi0828=true := by decide +kernel
def bracket0828 : MeanBracket := meanBracketOfMoments (31/100) lo0828 hi0828 accepted0828
def lo0829b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨34,by decide⟩
def lo0829b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨35,by decide⟩
def lo0829 : CheckedMoment :=
  CheckedMoment.ofBessel lo0829b1 lo0829b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0829b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨39,by decide⟩
def hi0829b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨40,by decide⟩
def hi0829 : CheckedMoment :=
  CheckedMoment.ofBessel hi0829b1 hi0829b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0829 : meanBracketCheck (311/1000) lo0829 hi0829=true := by decide +kernel
def bracket0829 : MeanBracket := meanBracketOfMoments (311/1000) lo0829 hi0829 accepted0829
def lo0830b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨44,by decide⟩
def lo0830b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨45,by decide⟩
def lo0830 : CheckedMoment :=
  CheckedMoment.ofBessel lo0830b1 lo0830b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0830b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨49,by decide⟩
def hi0830b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨50,by decide⟩
def hi0830 : CheckedMoment :=
  CheckedMoment.ofBessel hi0830b1 hi0830b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0830 : meanBracketCheck (39/125) lo0830 hi0830=true := by decide +kernel
def bracket0830 : MeanBracket := meanBracketOfMoments (39/125) lo0830 hi0830 accepted0830
def lo0831b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨54,by decide⟩
def lo0831b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨55,by decide⟩
def lo0831 : CheckedMoment :=
  CheckedMoment.ofBessel lo0831b1 lo0831b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0831b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨59,by decide⟩
def hi0831b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨60,by decide⟩
def hi0831 : CheckedMoment :=
  CheckedMoment.ofBessel hi0831b1 hi0831b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0831 : meanBracketCheck (313/1000) lo0831 hi0831=true := by decide +kernel
def bracket0831 : MeanBracket := meanBracketOfMoments (313/1000) lo0831 hi0831 accepted0831
#print axioms bracket0816
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0051
