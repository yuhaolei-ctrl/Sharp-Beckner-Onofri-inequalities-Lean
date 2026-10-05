import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0145
import BecknerOnofri.EntropyScalarCertificate.Bessel0146
import BecknerOnofri.EntropyScalarCertificate.Bessel0147
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0058
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0928b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨0,by decide⟩
def lo0928b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨1,by decide⟩
def lo0928 : CheckedMoment :=
  CheckedMoment.ofBessel lo0928b1 lo0928b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0928b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨5,by decide⟩
def hi0928b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨6,by decide⟩
def hi0928 : CheckedMoment :=
  CheckedMoment.ofBessel hi0928b1 hi0928b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0928 : meanBracketCheck (41/100) lo0928 hi0928=true := by decide +kernel
def bracket0928 : MeanBracket := meanBracketOfMoments (41/100) lo0928 hi0928 accepted0928
def lo0929b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨10,by decide⟩
def lo0929b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨11,by decide⟩
def lo0929 : CheckedMoment :=
  CheckedMoment.ofBessel lo0929b1 lo0929b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0929b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨15,by decide⟩
def hi0929b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨16,by decide⟩
def hi0929 : CheckedMoment :=
  CheckedMoment.ofBessel hi0929b1 hi0929b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0929 : meanBracketCheck (411/1000) lo0929 hi0929=true := by decide +kernel
def bracket0929 : MeanBracket := meanBracketOfMoments (411/1000) lo0929 hi0929 accepted0929
def lo0930b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨20,by decide⟩
def lo0930b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨21,by decide⟩
def lo0930 : CheckedMoment :=
  CheckedMoment.ofBessel lo0930b1 lo0930b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0930b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨25,by decide⟩
def hi0930b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨26,by decide⟩
def hi0930 : CheckedMoment :=
  CheckedMoment.ofBessel hi0930b1 hi0930b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0930 : meanBracketCheck (103/250) lo0930 hi0930=true := by decide +kernel
def bracket0930 : MeanBracket := meanBracketOfMoments (103/250) lo0930 hi0930 accepted0930
def lo0931b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨30,by decide⟩
def lo0931b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨31,by decide⟩
def lo0931 : CheckedMoment :=
  CheckedMoment.ofBessel lo0931b1 lo0931b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0931b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨35,by decide⟩
def hi0931b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨36,by decide⟩
def hi0931 : CheckedMoment :=
  CheckedMoment.ofBessel hi0931b1 hi0931b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0931 : meanBracketCheck (413/1000) lo0931 hi0931=true := by decide +kernel
def bracket0931 : MeanBracket := meanBracketOfMoments (413/1000) lo0931 hi0931 accepted0931
def lo0932b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨40,by decide⟩
def lo0932b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨41,by decide⟩
def lo0932 : CheckedMoment :=
  CheckedMoment.ofBessel lo0932b1 lo0932b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0932b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨45,by decide⟩
def hi0932b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨46,by decide⟩
def hi0932 : CheckedMoment :=
  CheckedMoment.ofBessel hi0932b1 hi0932b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0932 : meanBracketCheck (207/500) lo0932 hi0932=true := by decide +kernel
def bracket0932 : MeanBracket := meanBracketOfMoments (207/500) lo0932 hi0932 accepted0932
def lo0933b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨50,by decide⟩
def lo0933b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨51,by decide⟩
def lo0933 : CheckedMoment :=
  CheckedMoment.ofBessel lo0933b1 lo0933b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0933b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨55,by decide⟩
def hi0933b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨56,by decide⟩
def hi0933 : CheckedMoment :=
  CheckedMoment.ofBessel hi0933b1 hi0933b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0933 : meanBracketCheck (83/200) lo0933 hi0933=true := by decide +kernel
def bracket0933 : MeanBracket := meanBracketOfMoments (83/200) lo0933 hi0933 accepted0933
def lo0934b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨60,by decide⟩
def lo0934b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨61,by decide⟩
def lo0934 : CheckedMoment :=
  CheckedMoment.ofBessel lo0934b1 lo0934b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0934b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨1,by decide⟩
def hi0934b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨2,by decide⟩
def hi0934 : CheckedMoment :=
  CheckedMoment.ofBessel hi0934b1 hi0934b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0934 : meanBracketCheck (52/125) lo0934 hi0934=true := by decide +kernel
def bracket0934 : MeanBracket := meanBracketOfMoments (52/125) lo0934 hi0934 accepted0934
def lo0935b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨6,by decide⟩
def lo0935b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨7,by decide⟩
def lo0935 : CheckedMoment :=
  CheckedMoment.ofBessel lo0935b1 lo0935b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0935b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨11,by decide⟩
def hi0935b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨12,by decide⟩
def hi0935 : CheckedMoment :=
  CheckedMoment.ofBessel hi0935b1 hi0935b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0935 : meanBracketCheck (417/1000) lo0935 hi0935=true := by decide +kernel
def bracket0935 : MeanBracket := meanBracketOfMoments (417/1000) lo0935 hi0935 accepted0935
def lo0936b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨16,by decide⟩
def lo0936b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨17,by decide⟩
def lo0936 : CheckedMoment :=
  CheckedMoment.ofBessel lo0936b1 lo0936b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0936b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨21,by decide⟩
def hi0936b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨22,by decide⟩
def hi0936 : CheckedMoment :=
  CheckedMoment.ofBessel hi0936b1 hi0936b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0936 : meanBracketCheck (209/500) lo0936 hi0936=true := by decide +kernel
def bracket0936 : MeanBracket := meanBracketOfMoments (209/500) lo0936 hi0936 accepted0936
def lo0937b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨26,by decide⟩
def lo0937b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨27,by decide⟩
def lo0937 : CheckedMoment :=
  CheckedMoment.ofBessel lo0937b1 lo0937b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0937b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨31,by decide⟩
def hi0937b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨32,by decide⟩
def hi0937 : CheckedMoment :=
  CheckedMoment.ofBessel hi0937b1 hi0937b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0937 : meanBracketCheck (419/1000) lo0937 hi0937=true := by decide +kernel
def bracket0937 : MeanBracket := meanBracketOfMoments (419/1000) lo0937 hi0937 accepted0937
def lo0938b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨36,by decide⟩
def lo0938b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨37,by decide⟩
def lo0938 : CheckedMoment :=
  CheckedMoment.ofBessel lo0938b1 lo0938b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0938b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨41,by decide⟩
def hi0938b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨42,by decide⟩
def hi0938 : CheckedMoment :=
  CheckedMoment.ofBessel hi0938b1 hi0938b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0938 : meanBracketCheck (21/50) lo0938 hi0938=true := by decide +kernel
def bracket0938 : MeanBracket := meanBracketOfMoments (21/50) lo0938 hi0938 accepted0938
def lo0939b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨46,by decide⟩
def lo0939b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨47,by decide⟩
def lo0939 : CheckedMoment :=
  CheckedMoment.ofBessel lo0939b1 lo0939b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0939b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨51,by decide⟩
def hi0939b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨52,by decide⟩
def hi0939 : CheckedMoment :=
  CheckedMoment.ofBessel hi0939b1 hi0939b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0939 : meanBracketCheck (421/1000) lo0939 hi0939=true := by decide +kernel
def bracket0939 : MeanBracket := meanBracketOfMoments (421/1000) lo0939 hi0939 accepted0939
def lo0940b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨56,by decide⟩
def lo0940b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨57,by decide⟩
def lo0940 : CheckedMoment :=
  CheckedMoment.ofBessel lo0940b1 lo0940b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0940b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨61,by decide⟩
def hi0940b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0146.rows BesselBatch0146.accepted ⟨62,by decide⟩
def hi0940 : CheckedMoment :=
  CheckedMoment.ofBessel hi0940b1 hi0940b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0940 : meanBracketCheck (211/500) lo0940 hi0940=true := by decide +kernel
def bracket0940 : MeanBracket := meanBracketOfMoments (211/500) lo0940 hi0940 accepted0940
def lo0941b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨2,by decide⟩
def lo0941b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨3,by decide⟩
def lo0941 : CheckedMoment :=
  CheckedMoment.ofBessel lo0941b1 lo0941b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0941b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨7,by decide⟩
def hi0941b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨8,by decide⟩
def hi0941 : CheckedMoment :=
  CheckedMoment.ofBessel hi0941b1 hi0941b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0941 : meanBracketCheck (423/1000) lo0941 hi0941=true := by decide +kernel
def bracket0941 : MeanBracket := meanBracketOfMoments (423/1000) lo0941 hi0941 accepted0941
def lo0942b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨12,by decide⟩
def lo0942b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨13,by decide⟩
def lo0942 : CheckedMoment :=
  CheckedMoment.ofBessel lo0942b1 lo0942b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0942b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨17,by decide⟩
def hi0942b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨18,by decide⟩
def hi0942 : CheckedMoment :=
  CheckedMoment.ofBessel hi0942b1 hi0942b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0942 : meanBracketCheck (53/125) lo0942 hi0942=true := by decide +kernel
def bracket0942 : MeanBracket := meanBracketOfMoments (53/125) lo0942 hi0942 accepted0942
def lo0943b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨22,by decide⟩
def lo0943b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨23,by decide⟩
def lo0943 : CheckedMoment :=
  CheckedMoment.ofBessel lo0943b1 lo0943b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0943b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨27,by decide⟩
def hi0943b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨28,by decide⟩
def hi0943 : CheckedMoment :=
  CheckedMoment.ofBessel hi0943b1 hi0943b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0943 : meanBracketCheck (17/40) lo0943 hi0943=true := by decide +kernel
def bracket0943 : MeanBracket := meanBracketOfMoments (17/40) lo0943 hi0943 accepted0943
#print axioms bracket0928
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0058
