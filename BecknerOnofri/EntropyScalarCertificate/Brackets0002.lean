import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0005
import BecknerOnofri.EntropyScalarCertificate.Bessel0006
import BecknerOnofri.EntropyScalarCertificate.Bessel0007
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0002
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0032b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨0,by decide⟩
def lo0032b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨1,by decide⟩
def lo0032 : CheckedMoment :=
  CheckedMoment.ofBessel lo0032b1 lo0032b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0032b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨5,by decide⟩
def hi0032b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨6,by decide⟩
def hi0032 : CheckedMoment :=
  CheckedMoment.ofBessel hi0032b1 hi0032b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0032 : meanBracketCheck (641/10000) lo0032 hi0032=true := by decide +kernel
def bracket0032 : MeanBracket := meanBracketOfMoments (641/10000) lo0032 hi0032 accepted0032
def lo0033b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨10,by decide⟩
def lo0033b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨11,by decide⟩
def lo0033 : CheckedMoment :=
  CheckedMoment.ofBessel lo0033b1 lo0033b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0033b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨15,by decide⟩
def hi0033b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨16,by decide⟩
def hi0033 : CheckedMoment :=
  CheckedMoment.ofBessel hi0033b1 hi0033b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0033 : meanBracketCheck (1283/20000) lo0033 hi0033=true := by decide +kernel
def bracket0033 : MeanBracket := meanBracketOfMoments (1283/20000) lo0033 hi0033 accepted0033
def lo0034b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨20,by decide⟩
def lo0034b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨21,by decide⟩
def lo0034 : CheckedMoment :=
  CheckedMoment.ofBessel lo0034b1 lo0034b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0034b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨25,by decide⟩
def hi0034b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨26,by decide⟩
def hi0034 : CheckedMoment :=
  CheckedMoment.ofBessel hi0034b1 hi0034b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0034 : meanBracketCheck (321/5000) lo0034 hi0034=true := by decide +kernel
def bracket0034 : MeanBracket := meanBracketOfMoments (321/5000) lo0034 hi0034 accepted0034
def lo0035b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨30,by decide⟩
def lo0035b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨31,by decide⟩
def lo0035 : CheckedMoment :=
  CheckedMoment.ofBessel lo0035b1 lo0035b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0035b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨35,by decide⟩
def hi0035b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨36,by decide⟩
def hi0035 : CheckedMoment :=
  CheckedMoment.ofBessel hi0035b1 hi0035b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0035 : meanBracketCheck (257/4000) lo0035 hi0035=true := by decide +kernel
def bracket0035 : MeanBracket := meanBracketOfMoments (257/4000) lo0035 hi0035 accepted0035
def lo0036b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨40,by decide⟩
def lo0036b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨41,by decide⟩
def lo0036 : CheckedMoment :=
  CheckedMoment.ofBessel lo0036b1 lo0036b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0036b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨45,by decide⟩
def hi0036b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨46,by decide⟩
def hi0036 : CheckedMoment :=
  CheckedMoment.ofBessel hi0036b1 hi0036b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0036 : meanBracketCheck (643/10000) lo0036 hi0036=true := by decide +kernel
def bracket0036 : MeanBracket := meanBracketOfMoments (643/10000) lo0036 hi0036 accepted0036
def lo0037b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨50,by decide⟩
def lo0037b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨51,by decide⟩
def lo0037 : CheckedMoment :=
  CheckedMoment.ofBessel lo0037b1 lo0037b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0037b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨55,by decide⟩
def hi0037b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨56,by decide⟩
def hi0037 : CheckedMoment :=
  CheckedMoment.ofBessel hi0037b1 hi0037b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0037 : meanBracketCheck (1287/20000) lo0037 hi0037=true := by decide +kernel
def bracket0037 : MeanBracket := meanBracketOfMoments (1287/20000) lo0037 hi0037 accepted0037
def lo0038b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨60,by decide⟩
def lo0038b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨61,by decide⟩
def lo0038 : CheckedMoment :=
  CheckedMoment.ofBessel lo0038b1 lo0038b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0038b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨1,by decide⟩
def hi0038b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨2,by decide⟩
def hi0038 : CheckedMoment :=
  CheckedMoment.ofBessel hi0038b1 hi0038b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0038 : meanBracketCheck (161/2500) lo0038 hi0038=true := by decide +kernel
def bracket0038 : MeanBracket := meanBracketOfMoments (161/2500) lo0038 hi0038 accepted0038
def lo0039b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨6,by decide⟩
def lo0039b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨7,by decide⟩
def lo0039 : CheckedMoment :=
  CheckedMoment.ofBessel lo0039b1 lo0039b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0039b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨11,by decide⟩
def hi0039b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨12,by decide⟩
def hi0039 : CheckedMoment :=
  CheckedMoment.ofBessel hi0039b1 hi0039b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0039 : meanBracketCheck (1289/20000) lo0039 hi0039=true := by decide +kernel
def bracket0039 : MeanBracket := meanBracketOfMoments (1289/20000) lo0039 hi0039 accepted0039
def lo0040b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨16,by decide⟩
def lo0040b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨17,by decide⟩
def lo0040 : CheckedMoment :=
  CheckedMoment.ofBessel lo0040b1 lo0040b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0040b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨21,by decide⟩
def hi0040b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨22,by decide⟩
def hi0040 : CheckedMoment :=
  CheckedMoment.ofBessel hi0040b1 hi0040b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0040 : meanBracketCheck (129/2000) lo0040 hi0040=true := by decide +kernel
def bracket0040 : MeanBracket := meanBracketOfMoments (129/2000) lo0040 hi0040 accepted0040
def lo0041b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨26,by decide⟩
def lo0041b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨27,by decide⟩
def lo0041 : CheckedMoment :=
  CheckedMoment.ofBessel lo0041b1 lo0041b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0041b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨31,by decide⟩
def hi0041b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨32,by decide⟩
def hi0041 : CheckedMoment :=
  CheckedMoment.ofBessel hi0041b1 hi0041b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0041 : meanBracketCheck (647/10000) lo0041 hi0041=true := by decide +kernel
def bracket0041 : MeanBracket := meanBracketOfMoments (647/10000) lo0041 hi0041 accepted0041
def lo0042b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨36,by decide⟩
def lo0042b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨37,by decide⟩
def lo0042 : CheckedMoment :=
  CheckedMoment.ofBessel lo0042b1 lo0042b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0042b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨41,by decide⟩
def hi0042b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨42,by decide⟩
def hi0042 : CheckedMoment :=
  CheckedMoment.ofBessel hi0042b1 hi0042b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0042 : meanBracketCheck (649/10000) lo0042 hi0042=true := by decide +kernel
def bracket0042 : MeanBracket := meanBracketOfMoments (649/10000) lo0042 hi0042 accepted0042
def lo0043b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨46,by decide⟩
def lo0043b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨47,by decide⟩
def lo0043 : CheckedMoment :=
  CheckedMoment.ofBessel lo0043b1 lo0043b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0043b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨51,by decide⟩
def hi0043b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨52,by decide⟩
def hi0043 : CheckedMoment :=
  CheckedMoment.ofBessel hi0043b1 hi0043b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0043 : meanBracketCheck (651/10000) lo0043 hi0043=true := by decide +kernel
def bracket0043 : MeanBracket := meanBracketOfMoments (651/10000) lo0043 hi0043 accepted0043
def lo0044b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨56,by decide⟩
def lo0044b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨57,by decide⟩
def lo0044 : CheckedMoment :=
  CheckedMoment.ofBessel lo0044b1 lo0044b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0044b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨61,by decide⟩
def hi0044b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨62,by decide⟩
def hi0044 : CheckedMoment :=
  CheckedMoment.ofBessel hi0044b1 hi0044b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0044 : meanBracketCheck (653/10000) lo0044 hi0044=true := by decide +kernel
def bracket0044 : MeanBracket := meanBracketOfMoments (653/10000) lo0044 hi0044 accepted0044
def lo0045b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨2,by decide⟩
def lo0045b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨3,by decide⟩
def lo0045 : CheckedMoment :=
  CheckedMoment.ofBessel lo0045b1 lo0045b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0045b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨7,by decide⟩
def hi0045b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨8,by decide⟩
def hi0045 : CheckedMoment :=
  CheckedMoment.ofBessel hi0045b1 hi0045b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0045 : meanBracketCheck (131/2000) lo0045 hi0045=true := by decide +kernel
def bracket0045 : MeanBracket := meanBracketOfMoments (131/2000) lo0045 hi0045 accepted0045
def lo0046b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨12,by decide⟩
def lo0046b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨13,by decide⟩
def lo0046 : CheckedMoment :=
  CheckedMoment.ofBessel lo0046b1 lo0046b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0046b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨17,by decide⟩
def hi0046b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨18,by decide⟩
def hi0046 : CheckedMoment :=
  CheckedMoment.ofBessel hi0046b1 hi0046b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0046 : meanBracketCheck (657/10000) lo0046 hi0046=true := by decide +kernel
def bracket0046 : MeanBracket := meanBracketOfMoments (657/10000) lo0046 hi0046 accepted0046
def lo0047b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨22,by decide⟩
def lo0047b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨23,by decide⟩
def lo0047 : CheckedMoment :=
  CheckedMoment.ofBessel lo0047b1 lo0047b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0047b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨27,by decide⟩
def hi0047b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨28,by decide⟩
def hi0047 : CheckedMoment :=
  CheckedMoment.ofBessel hi0047b1 hi0047b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0047 : meanBracketCheck (659/10000) lo0047 hi0047=true := by decide +kernel
def bracket0047 : MeanBracket := meanBracketOfMoments (659/10000) lo0047 hi0047 accepted0047
#print axioms bracket0032
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0002
