import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0000
import BecknerOnofri.EntropyScalarCertificate.Bessel0001
import BecknerOnofri.EntropyScalarCertificate.Bessel0002
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0000
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0000b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨0,by decide⟩
def lo0000b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨1,by decide⟩
def lo0000 : CheckedMoment :=
  CheckedMoment.ofBessel lo0000b1 lo0000b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0000b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨5,by decide⟩
def hi0000b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨6,by decide⟩
def hi0000 : CheckedMoment :=
  CheckedMoment.ofBessel hi0000b1 hi0000b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0000 : meanBracketCheck (1/16) lo0000 hi0000=true := by decide +kernel
def bracket0000 : MeanBracket := meanBracketOfMoments (1/16) lo0000 hi0000 accepted0000
def lo0001b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨10,by decide⟩
def lo0001b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨11,by decide⟩
def lo0001 : CheckedMoment :=
  CheckedMoment.ofBessel lo0001b1 lo0001b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0001b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨15,by decide⟩
def hi0001b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨16,by decide⟩
def hi0001 : CheckedMoment :=
  CheckedMoment.ofBessel hi0001b1 hi0001b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0001 : meanBracketCheck (1251/20000) lo0001 hi0001=true := by decide +kernel
def bracket0001 : MeanBracket := meanBracketOfMoments (1251/20000) lo0001 hi0001 accepted0001
def lo0002b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨20,by decide⟩
def lo0002b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨21,by decide⟩
def lo0002 : CheckedMoment :=
  CheckedMoment.ofBessel lo0002b1 lo0002b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0002b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨25,by decide⟩
def hi0002b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨26,by decide⟩
def hi0002 : CheckedMoment :=
  CheckedMoment.ofBessel hi0002b1 hi0002b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0002 : meanBracketCheck (313/5000) lo0002 hi0002=true := by decide +kernel
def bracket0002 : MeanBracket := meanBracketOfMoments (313/5000) lo0002 hi0002 accepted0002
def lo0003b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨30,by decide⟩
def lo0003b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨31,by decide⟩
def lo0003 : CheckedMoment :=
  CheckedMoment.ofBessel lo0003b1 lo0003b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0003b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨35,by decide⟩
def hi0003b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨36,by decide⟩
def hi0003 : CheckedMoment :=
  CheckedMoment.ofBessel hi0003b1 hi0003b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0003 : meanBracketCheck (1253/20000) lo0003 hi0003=true := by decide +kernel
def bracket0003 : MeanBracket := meanBracketOfMoments (1253/20000) lo0003 hi0003 accepted0003
def lo0004b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨40,by decide⟩
def lo0004b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨41,by decide⟩
def lo0004 : CheckedMoment :=
  CheckedMoment.ofBessel lo0004b1 lo0004b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0004b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨45,by decide⟩
def hi0004b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨46,by decide⟩
def hi0004 : CheckedMoment :=
  CheckedMoment.ofBessel hi0004b1 hi0004b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0004 : meanBracketCheck (627/10000) lo0004 hi0004=true := by decide +kernel
def bracket0004 : MeanBracket := meanBracketOfMoments (627/10000) lo0004 hi0004 accepted0004
def lo0005b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨50,by decide⟩
def lo0005b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨51,by decide⟩
def lo0005 : CheckedMoment :=
  CheckedMoment.ofBessel lo0005b1 lo0005b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0005b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨55,by decide⟩
def hi0005b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨56,by decide⟩
def hi0005 : CheckedMoment :=
  CheckedMoment.ofBessel hi0005b1 hi0005b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0005 : meanBracketCheck (251/4000) lo0005 hi0005=true := by decide +kernel
def bracket0005 : MeanBracket := meanBracketOfMoments (251/4000) lo0005 hi0005 accepted0005
def lo0006b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨60,by decide⟩
def lo0006b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨61,by decide⟩
def lo0006 : CheckedMoment :=
  CheckedMoment.ofBessel lo0006b1 lo0006b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0006b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨1,by decide⟩
def hi0006b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨2,by decide⟩
def hi0006 : CheckedMoment :=
  CheckedMoment.ofBessel hi0006b1 hi0006b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0006 : meanBracketCheck (157/2500) lo0006 hi0006=true := by decide +kernel
def bracket0006 : MeanBracket := meanBracketOfMoments (157/2500) lo0006 hi0006 accepted0006
def lo0007b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨6,by decide⟩
def lo0007b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨7,by decide⟩
def lo0007 : CheckedMoment :=
  CheckedMoment.ofBessel lo0007b1 lo0007b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0007b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨11,by decide⟩
def hi0007b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨12,by decide⟩
def hi0007 : CheckedMoment :=
  CheckedMoment.ofBessel hi0007b1 hi0007b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0007 : meanBracketCheck (1257/20000) lo0007 hi0007=true := by decide +kernel
def bracket0007 : MeanBracket := meanBracketOfMoments (1257/20000) lo0007 hi0007 accepted0007
def lo0008b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨16,by decide⟩
def lo0008b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨17,by decide⟩
def lo0008 : CheckedMoment :=
  CheckedMoment.ofBessel lo0008b1 lo0008b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0008b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨21,by decide⟩
def hi0008b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨22,by decide⟩
def hi0008 : CheckedMoment :=
  CheckedMoment.ofBessel hi0008b1 hi0008b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0008 : meanBracketCheck (629/10000) lo0008 hi0008=true := by decide +kernel
def bracket0008 : MeanBracket := meanBracketOfMoments (629/10000) lo0008 hi0008 accepted0008
def lo0009b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨26,by decide⟩
def lo0009b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨27,by decide⟩
def lo0009 : CheckedMoment :=
  CheckedMoment.ofBessel lo0009b1 lo0009b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0009b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨31,by decide⟩
def hi0009b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨32,by decide⟩
def hi0009 : CheckedMoment :=
  CheckedMoment.ofBessel hi0009b1 hi0009b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0009 : meanBracketCheck (1259/20000) lo0009 hi0009=true := by decide +kernel
def bracket0009 : MeanBracket := meanBracketOfMoments (1259/20000) lo0009 hi0009 accepted0009
def lo0010b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨36,by decide⟩
def lo0010b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨37,by decide⟩
def lo0010 : CheckedMoment :=
  CheckedMoment.ofBessel lo0010b1 lo0010b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0010b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨41,by decide⟩
def hi0010b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨42,by decide⟩
def hi0010 : CheckedMoment :=
  CheckedMoment.ofBessel hi0010b1 hi0010b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0010 : meanBracketCheck (63/1000) lo0010 hi0010=true := by decide +kernel
def bracket0010 : MeanBracket := meanBracketOfMoments (63/1000) lo0010 hi0010 accepted0010
def lo0011b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨46,by decide⟩
def lo0011b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨47,by decide⟩
def lo0011 : CheckedMoment :=
  CheckedMoment.ofBessel lo0011b1 lo0011b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0011b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨51,by decide⟩
def hi0011b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨52,by decide⟩
def hi0011 : CheckedMoment :=
  CheckedMoment.ofBessel hi0011b1 hi0011b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0011 : meanBracketCheck (1261/20000) lo0011 hi0011=true := by decide +kernel
def bracket0011 : MeanBracket := meanBracketOfMoments (1261/20000) lo0011 hi0011 accepted0011
def lo0012b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨56,by decide⟩
def lo0012b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨57,by decide⟩
def lo0012 : CheckedMoment :=
  CheckedMoment.ofBessel lo0012b1 lo0012b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0012b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨61,by decide⟩
def hi0012b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨62,by decide⟩
def hi0012 : CheckedMoment :=
  CheckedMoment.ofBessel hi0012b1 hi0012b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0012 : meanBracketCheck (631/10000) lo0012 hi0012=true := by decide +kernel
def bracket0012 : MeanBracket := meanBracketOfMoments (631/10000) lo0012 hi0012 accepted0012
def lo0013b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨2,by decide⟩
def lo0013b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨3,by decide⟩
def lo0013 : CheckedMoment :=
  CheckedMoment.ofBessel lo0013b1 lo0013b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0013b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨7,by decide⟩
def hi0013b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨8,by decide⟩
def hi0013 : CheckedMoment :=
  CheckedMoment.ofBessel hi0013b1 hi0013b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0013 : meanBracketCheck (1263/20000) lo0013 hi0013=true := by decide +kernel
def bracket0013 : MeanBracket := meanBracketOfMoments (1263/20000) lo0013 hi0013 accepted0013
def lo0014b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨12,by decide⟩
def lo0014b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨13,by decide⟩
def lo0014 : CheckedMoment :=
  CheckedMoment.ofBessel lo0014b1 lo0014b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0014b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨17,by decide⟩
def hi0014b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨18,by decide⟩
def hi0014 : CheckedMoment :=
  CheckedMoment.ofBessel hi0014b1 hi0014b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0014 : meanBracketCheck (79/1250) lo0014 hi0014=true := by decide +kernel
def bracket0014 : MeanBracket := meanBracketOfMoments (79/1250) lo0014 hi0014 accepted0014
def lo0015b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨22,by decide⟩
def lo0015b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨23,by decide⟩
def lo0015 : CheckedMoment :=
  CheckedMoment.ofBessel lo0015b1 lo0015b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0015b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨27,by decide⟩
def hi0015b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨28,by decide⟩
def hi0015 : CheckedMoment :=
  CheckedMoment.ofBessel hi0015b1 hi0015b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0015 : meanBracketCheck (253/4000) lo0015 hi0015=true := by decide +kernel
def bracket0015 : MeanBracket := meanBracketOfMoments (253/4000) lo0015 hi0015 accepted0015
#print axioms bracket0000
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0000
