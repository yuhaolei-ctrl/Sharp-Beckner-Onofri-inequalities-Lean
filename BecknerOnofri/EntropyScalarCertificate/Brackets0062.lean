module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0155
public import BecknerOnofri.EntropyScalarCertificate.Bessel0156
public import BecknerOnofri.EntropyScalarCertificate.Bessel0157

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0062
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0992b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨0,by decide⟩
def lo0992b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨1,by decide⟩
def lo0992 : CheckedMoment :=
  CheckedMoment.ofBessel lo0992b1 lo0992b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0992b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨5,by decide⟩
def hi0992b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨6,by decide⟩
def hi0992 : CheckedMoment :=
  CheckedMoment.ofBessel hi0992b1 hi0992b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0992 : meanBracketCheck (237/500) lo0992 hi0992=true := by decide +kernel
def bracket0992 : MeanBracket := meanBracketOfMoments (237/500) lo0992 hi0992 accepted0992
def lo0993b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨10,by decide⟩
def lo0993b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨11,by decide⟩
def lo0993 : CheckedMoment :=
  CheckedMoment.ofBessel lo0993b1 lo0993b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0993b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨15,by decide⟩
def hi0993b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨16,by decide⟩
def hi0993 : CheckedMoment :=
  CheckedMoment.ofBessel hi0993b1 hi0993b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0993 : meanBracketCheck (19/40) lo0993 hi0993=true := by decide +kernel
def bracket0993 : MeanBracket := meanBracketOfMoments (19/40) lo0993 hi0993 accepted0993
def lo0994b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨20,by decide⟩
def lo0994b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨21,by decide⟩
def lo0994 : CheckedMoment :=
  CheckedMoment.ofBessel lo0994b1 lo0994b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0994b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨25,by decide⟩
def hi0994b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨26,by decide⟩
def hi0994 : CheckedMoment :=
  CheckedMoment.ofBessel hi0994b1 hi0994b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0994 : meanBracketCheck (119/250) lo0994 hi0994=true := by decide +kernel
def bracket0994 : MeanBracket := meanBracketOfMoments (119/250) lo0994 hi0994 accepted0994
def lo0995b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨30,by decide⟩
def lo0995b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨31,by decide⟩
def lo0995 : CheckedMoment :=
  CheckedMoment.ofBessel lo0995b1 lo0995b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0995b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨35,by decide⟩
def hi0995b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨36,by decide⟩
def hi0995 : CheckedMoment :=
  CheckedMoment.ofBessel hi0995b1 hi0995b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0995 : meanBracketCheck (477/1000) lo0995 hi0995=true := by decide +kernel
def bracket0995 : MeanBracket := meanBracketOfMoments (477/1000) lo0995 hi0995 accepted0995
def lo0996b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨40,by decide⟩
def lo0996b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨41,by decide⟩
def lo0996 : CheckedMoment :=
  CheckedMoment.ofBessel lo0996b1 lo0996b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0996b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨45,by decide⟩
def hi0996b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨46,by decide⟩
def hi0996 : CheckedMoment :=
  CheckedMoment.ofBessel hi0996b1 hi0996b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0996 : meanBracketCheck (239/500) lo0996 hi0996=true := by decide +kernel
def bracket0996 : MeanBracket := meanBracketOfMoments (239/500) lo0996 hi0996 accepted0996
def lo0997b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨50,by decide⟩
def lo0997b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨51,by decide⟩
def lo0997 : CheckedMoment :=
  CheckedMoment.ofBessel lo0997b1 lo0997b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0997b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨55,by decide⟩
def hi0997b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨56,by decide⟩
def hi0997 : CheckedMoment :=
  CheckedMoment.ofBessel hi0997b1 hi0997b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0997 : meanBracketCheck (479/1000) lo0997 hi0997=true := by decide +kernel
def bracket0997 : MeanBracket := meanBracketOfMoments (479/1000) lo0997 hi0997 accepted0997
def lo0998b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨60,by decide⟩
def lo0998b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0155.rows BesselBatch0155.accepted ⟨61,by decide⟩
def lo0998 : CheckedMoment :=
  CheckedMoment.ofBessel lo0998b1 lo0998b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0998b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨1,by decide⟩
def hi0998b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨2,by decide⟩
def hi0998 : CheckedMoment :=
  CheckedMoment.ofBessel hi0998b1 hi0998b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0998 : meanBracketCheck (12/25) lo0998 hi0998=true := by decide +kernel
def bracket0998 : MeanBracket := meanBracketOfMoments (12/25) lo0998 hi0998 accepted0998
def lo0999b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨6,by decide⟩
def lo0999b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨7,by decide⟩
def lo0999 : CheckedMoment :=
  CheckedMoment.ofBessel lo0999b1 lo0999b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0999b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨11,by decide⟩
def hi0999b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨12,by decide⟩
def hi0999 : CheckedMoment :=
  CheckedMoment.ofBessel hi0999b1 hi0999b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0999 : meanBracketCheck (481/1000) lo0999 hi0999=true := by decide +kernel
def bracket0999 : MeanBracket := meanBracketOfMoments (481/1000) lo0999 hi0999 accepted0999
def lo1000b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨16,by decide⟩
def lo1000b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨17,by decide⟩
def lo1000 : CheckedMoment :=
  CheckedMoment.ofBessel lo1000b1 lo1000b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1000b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨21,by decide⟩
def hi1000b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨22,by decide⟩
def hi1000 : CheckedMoment :=
  CheckedMoment.ofBessel hi1000b1 hi1000b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1000 : meanBracketCheck (241/500) lo1000 hi1000=true := by decide +kernel
def bracket1000 : MeanBracket := meanBracketOfMoments (241/500) lo1000 hi1000 accepted1000
def lo1001b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨26,by decide⟩
def lo1001b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨27,by decide⟩
def lo1001 : CheckedMoment :=
  CheckedMoment.ofBessel lo1001b1 lo1001b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1001b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨31,by decide⟩
def hi1001b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨32,by decide⟩
def hi1001 : CheckedMoment :=
  CheckedMoment.ofBessel hi1001b1 hi1001b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1001 : meanBracketCheck (483/1000) lo1001 hi1001=true := by decide +kernel
def bracket1001 : MeanBracket := meanBracketOfMoments (483/1000) lo1001 hi1001 accepted1001
def lo1002b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨36,by decide⟩
def lo1002b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨37,by decide⟩
def lo1002 : CheckedMoment :=
  CheckedMoment.ofBessel lo1002b1 lo1002b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1002b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨41,by decide⟩
def hi1002b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨42,by decide⟩
def hi1002 : CheckedMoment :=
  CheckedMoment.ofBessel hi1002b1 hi1002b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1002 : meanBracketCheck (121/250) lo1002 hi1002=true := by decide +kernel
def bracket1002 : MeanBracket := meanBracketOfMoments (121/250) lo1002 hi1002 accepted1002
def lo1003b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨46,by decide⟩
def lo1003b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨47,by decide⟩
def lo1003 : CheckedMoment :=
  CheckedMoment.ofBessel lo1003b1 lo1003b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1003b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨51,by decide⟩
def hi1003b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨52,by decide⟩
def hi1003 : CheckedMoment :=
  CheckedMoment.ofBessel hi1003b1 hi1003b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1003 : meanBracketCheck (97/200) lo1003 hi1003=true := by decide +kernel
def bracket1003 : MeanBracket := meanBracketOfMoments (97/200) lo1003 hi1003 accepted1003
def lo1004b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨56,by decide⟩
def lo1004b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨57,by decide⟩
def lo1004 : CheckedMoment :=
  CheckedMoment.ofBessel lo1004b1 lo1004b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1004b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨61,by decide⟩
def hi1004b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨62,by decide⟩
def hi1004 : CheckedMoment :=
  CheckedMoment.ofBessel hi1004b1 hi1004b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1004 : meanBracketCheck (243/500) lo1004 hi1004=true := by decide +kernel
def bracket1004 : MeanBracket := meanBracketOfMoments (243/500) lo1004 hi1004 accepted1004
def lo1005b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨2,by decide⟩
def lo1005b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨3,by decide⟩
def lo1005 : CheckedMoment :=
  CheckedMoment.ofBessel lo1005b1 lo1005b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1005b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨7,by decide⟩
def hi1005b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨8,by decide⟩
def hi1005 : CheckedMoment :=
  CheckedMoment.ofBessel hi1005b1 hi1005b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1005 : meanBracketCheck (487/1000) lo1005 hi1005=true := by decide +kernel
def bracket1005 : MeanBracket := meanBracketOfMoments (487/1000) lo1005 hi1005 accepted1005
def lo1006b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨12,by decide⟩
def lo1006b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨13,by decide⟩
def lo1006 : CheckedMoment :=
  CheckedMoment.ofBessel lo1006b1 lo1006b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1006b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨17,by decide⟩
def hi1006b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨18,by decide⟩
def hi1006 : CheckedMoment :=
  CheckedMoment.ofBessel hi1006b1 hi1006b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1006 : meanBracketCheck (61/125) lo1006 hi1006=true := by decide +kernel
def bracket1006 : MeanBracket := meanBracketOfMoments (61/125) lo1006 hi1006 accepted1006
def lo1007b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨22,by decide⟩
def lo1007b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨23,by decide⟩
def lo1007 : CheckedMoment :=
  CheckedMoment.ofBessel lo1007b1 lo1007b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1007b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨27,by decide⟩
def hi1007b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨28,by decide⟩
def hi1007 : CheckedMoment :=
  CheckedMoment.ofBessel hi1007b1 hi1007b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1007 : meanBracketCheck (489/1000) lo1007 hi1007=true := by decide +kernel
def bracket1007 : MeanBracket := meanBracketOfMoments (489/1000) lo1007 hi1007 accepted1007
#print axioms bracket0992
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0062
