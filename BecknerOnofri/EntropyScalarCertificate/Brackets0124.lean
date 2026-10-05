module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0310
public import BecknerOnofri.EntropyScalarCertificate.Bessel0311
public import BecknerOnofri.EntropyScalarCertificate.Bessel0312

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0124
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1984b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨0,by decide⟩
def lo1984b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨1,by decide⟩
def lo1984 : CheckedMoment :=
  CheckedMoment.ofBessel lo1984b1 lo1984b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1984b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨5,by decide⟩
def hi1984b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨6,by decide⟩
def hi1984 : CheckedMoment :=
  CheckedMoment.ofBessel hi1984b1 hi1984b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1984 : meanBracketCheck (4753/5000) lo1984 hi1984=true := by decide +kernel
def bracket1984 : MeanBracket := meanBracketOfMoments (4753/5000) lo1984 hi1984 accepted1984
def lo1985b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨10,by decide⟩
def lo1985b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨11,by decide⟩
def lo1985 : CheckedMoment :=
  CheckedMoment.ofBessel lo1985b1 lo1985b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1985b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨15,by decide⟩
def hi1985b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨16,by decide⟩
def hi1985 : CheckedMoment :=
  CheckedMoment.ofBessel hi1985b1 hi1985b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1985 : meanBracketCheck (9507/10000) lo1985 hi1985=true := by decide +kernel
def bracket1985 : MeanBracket := meanBracketOfMoments (9507/10000) lo1985 hi1985 accepted1985
def lo1986b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨20,by decide⟩
def lo1986b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨21,by decide⟩
def lo1986 : CheckedMoment :=
  CheckedMoment.ofBessel lo1986b1 lo1986b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1986b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨25,by decide⟩
def hi1986b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨26,by decide⟩
def hi1986 : CheckedMoment :=
  CheckedMoment.ofBessel hi1986b1 hi1986b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1986 : meanBracketCheck (2377/2500) lo1986 hi1986=true := by decide +kernel
def bracket1986 : MeanBracket := meanBracketOfMoments (2377/2500) lo1986 hi1986 accepted1986
def lo1987b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨30,by decide⟩
def lo1987b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨31,by decide⟩
def lo1987 : CheckedMoment :=
  CheckedMoment.ofBessel lo1987b1 lo1987b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1987b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨35,by decide⟩
def hi1987b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨36,by decide⟩
def hi1987 : CheckedMoment :=
  CheckedMoment.ofBessel hi1987b1 hi1987b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1987 : meanBracketCheck (9509/10000) lo1987 hi1987=true := by decide +kernel
def bracket1987 : MeanBracket := meanBracketOfMoments (9509/10000) lo1987 hi1987 accepted1987
def lo1988b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨40,by decide⟩
def lo1988b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨41,by decide⟩
def lo1988 : CheckedMoment :=
  CheckedMoment.ofBessel lo1988b1 lo1988b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1988b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨45,by decide⟩
def hi1988b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨46,by decide⟩
def hi1988 : CheckedMoment :=
  CheckedMoment.ofBessel hi1988b1 hi1988b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1988 : meanBracketCheck (951/1000) lo1988 hi1988=true := by decide +kernel
def bracket1988 : MeanBracket := meanBracketOfMoments (951/1000) lo1988 hi1988 accepted1988
def lo1989b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨50,by decide⟩
def lo1989b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨51,by decide⟩
def lo1989 : CheckedMoment :=
  CheckedMoment.ofBessel lo1989b1 lo1989b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1989b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨55,by decide⟩
def hi1989b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨56,by decide⟩
def hi1989 : CheckedMoment :=
  CheckedMoment.ofBessel hi1989b1 hi1989b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1989 : meanBracketCheck (9511/10000) lo1989 hi1989=true := by decide +kernel
def bracket1989 : MeanBracket := meanBracketOfMoments (9511/10000) lo1989 hi1989 accepted1989
def lo1990b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨60,by decide⟩
def lo1990b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨61,by decide⟩
def lo1990 : CheckedMoment :=
  CheckedMoment.ofBessel lo1990b1 lo1990b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1990b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨1,by decide⟩
def hi1990b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨2,by decide⟩
def hi1990 : CheckedMoment :=
  CheckedMoment.ofBessel hi1990b1 hi1990b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1990 : meanBracketCheck (1189/1250) lo1990 hi1990=true := by decide +kernel
def bracket1990 : MeanBracket := meanBracketOfMoments (1189/1250) lo1990 hi1990 accepted1990
def lo1991b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨6,by decide⟩
def lo1991b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨7,by decide⟩
def lo1991 : CheckedMoment :=
  CheckedMoment.ofBessel lo1991b1 lo1991b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1991b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨11,by decide⟩
def hi1991b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨12,by decide⟩
def hi1991 : CheckedMoment :=
  CheckedMoment.ofBessel hi1991b1 hi1991b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1991 : meanBracketCheck (9513/10000) lo1991 hi1991=true := by decide +kernel
def bracket1991 : MeanBracket := meanBracketOfMoments (9513/10000) lo1991 hi1991 accepted1991
def lo1992b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨16,by decide⟩
def lo1992b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨17,by decide⟩
def lo1992 : CheckedMoment :=
  CheckedMoment.ofBessel lo1992b1 lo1992b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1992b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨21,by decide⟩
def hi1992b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨22,by decide⟩
def hi1992 : CheckedMoment :=
  CheckedMoment.ofBessel hi1992b1 hi1992b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1992 : meanBracketCheck (4757/5000) lo1992 hi1992=true := by decide +kernel
def bracket1992 : MeanBracket := meanBracketOfMoments (4757/5000) lo1992 hi1992 accepted1992
def lo1993b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨26,by decide⟩
def lo1993b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨27,by decide⟩
def lo1993 : CheckedMoment :=
  CheckedMoment.ofBessel lo1993b1 lo1993b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1993b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨31,by decide⟩
def hi1993b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨32,by decide⟩
def hi1993 : CheckedMoment :=
  CheckedMoment.ofBessel hi1993b1 hi1993b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1993 : meanBracketCheck (1903/2000) lo1993 hi1993=true := by decide +kernel
def bracket1993 : MeanBracket := meanBracketOfMoments (1903/2000) lo1993 hi1993 accepted1993
def lo1994b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨36,by decide⟩
def lo1994b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨37,by decide⟩
def lo1994 : CheckedMoment :=
  CheckedMoment.ofBessel lo1994b1 lo1994b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1994b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨41,by decide⟩
def hi1994b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨42,by decide⟩
def hi1994 : CheckedMoment :=
  CheckedMoment.ofBessel hi1994b1 hi1994b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1994 : meanBracketCheck (2379/2500) lo1994 hi1994=true := by decide +kernel
def bracket1994 : MeanBracket := meanBracketOfMoments (2379/2500) lo1994 hi1994 accepted1994
def lo1995b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨46,by decide⟩
def lo1995b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨47,by decide⟩
def lo1995 : CheckedMoment :=
  CheckedMoment.ofBessel lo1995b1 lo1995b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1995b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨51,by decide⟩
def hi1995b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨52,by decide⟩
def hi1995 : CheckedMoment :=
  CheckedMoment.ofBessel hi1995b1 hi1995b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1995 : meanBracketCheck (9517/10000) lo1995 hi1995=true := by decide +kernel
def bracket1995 : MeanBracket := meanBracketOfMoments (9517/10000) lo1995 hi1995 accepted1995
def lo1996b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨56,by decide⟩
def lo1996b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨57,by decide⟩
def lo1996 : CheckedMoment :=
  CheckedMoment.ofBessel lo1996b1 lo1996b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1996b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨61,by decide⟩
def hi1996b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨62,by decide⟩
def hi1996 : CheckedMoment :=
  CheckedMoment.ofBessel hi1996b1 hi1996b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1996 : meanBracketCheck (4759/5000) lo1996 hi1996=true := by decide +kernel
def bracket1996 : MeanBracket := meanBracketOfMoments (4759/5000) lo1996 hi1996 accepted1996
def lo1997b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨2,by decide⟩
def lo1997b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨3,by decide⟩
def lo1997 : CheckedMoment :=
  CheckedMoment.ofBessel lo1997b1 lo1997b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1997b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨7,by decide⟩
def hi1997b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨8,by decide⟩
def hi1997 : CheckedMoment :=
  CheckedMoment.ofBessel hi1997b1 hi1997b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1997 : meanBracketCheck (9519/10000) lo1997 hi1997=true := by decide +kernel
def bracket1997 : MeanBracket := meanBracketOfMoments (9519/10000) lo1997 hi1997 accepted1997
def lo1998b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨12,by decide⟩
def lo1998b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨13,by decide⟩
def lo1998 : CheckedMoment :=
  CheckedMoment.ofBessel lo1998b1 lo1998b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1998b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨17,by decide⟩
def hi1998b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨18,by decide⟩
def hi1998 : CheckedMoment :=
  CheckedMoment.ofBessel hi1998b1 hi1998b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1998 : meanBracketCheck (119/125) lo1998 hi1998=true := by decide +kernel
def bracket1998 : MeanBracket := meanBracketOfMoments (119/125) lo1998 hi1998 accepted1998
def lo1999b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨22,by decide⟩
def lo1999b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨23,by decide⟩
def lo1999 : CheckedMoment :=
  CheckedMoment.ofBessel lo1999b1 lo1999b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1999b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨27,by decide⟩
def hi1999b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨28,by decide⟩
def hi1999 : CheckedMoment :=
  CheckedMoment.ofBessel hi1999b1 hi1999b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1999 : meanBracketCheck (9521/10000) lo1999 hi1999=true := by decide +kernel
def bracket1999 : MeanBracket := meanBracketOfMoments (9521/10000) lo1999 hi1999 accepted1999
#print axioms bracket1984
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0124
