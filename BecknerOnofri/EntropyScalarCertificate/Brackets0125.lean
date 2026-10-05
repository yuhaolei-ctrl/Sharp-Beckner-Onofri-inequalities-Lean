module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0312
public import BecknerOnofri.EntropyScalarCertificate.Bessel0313
public import BecknerOnofri.EntropyScalarCertificate.Bessel0314

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0125
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2000b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨32,by decide⟩
def lo2000b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨33,by decide⟩
def lo2000 : CheckedMoment :=
  CheckedMoment.ofBessel lo2000b1 lo2000b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2000b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨37,by decide⟩
def hi2000b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨38,by decide⟩
def hi2000 : CheckedMoment :=
  CheckedMoment.ofBessel hi2000b1 hi2000b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2000 : meanBracketCheck (4761/5000) lo2000 hi2000=true := by decide +kernel
def bracket2000 : MeanBracket := meanBracketOfMoments (4761/5000) lo2000 hi2000 accepted2000
def lo2001b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨42,by decide⟩
def lo2001b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨43,by decide⟩
def lo2001 : CheckedMoment :=
  CheckedMoment.ofBessel lo2001b1 lo2001b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2001b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨47,by decide⟩
def hi2001b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨48,by decide⟩
def hi2001 : CheckedMoment :=
  CheckedMoment.ofBessel hi2001b1 hi2001b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2001 : meanBracketCheck (9523/10000) lo2001 hi2001=true := by decide +kernel
def bracket2001 : MeanBracket := meanBracketOfMoments (9523/10000) lo2001 hi2001 accepted2001
def lo2002b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨52,by decide⟩
def lo2002b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨53,by decide⟩
def lo2002 : CheckedMoment :=
  CheckedMoment.ofBessel lo2002b1 lo2002b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2002b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨57,by decide⟩
def hi2002b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨58,by decide⟩
def hi2002 : CheckedMoment :=
  CheckedMoment.ofBessel hi2002b1 hi2002b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2002 : meanBracketCheck (2381/2500) lo2002 hi2002=true := by decide +kernel
def bracket2002 : MeanBracket := meanBracketOfMoments (2381/2500) lo2002 hi2002 accepted2002
def lo2003b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨62,by decide⟩
def lo2003b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨63,by decide⟩
def lo2003 : CheckedMoment :=
  CheckedMoment.ofBessel lo2003b1 lo2003b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2003b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨3,by decide⟩
def hi2003b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨4,by decide⟩
def hi2003 : CheckedMoment :=
  CheckedMoment.ofBessel hi2003b1 hi2003b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2003 : meanBracketCheck (381/400) lo2003 hi2003=true := by decide +kernel
def bracket2003 : MeanBracket := meanBracketOfMoments (381/400) lo2003 hi2003 accepted2003
def lo2004b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨8,by decide⟩
def lo2004b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨9,by decide⟩
def lo2004 : CheckedMoment :=
  CheckedMoment.ofBessel lo2004b1 lo2004b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2004b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨13,by decide⟩
def hi2004b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨14,by decide⟩
def hi2004 : CheckedMoment :=
  CheckedMoment.ofBessel hi2004b1 hi2004b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2004 : meanBracketCheck (4763/5000) lo2004 hi2004=true := by decide +kernel
def bracket2004 : MeanBracket := meanBracketOfMoments (4763/5000) lo2004 hi2004 accepted2004
def lo2005b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨18,by decide⟩
def lo2005b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨19,by decide⟩
def lo2005 : CheckedMoment :=
  CheckedMoment.ofBessel lo2005b1 lo2005b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2005b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨23,by decide⟩
def hi2005b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨24,by decide⟩
def hi2005 : CheckedMoment :=
  CheckedMoment.ofBessel hi2005b1 hi2005b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2005 : meanBracketCheck (9527/10000) lo2005 hi2005=true := by decide +kernel
def bracket2005 : MeanBracket := meanBracketOfMoments (9527/10000) lo2005 hi2005 accepted2005
def lo2006b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨28,by decide⟩
def lo2006b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨29,by decide⟩
def lo2006 : CheckedMoment :=
  CheckedMoment.ofBessel lo2006b1 lo2006b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2006b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨33,by decide⟩
def hi2006b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨34,by decide⟩
def hi2006 : CheckedMoment :=
  CheckedMoment.ofBessel hi2006b1 hi2006b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2006 : meanBracketCheck (1191/1250) lo2006 hi2006=true := by decide +kernel
def bracket2006 : MeanBracket := meanBracketOfMoments (1191/1250) lo2006 hi2006 accepted2006
def lo2007b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨38,by decide⟩
def lo2007b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨39,by decide⟩
def lo2007 : CheckedMoment :=
  CheckedMoment.ofBessel lo2007b1 lo2007b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2007b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨43,by decide⟩
def hi2007b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨44,by decide⟩
def hi2007 : CheckedMoment :=
  CheckedMoment.ofBessel hi2007b1 hi2007b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2007 : meanBracketCheck (9529/10000) lo2007 hi2007=true := by decide +kernel
def bracket2007 : MeanBracket := meanBracketOfMoments (9529/10000) lo2007 hi2007 accepted2007
def lo2008b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨48,by decide⟩
def lo2008b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨49,by decide⟩
def lo2008 : CheckedMoment :=
  CheckedMoment.ofBessel lo2008b1 lo2008b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2008b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨53,by decide⟩
def hi2008b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨54,by decide⟩
def hi2008 : CheckedMoment :=
  CheckedMoment.ofBessel hi2008b1 hi2008b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2008 : meanBracketCheck (953/1000) lo2008 hi2008=true := by decide +kernel
def bracket2008 : MeanBracket := meanBracketOfMoments (953/1000) lo2008 hi2008 accepted2008
def lo2009b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨58,by decide⟩
def lo2009b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨59,by decide⟩
def lo2009 : CheckedMoment :=
  CheckedMoment.ofBessel lo2009b1 lo2009b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2009b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨63,by decide⟩
def hi2009b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨0,by decide⟩
def hi2009 : CheckedMoment :=
  CheckedMoment.ofBessel hi2009b1 hi2009b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2009 : meanBracketCheck (9531/10000) lo2009 hi2009=true := by decide +kernel
def bracket2009 : MeanBracket := meanBracketOfMoments (9531/10000) lo2009 hi2009 accepted2009
def lo2010b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨4,by decide⟩
def lo2010b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨5,by decide⟩
def lo2010 : CheckedMoment :=
  CheckedMoment.ofBessel lo2010b1 lo2010b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2010b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨9,by decide⟩
def hi2010b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨10,by decide⟩
def hi2010 : CheckedMoment :=
  CheckedMoment.ofBessel hi2010b1 hi2010b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2010 : meanBracketCheck (2383/2500) lo2010 hi2010=true := by decide +kernel
def bracket2010 : MeanBracket := meanBracketOfMoments (2383/2500) lo2010 hi2010 accepted2010
def lo2011b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨14,by decide⟩
def lo2011b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨15,by decide⟩
def lo2011 : CheckedMoment :=
  CheckedMoment.ofBessel lo2011b1 lo2011b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2011b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨19,by decide⟩
def hi2011b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨20,by decide⟩
def hi2011 : CheckedMoment :=
  CheckedMoment.ofBessel hi2011b1 hi2011b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2011 : meanBracketCheck (9533/10000) lo2011 hi2011=true := by decide +kernel
def bracket2011 : MeanBracket := meanBracketOfMoments (9533/10000) lo2011 hi2011 accepted2011
def lo2012b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨24,by decide⟩
def lo2012b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨25,by decide⟩
def lo2012 : CheckedMoment :=
  CheckedMoment.ofBessel lo2012b1 lo2012b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2012b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨29,by decide⟩
def hi2012b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨30,by decide⟩
def hi2012 : CheckedMoment :=
  CheckedMoment.ofBessel hi2012b1 hi2012b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2012 : meanBracketCheck (4767/5000) lo2012 hi2012=true := by decide +kernel
def bracket2012 : MeanBracket := meanBracketOfMoments (4767/5000) lo2012 hi2012 accepted2012
def lo2013b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨34,by decide⟩
def lo2013b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨35,by decide⟩
def lo2013 : CheckedMoment :=
  CheckedMoment.ofBessel lo2013b1 lo2013b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2013b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨39,by decide⟩
def hi2013b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨40,by decide⟩
def hi2013 : CheckedMoment :=
  CheckedMoment.ofBessel hi2013b1 hi2013b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2013 : meanBracketCheck (1907/2000) lo2013 hi2013=true := by decide +kernel
def bracket2013 : MeanBracket := meanBracketOfMoments (1907/2000) lo2013 hi2013 accepted2013
def lo2014b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨44,by decide⟩
def lo2014b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨45,by decide⟩
def lo2014 : CheckedMoment :=
  CheckedMoment.ofBessel lo2014b1 lo2014b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2014b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨49,by decide⟩
def hi2014b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨50,by decide⟩
def hi2014 : CheckedMoment :=
  CheckedMoment.ofBessel hi2014b1 hi2014b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2014 : meanBracketCheck (596/625) lo2014 hi2014=true := by decide +kernel
def bracket2014 : MeanBracket := meanBracketOfMoments (596/625) lo2014 hi2014 accepted2014
def lo2015b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨54,by decide⟩
def lo2015b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨55,by decide⟩
def lo2015 : CheckedMoment :=
  CheckedMoment.ofBessel lo2015b1 lo2015b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2015b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨59,by decide⟩
def hi2015b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨60,by decide⟩
def hi2015 : CheckedMoment :=
  CheckedMoment.ofBessel hi2015b1 hi2015b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2015 : meanBracketCheck (9537/10000) lo2015 hi2015=true := by decide +kernel
def bracket2015 : MeanBracket := meanBracketOfMoments (9537/10000) lo2015 hi2015 accepted2015
#print axioms bracket2000
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0125
