module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0247
public import BecknerOnofri.EntropyScalarCertificate.Bessel0248
public import BecknerOnofri.EntropyScalarCertificate.Bessel0249

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0099
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1584b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨32,by decide⟩
def lo1584b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨33,by decide⟩
def lo1584 : CheckedMoment :=
  CheckedMoment.ofBessel lo1584b1 lo1584b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1584b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨37,by decide⟩
def hi1584b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨38,by decide⟩
def hi1584 : CheckedMoment :=
  CheckedMoment.ofBessel hi1584b1 hi1584b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1584 : meanBracketCheck (4253/5000) lo1584 hi1584=true := by decide +kernel
def bracket1584 : MeanBracket := meanBracketOfMoments (4253/5000) lo1584 hi1584 accepted1584
def lo1585b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨42,by decide⟩
def lo1585b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨43,by decide⟩
def lo1585 : CheckedMoment :=
  CheckedMoment.ofBessel lo1585b1 lo1585b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1585b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨47,by decide⟩
def hi1585b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨48,by decide⟩
def hi1585 : CheckedMoment :=
  CheckedMoment.ofBessel hi1585b1 hi1585b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1585 : meanBracketCheck (8507/10000) lo1585 hi1585=true := by decide +kernel
def bracket1585 : MeanBracket := meanBracketOfMoments (8507/10000) lo1585 hi1585 accepted1585
def lo1586b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨52,by decide⟩
def lo1586b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨53,by decide⟩
def lo1586 : CheckedMoment :=
  CheckedMoment.ofBessel lo1586b1 lo1586b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1586b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨57,by decide⟩
def hi1586b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨58,by decide⟩
def hi1586 : CheckedMoment :=
  CheckedMoment.ofBessel hi1586b1 hi1586b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1586 : meanBracketCheck (2127/2500) lo1586 hi1586=true := by decide +kernel
def bracket1586 : MeanBracket := meanBracketOfMoments (2127/2500) lo1586 hi1586 accepted1586
def lo1587b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨62,by decide⟩
def lo1587b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨63,by decide⟩
def lo1587 : CheckedMoment :=
  CheckedMoment.ofBessel lo1587b1 lo1587b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1587b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨3,by decide⟩
def hi1587b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨4,by decide⟩
def hi1587 : CheckedMoment :=
  CheckedMoment.ofBessel hi1587b1 hi1587b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1587 : meanBracketCheck (8509/10000) lo1587 hi1587=true := by decide +kernel
def bracket1587 : MeanBracket := meanBracketOfMoments (8509/10000) lo1587 hi1587 accepted1587
def lo1588b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨8,by decide⟩
def lo1588b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨9,by decide⟩
def lo1588 : CheckedMoment :=
  CheckedMoment.ofBessel lo1588b1 lo1588b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1588b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨13,by decide⟩
def hi1588b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨14,by decide⟩
def hi1588 : CheckedMoment :=
  CheckedMoment.ofBessel hi1588b1 hi1588b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1588 : meanBracketCheck (851/1000) lo1588 hi1588=true := by decide +kernel
def bracket1588 : MeanBracket := meanBracketOfMoments (851/1000) lo1588 hi1588 accepted1588
def lo1589b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨18,by decide⟩
def lo1589b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨19,by decide⟩
def lo1589 : CheckedMoment :=
  CheckedMoment.ofBessel lo1589b1 lo1589b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1589b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨23,by decide⟩
def hi1589b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨24,by decide⟩
def hi1589 : CheckedMoment :=
  CheckedMoment.ofBessel hi1589b1 hi1589b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1589 : meanBracketCheck (8511/10000) lo1589 hi1589=true := by decide +kernel
def bracket1589 : MeanBracket := meanBracketOfMoments (8511/10000) lo1589 hi1589 accepted1589
def lo1590b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨28,by decide⟩
def lo1590b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨29,by decide⟩
def lo1590 : CheckedMoment :=
  CheckedMoment.ofBessel lo1590b1 lo1590b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1590b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨33,by decide⟩
def hi1590b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨34,by decide⟩
def hi1590 : CheckedMoment :=
  CheckedMoment.ofBessel hi1590b1 hi1590b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1590 : meanBracketCheck (532/625) lo1590 hi1590=true := by decide +kernel
def bracket1590 : MeanBracket := meanBracketOfMoments (532/625) lo1590 hi1590 accepted1590
def lo1591b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨38,by decide⟩
def lo1591b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨39,by decide⟩
def lo1591 : CheckedMoment :=
  CheckedMoment.ofBessel lo1591b1 lo1591b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1591b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨43,by decide⟩
def hi1591b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨44,by decide⟩
def hi1591 : CheckedMoment :=
  CheckedMoment.ofBessel hi1591b1 hi1591b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1591 : meanBracketCheck (8513/10000) lo1591 hi1591=true := by decide +kernel
def bracket1591 : MeanBracket := meanBracketOfMoments (8513/10000) lo1591 hi1591 accepted1591
def lo1592b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨48,by decide⟩
def lo1592b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨49,by decide⟩
def lo1592 : CheckedMoment :=
  CheckedMoment.ofBessel lo1592b1 lo1592b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1592b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨53,by decide⟩
def hi1592b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨54,by decide⟩
def hi1592 : CheckedMoment :=
  CheckedMoment.ofBessel hi1592b1 hi1592b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1592 : meanBracketCheck (4257/5000) lo1592 hi1592=true := by decide +kernel
def bracket1592 : MeanBracket := meanBracketOfMoments (4257/5000) lo1592 hi1592 accepted1592
def lo1593b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨58,by decide⟩
def lo1593b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨59,by decide⟩
def lo1593 : CheckedMoment :=
  CheckedMoment.ofBessel lo1593b1 lo1593b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1593b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨63,by decide⟩
def hi1593b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨0,by decide⟩
def hi1593 : CheckedMoment :=
  CheckedMoment.ofBessel hi1593b1 hi1593b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1593 : meanBracketCheck (1703/2000) lo1593 hi1593=true := by decide +kernel
def bracket1593 : MeanBracket := meanBracketOfMoments (1703/2000) lo1593 hi1593 accepted1593
def lo1594b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨4,by decide⟩
def lo1594b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨5,by decide⟩
def lo1594 : CheckedMoment :=
  CheckedMoment.ofBessel lo1594b1 lo1594b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1594b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨9,by decide⟩
def hi1594b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨10,by decide⟩
def hi1594 : CheckedMoment :=
  CheckedMoment.ofBessel hi1594b1 hi1594b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1594 : meanBracketCheck (2129/2500) lo1594 hi1594=true := by decide +kernel
def bracket1594 : MeanBracket := meanBracketOfMoments (2129/2500) lo1594 hi1594 accepted1594
def lo1595b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨14,by decide⟩
def lo1595b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨15,by decide⟩
def lo1595 : CheckedMoment :=
  CheckedMoment.ofBessel lo1595b1 lo1595b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1595b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨19,by decide⟩
def hi1595b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨20,by decide⟩
def hi1595 : CheckedMoment :=
  CheckedMoment.ofBessel hi1595b1 hi1595b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1595 : meanBracketCheck (8517/10000) lo1595 hi1595=true := by decide +kernel
def bracket1595 : MeanBracket := meanBracketOfMoments (8517/10000) lo1595 hi1595 accepted1595
def lo1596b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨24,by decide⟩
def lo1596b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨25,by decide⟩
def lo1596 : CheckedMoment :=
  CheckedMoment.ofBessel lo1596b1 lo1596b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1596b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨29,by decide⟩
def hi1596b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨30,by decide⟩
def hi1596 : CheckedMoment :=
  CheckedMoment.ofBessel hi1596b1 hi1596b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1596 : meanBracketCheck (4259/5000) lo1596 hi1596=true := by decide +kernel
def bracket1596 : MeanBracket := meanBracketOfMoments (4259/5000) lo1596 hi1596 accepted1596
def lo1597b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨34,by decide⟩
def lo1597b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨35,by decide⟩
def lo1597 : CheckedMoment :=
  CheckedMoment.ofBessel lo1597b1 lo1597b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1597b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨39,by decide⟩
def hi1597b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨40,by decide⟩
def hi1597 : CheckedMoment :=
  CheckedMoment.ofBessel hi1597b1 hi1597b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1597 : meanBracketCheck (8519/10000) lo1597 hi1597=true := by decide +kernel
def bracket1597 : MeanBracket := meanBracketOfMoments (8519/10000) lo1597 hi1597 accepted1597
def lo1598b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨44,by decide⟩
def lo1598b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨45,by decide⟩
def lo1598 : CheckedMoment :=
  CheckedMoment.ofBessel lo1598b1 lo1598b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1598b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨49,by decide⟩
def hi1598b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨50,by decide⟩
def hi1598 : CheckedMoment :=
  CheckedMoment.ofBessel hi1598b1 hi1598b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1598 : meanBracketCheck (213/250) lo1598 hi1598=true := by decide +kernel
def bracket1598 : MeanBracket := meanBracketOfMoments (213/250) lo1598 hi1598 accepted1598
def lo1599b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨54,by decide⟩
def lo1599b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨55,by decide⟩
def lo1599 : CheckedMoment :=
  CheckedMoment.ofBessel lo1599b1 lo1599b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1599b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨59,by decide⟩
def hi1599b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨60,by decide⟩
def hi1599 : CheckedMoment :=
  CheckedMoment.ofBessel hi1599b1 hi1599b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1599 : meanBracketCheck (8521/10000) lo1599 hi1599=true := by decide +kernel
def bracket1599 : MeanBracket := meanBracketOfMoments (8521/10000) lo1599 hi1599 accepted1599
#print axioms bracket1584
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0099
