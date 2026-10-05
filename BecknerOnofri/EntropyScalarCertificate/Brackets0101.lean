import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0252
import BecknerOnofri.EntropyScalarCertificate.Bessel0253
import BecknerOnofri.EntropyScalarCertificate.Bessel0254
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0101
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1616b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨32,by decide⟩
def lo1616b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨33,by decide⟩
def lo1616 : CheckedMoment :=
  CheckedMoment.ofBessel lo1616b1 lo1616b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1616b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨37,by decide⟩
def hi1616b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨38,by decide⟩
def hi1616 : CheckedMoment :=
  CheckedMoment.ofBessel hi1616b1 hi1616b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1616 : meanBracketCheck (4269/5000) lo1616 hi1616=true := by decide +kernel
def bracket1616 : MeanBracket := meanBracketOfMoments (4269/5000) lo1616 hi1616 accepted1616
def lo1617b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨42,by decide⟩
def lo1617b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨43,by decide⟩
def lo1617 : CheckedMoment :=
  CheckedMoment.ofBessel lo1617b1 lo1617b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1617b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨47,by decide⟩
def hi1617b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨48,by decide⟩
def hi1617 : CheckedMoment :=
  CheckedMoment.ofBessel hi1617b1 hi1617b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1617 : meanBracketCheck (8539/10000) lo1617 hi1617=true := by decide +kernel
def bracket1617 : MeanBracket := meanBracketOfMoments (8539/10000) lo1617 hi1617 accepted1617
def lo1618b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨52,by decide⟩
def lo1618b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨53,by decide⟩
def lo1618 : CheckedMoment :=
  CheckedMoment.ofBessel lo1618b1 lo1618b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1618b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨57,by decide⟩
def hi1618b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨58,by decide⟩
def hi1618 : CheckedMoment :=
  CheckedMoment.ofBessel hi1618b1 hi1618b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1618 : meanBracketCheck (427/500) lo1618 hi1618=true := by decide +kernel
def bracket1618 : MeanBracket := meanBracketOfMoments (427/500) lo1618 hi1618 accepted1618
def lo1619b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨62,by decide⟩
def lo1619b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨63,by decide⟩
def lo1619 : CheckedMoment :=
  CheckedMoment.ofBessel lo1619b1 lo1619b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1619b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨3,by decide⟩
def hi1619b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨4,by decide⟩
def hi1619 : CheckedMoment :=
  CheckedMoment.ofBessel hi1619b1 hi1619b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1619 : meanBracketCheck (8541/10000) lo1619 hi1619=true := by decide +kernel
def bracket1619 : MeanBracket := meanBracketOfMoments (8541/10000) lo1619 hi1619 accepted1619
def lo1620b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨8,by decide⟩
def lo1620b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨9,by decide⟩
def lo1620 : CheckedMoment :=
  CheckedMoment.ofBessel lo1620b1 lo1620b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1620b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨13,by decide⟩
def hi1620b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨14,by decide⟩
def hi1620 : CheckedMoment :=
  CheckedMoment.ofBessel hi1620b1 hi1620b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1620 : meanBracketCheck (4271/5000) lo1620 hi1620=true := by decide +kernel
def bracket1620 : MeanBracket := meanBracketOfMoments (4271/5000) lo1620 hi1620 accepted1620
def lo1621b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨18,by decide⟩
def lo1621b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨19,by decide⟩
def lo1621 : CheckedMoment :=
  CheckedMoment.ofBessel lo1621b1 lo1621b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1621b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨23,by decide⟩
def hi1621b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨24,by decide⟩
def hi1621 : CheckedMoment :=
  CheckedMoment.ofBessel hi1621b1 hi1621b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1621 : meanBracketCheck (8543/10000) lo1621 hi1621=true := by decide +kernel
def bracket1621 : MeanBracket := meanBracketOfMoments (8543/10000) lo1621 hi1621 accepted1621
def lo1622b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨28,by decide⟩
def lo1622b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨29,by decide⟩
def lo1622 : CheckedMoment :=
  CheckedMoment.ofBessel lo1622b1 lo1622b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1622b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨33,by decide⟩
def hi1622b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨34,by decide⟩
def hi1622 : CheckedMoment :=
  CheckedMoment.ofBessel hi1622b1 hi1622b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1622 : meanBracketCheck (534/625) lo1622 hi1622=true := by decide +kernel
def bracket1622 : MeanBracket := meanBracketOfMoments (534/625) lo1622 hi1622 accepted1622
def lo1623b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨38,by decide⟩
def lo1623b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨39,by decide⟩
def lo1623 : CheckedMoment :=
  CheckedMoment.ofBessel lo1623b1 lo1623b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1623b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨43,by decide⟩
def hi1623b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨44,by decide⟩
def hi1623 : CheckedMoment :=
  CheckedMoment.ofBessel hi1623b1 hi1623b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1623 : meanBracketCheck (1709/2000) lo1623 hi1623=true := by decide +kernel
def bracket1623 : MeanBracket := meanBracketOfMoments (1709/2000) lo1623 hi1623 accepted1623
def lo1624b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨48,by decide⟩
def lo1624b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨49,by decide⟩
def lo1624 : CheckedMoment :=
  CheckedMoment.ofBessel lo1624b1 lo1624b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1624b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨53,by decide⟩
def hi1624b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨54,by decide⟩
def hi1624 : CheckedMoment :=
  CheckedMoment.ofBessel hi1624b1 hi1624b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1624 : meanBracketCheck (4273/5000) lo1624 hi1624=true := by decide +kernel
def bracket1624 : MeanBracket := meanBracketOfMoments (4273/5000) lo1624 hi1624 accepted1624
def lo1625b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨58,by decide⟩
def lo1625b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨59,by decide⟩
def lo1625 : CheckedMoment :=
  CheckedMoment.ofBessel lo1625b1 lo1625b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1625b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨63,by decide⟩
def hi1625b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨0,by decide⟩
def hi1625 : CheckedMoment :=
  CheckedMoment.ofBessel hi1625b1 hi1625b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1625 : meanBracketCheck (8547/10000) lo1625 hi1625=true := by decide +kernel
def bracket1625 : MeanBracket := meanBracketOfMoments (8547/10000) lo1625 hi1625 accepted1625
def lo1626b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨4,by decide⟩
def lo1626b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨5,by decide⟩
def lo1626 : CheckedMoment :=
  CheckedMoment.ofBessel lo1626b1 lo1626b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1626b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨9,by decide⟩
def hi1626b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨10,by decide⟩
def hi1626 : CheckedMoment :=
  CheckedMoment.ofBessel hi1626b1 hi1626b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1626 : meanBracketCheck (2137/2500) lo1626 hi1626=true := by decide +kernel
def bracket1626 : MeanBracket := meanBracketOfMoments (2137/2500) lo1626 hi1626 accepted1626
def lo1627b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨14,by decide⟩
def lo1627b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨15,by decide⟩
def lo1627 : CheckedMoment :=
  CheckedMoment.ofBessel lo1627b1 lo1627b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1627b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨19,by decide⟩
def hi1627b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨20,by decide⟩
def hi1627 : CheckedMoment :=
  CheckedMoment.ofBessel hi1627b1 hi1627b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1627 : meanBracketCheck (8549/10000) lo1627 hi1627=true := by decide +kernel
def bracket1627 : MeanBracket := meanBracketOfMoments (8549/10000) lo1627 hi1627 accepted1627
def lo1628b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨24,by decide⟩
def lo1628b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨25,by decide⟩
def lo1628 : CheckedMoment :=
  CheckedMoment.ofBessel lo1628b1 lo1628b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1628b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨29,by decide⟩
def hi1628b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨30,by decide⟩
def hi1628 : CheckedMoment :=
  CheckedMoment.ofBessel hi1628b1 hi1628b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1628 : meanBracketCheck (171/200) lo1628 hi1628=true := by decide +kernel
def bracket1628 : MeanBracket := meanBracketOfMoments (171/200) lo1628 hi1628 accepted1628
def lo1629b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨34,by decide⟩
def lo1629b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨35,by decide⟩
def lo1629 : CheckedMoment :=
  CheckedMoment.ofBessel lo1629b1 lo1629b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1629b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨39,by decide⟩
def hi1629b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨40,by decide⟩
def hi1629 : CheckedMoment :=
  CheckedMoment.ofBessel hi1629b1 hi1629b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1629 : meanBracketCheck (8551/10000) lo1629 hi1629=true := by decide +kernel
def bracket1629 : MeanBracket := meanBracketOfMoments (8551/10000) lo1629 hi1629 accepted1629
def lo1630b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨44,by decide⟩
def lo1630b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨45,by decide⟩
def lo1630 : CheckedMoment :=
  CheckedMoment.ofBessel lo1630b1 lo1630b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1630b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨49,by decide⟩
def hi1630b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨50,by decide⟩
def hi1630 : CheckedMoment :=
  CheckedMoment.ofBessel hi1630b1 hi1630b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1630 : meanBracketCheck (1069/1250) lo1630 hi1630=true := by decide +kernel
def bracket1630 : MeanBracket := meanBracketOfMoments (1069/1250) lo1630 hi1630 accepted1630
def lo1631b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨54,by decide⟩
def lo1631b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨55,by decide⟩
def lo1631 : CheckedMoment :=
  CheckedMoment.ofBessel lo1631b1 lo1631b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1631b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨59,by decide⟩
def hi1631b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨60,by decide⟩
def hi1631 : CheckedMoment :=
  CheckedMoment.ofBessel hi1631b1 hi1631b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1631 : meanBracketCheck (8553/10000) lo1631 hi1631=true := by decide +kernel
def bracket1631 : MeanBracket := meanBracketOfMoments (8553/10000) lo1631 hi1631 accepted1631
#print axioms bracket1616
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0101
