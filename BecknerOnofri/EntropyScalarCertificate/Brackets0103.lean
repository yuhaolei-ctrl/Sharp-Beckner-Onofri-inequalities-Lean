import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0257
import BecknerOnofri.EntropyScalarCertificate.Bessel0258
import BecknerOnofri.EntropyScalarCertificate.Bessel0259
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0103
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1648b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨32,by decide⟩
def lo1648b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨33,by decide⟩
def lo1648 : CheckedMoment :=
  CheckedMoment.ofBessel lo1648b1 lo1648b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1648b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨37,by decide⟩
def hi1648b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨38,by decide⟩
def hi1648 : CheckedMoment :=
  CheckedMoment.ofBessel hi1648b1 hi1648b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1648 : meanBracketCheck (857/1000) lo1648 hi1648=true := by decide +kernel
def bracket1648 : MeanBracket := meanBracketOfMoments (857/1000) lo1648 hi1648 accepted1648
def lo1649b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨42,by decide⟩
def lo1649b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨43,by decide⟩
def lo1649 : CheckedMoment :=
  CheckedMoment.ofBessel lo1649b1 lo1649b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1649b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨47,by decide⟩
def hi1649b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨48,by decide⟩
def hi1649 : CheckedMoment :=
  CheckedMoment.ofBessel hi1649b1 hi1649b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1649 : meanBracketCheck (8571/10000) lo1649 hi1649=true := by decide +kernel
def bracket1649 : MeanBracket := meanBracketOfMoments (8571/10000) lo1649 hi1649 accepted1649
def lo1650b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨52,by decide⟩
def lo1650b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨53,by decide⟩
def lo1650 : CheckedMoment :=
  CheckedMoment.ofBessel lo1650b1 lo1650b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1650b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨57,by decide⟩
def hi1650b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨58,by decide⟩
def hi1650 : CheckedMoment :=
  CheckedMoment.ofBessel hi1650b1 hi1650b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1650 : meanBracketCheck (2143/2500) lo1650 hi1650=true := by decide +kernel
def bracket1650 : MeanBracket := meanBracketOfMoments (2143/2500) lo1650 hi1650 accepted1650
def lo1651b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨62,by decide⟩
def lo1651b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0257.rows BesselBatch0257.accepted ⟨63,by decide⟩
def lo1651 : CheckedMoment :=
  CheckedMoment.ofBessel lo1651b1 lo1651b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1651b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨3,by decide⟩
def hi1651b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨4,by decide⟩
def hi1651 : CheckedMoment :=
  CheckedMoment.ofBessel hi1651b1 hi1651b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1651 : meanBracketCheck (8573/10000) lo1651 hi1651=true := by decide +kernel
def bracket1651 : MeanBracket := meanBracketOfMoments (8573/10000) lo1651 hi1651 accepted1651
def lo1652b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨8,by decide⟩
def lo1652b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨9,by decide⟩
def lo1652 : CheckedMoment :=
  CheckedMoment.ofBessel lo1652b1 lo1652b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1652b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨13,by decide⟩
def hi1652b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨14,by decide⟩
def hi1652 : CheckedMoment :=
  CheckedMoment.ofBessel hi1652b1 hi1652b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1652 : meanBracketCheck (4287/5000) lo1652 hi1652=true := by decide +kernel
def bracket1652 : MeanBracket := meanBracketOfMoments (4287/5000) lo1652 hi1652 accepted1652
def lo1653b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨18,by decide⟩
def lo1653b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨19,by decide⟩
def lo1653 : CheckedMoment :=
  CheckedMoment.ofBessel lo1653b1 lo1653b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1653b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨23,by decide⟩
def hi1653b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨24,by decide⟩
def hi1653 : CheckedMoment :=
  CheckedMoment.ofBessel hi1653b1 hi1653b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1653 : meanBracketCheck (343/400) lo1653 hi1653=true := by decide +kernel
def bracket1653 : MeanBracket := meanBracketOfMoments (343/400) lo1653 hi1653 accepted1653
def lo1654b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨28,by decide⟩
def lo1654b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨29,by decide⟩
def lo1654 : CheckedMoment :=
  CheckedMoment.ofBessel lo1654b1 lo1654b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1654b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨33,by decide⟩
def hi1654b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨34,by decide⟩
def hi1654 : CheckedMoment :=
  CheckedMoment.ofBessel hi1654b1 hi1654b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1654 : meanBracketCheck (536/625) lo1654 hi1654=true := by decide +kernel
def bracket1654 : MeanBracket := meanBracketOfMoments (536/625) lo1654 hi1654 accepted1654
def lo1655b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨38,by decide⟩
def lo1655b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨39,by decide⟩
def lo1655 : CheckedMoment :=
  CheckedMoment.ofBessel lo1655b1 lo1655b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1655b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨43,by decide⟩
def hi1655b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨44,by decide⟩
def hi1655 : CheckedMoment :=
  CheckedMoment.ofBessel hi1655b1 hi1655b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1655 : meanBracketCheck (8577/10000) lo1655 hi1655=true := by decide +kernel
def bracket1655 : MeanBracket := meanBracketOfMoments (8577/10000) lo1655 hi1655 accepted1655
def lo1656b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨48,by decide⟩
def lo1656b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨49,by decide⟩
def lo1656 : CheckedMoment :=
  CheckedMoment.ofBessel lo1656b1 lo1656b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1656b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨53,by decide⟩
def hi1656b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨54,by decide⟩
def hi1656 : CheckedMoment :=
  CheckedMoment.ofBessel hi1656b1 hi1656b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1656 : meanBracketCheck (4289/5000) lo1656 hi1656=true := by decide +kernel
def bracket1656 : MeanBracket := meanBracketOfMoments (4289/5000) lo1656 hi1656 accepted1656
def lo1657b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨58,by decide⟩
def lo1657b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨59,by decide⟩
def lo1657 : CheckedMoment :=
  CheckedMoment.ofBessel lo1657b1 lo1657b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1657b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0258.rows BesselBatch0258.accepted ⟨63,by decide⟩
def hi1657b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨0,by decide⟩
def hi1657 : CheckedMoment :=
  CheckedMoment.ofBessel hi1657b1 hi1657b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1657 : meanBracketCheck (8579/10000) lo1657 hi1657=true := by decide +kernel
def bracket1657 : MeanBracket := meanBracketOfMoments (8579/10000) lo1657 hi1657 accepted1657
def lo1658b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨4,by decide⟩
def lo1658b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨5,by decide⟩
def lo1658 : CheckedMoment :=
  CheckedMoment.ofBessel lo1658b1 lo1658b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1658b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨9,by decide⟩
def hi1658b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨10,by decide⟩
def hi1658 : CheckedMoment :=
  CheckedMoment.ofBessel hi1658b1 hi1658b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1658 : meanBracketCheck (429/500) lo1658 hi1658=true := by decide +kernel
def bracket1658 : MeanBracket := meanBracketOfMoments (429/500) lo1658 hi1658 accepted1658
def lo1659b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨14,by decide⟩
def lo1659b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨15,by decide⟩
def lo1659 : CheckedMoment :=
  CheckedMoment.ofBessel lo1659b1 lo1659b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1659b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨19,by decide⟩
def hi1659b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨20,by decide⟩
def hi1659 : CheckedMoment :=
  CheckedMoment.ofBessel hi1659b1 hi1659b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1659 : meanBracketCheck (8581/10000) lo1659 hi1659=true := by decide +kernel
def bracket1659 : MeanBracket := meanBracketOfMoments (8581/10000) lo1659 hi1659 accepted1659
def lo1660b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨24,by decide⟩
def lo1660b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨25,by decide⟩
def lo1660 : CheckedMoment :=
  CheckedMoment.ofBessel lo1660b1 lo1660b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1660b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨29,by decide⟩
def hi1660b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨30,by decide⟩
def hi1660 : CheckedMoment :=
  CheckedMoment.ofBessel hi1660b1 hi1660b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1660 : meanBracketCheck (4291/5000) lo1660 hi1660=true := by decide +kernel
def bracket1660 : MeanBracket := meanBracketOfMoments (4291/5000) lo1660 hi1660 accepted1660
def lo1661b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨34,by decide⟩
def lo1661b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨35,by decide⟩
def lo1661 : CheckedMoment :=
  CheckedMoment.ofBessel lo1661b1 lo1661b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1661b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨39,by decide⟩
def hi1661b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨40,by decide⟩
def hi1661 : CheckedMoment :=
  CheckedMoment.ofBessel hi1661b1 hi1661b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1661 : meanBracketCheck (8583/10000) lo1661 hi1661=true := by decide +kernel
def bracket1661 : MeanBracket := meanBracketOfMoments (8583/10000) lo1661 hi1661 accepted1661
def lo1662b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨44,by decide⟩
def lo1662b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨45,by decide⟩
def lo1662 : CheckedMoment :=
  CheckedMoment.ofBessel lo1662b1 lo1662b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1662b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨49,by decide⟩
def hi1662b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨50,by decide⟩
def hi1662 : CheckedMoment :=
  CheckedMoment.ofBessel hi1662b1 hi1662b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1662 : meanBracketCheck (1073/1250) lo1662 hi1662=true := by decide +kernel
def bracket1662 : MeanBracket := meanBracketOfMoments (1073/1250) lo1662 hi1662 accepted1662
def lo1663b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨54,by decide⟩
def lo1663b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨55,by decide⟩
def lo1663 : CheckedMoment :=
  CheckedMoment.ofBessel lo1663b1 lo1663b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1663b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨59,by decide⟩
def hi1663b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0259.rows BesselBatch0259.accepted ⟨60,by decide⟩
def hi1663 : CheckedMoment :=
  CheckedMoment.ofBessel hi1663b1 hi1663b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1663 : meanBracketCheck (1717/2000) lo1663 hi1663=true := by decide +kernel
def bracket1663 : MeanBracket := meanBracketOfMoments (1717/2000) lo1663 hi1663 accepted1663
#print axioms bracket1648
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0103
