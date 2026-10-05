import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0087
import BecknerOnofri.EntropyScalarCertificate.Bessel0088
import BecknerOnofri.EntropyScalarCertificate.Bessel0089
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0035
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0560b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨32,by decide⟩
def lo0560b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨33,by decide⟩
def lo0560 : CheckedMoment :=
  CheckedMoment.ofBessel lo0560b1 lo0560b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0560b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨37,by decide⟩
def hi0560b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨38,by decide⟩
def hi0560 : CheckedMoment :=
  CheckedMoment.ofBessel hi0560b1 hi0560b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0560 : meanBracketCheck (337/2000) lo0560 hi0560=true := by decide +kernel
def bracket0560 : MeanBracket := meanBracketOfMoments (337/2000) lo0560 hi0560 accepted0560
def lo0561b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨42,by decide⟩
def lo0561b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨43,by decide⟩
def lo0561 : CheckedMoment :=
  CheckedMoment.ofBessel lo0561b1 lo0561b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0561b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨47,by decide⟩
def hi0561b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨48,by decide⟩
def hi0561 : CheckedMoment :=
  CheckedMoment.ofBessel hi0561b1 hi0561b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0561 : meanBracketCheck (1687/10000) lo0561 hi0561=true := by decide +kernel
def bracket0561 : MeanBracket := meanBracketOfMoments (1687/10000) lo0561 hi0561 accepted0561
def lo0562b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨52,by decide⟩
def lo0562b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨53,by decide⟩
def lo0562 : CheckedMoment :=
  CheckedMoment.ofBessel lo0562b1 lo0562b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0562b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨57,by decide⟩
def hi0562b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨58,by decide⟩
def hi0562 : CheckedMoment :=
  CheckedMoment.ofBessel hi0562b1 hi0562b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0562 : meanBracketCheck (1689/10000) lo0562 hi0562=true := by decide +kernel
def bracket0562 : MeanBracket := meanBracketOfMoments (1689/10000) lo0562 hi0562 accepted0562
def lo0563b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨62,by decide⟩
def lo0563b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨63,by decide⟩
def lo0563 : CheckedMoment :=
  CheckedMoment.ofBessel lo0563b1 lo0563b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0563b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨3,by decide⟩
def hi0563b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨4,by decide⟩
def hi0563 : CheckedMoment :=
  CheckedMoment.ofBessel hi0563b1 hi0563b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0563 : meanBracketCheck (1691/10000) lo0563 hi0563=true := by decide +kernel
def bracket0563 : MeanBracket := meanBracketOfMoments (1691/10000) lo0563 hi0563 accepted0563
def lo0564b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨8,by decide⟩
def lo0564b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨9,by decide⟩
def lo0564 : CheckedMoment :=
  CheckedMoment.ofBessel lo0564b1 lo0564b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0564b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨13,by decide⟩
def hi0564b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨14,by decide⟩
def hi0564 : CheckedMoment :=
  CheckedMoment.ofBessel hi0564b1 hi0564b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0564 : meanBracketCheck (1693/10000) lo0564 hi0564=true := by decide +kernel
def bracket0564 : MeanBracket := meanBracketOfMoments (1693/10000) lo0564 hi0564 accepted0564
def lo0565b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨18,by decide⟩
def lo0565b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨19,by decide⟩
def lo0565 : CheckedMoment :=
  CheckedMoment.ofBessel lo0565b1 lo0565b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0565b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨23,by decide⟩
def hi0565b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨24,by decide⟩
def hi0565 : CheckedMoment :=
  CheckedMoment.ofBessel hi0565b1 hi0565b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0565 : meanBracketCheck (339/2000) lo0565 hi0565=true := by decide +kernel
def bracket0565 : MeanBracket := meanBracketOfMoments (339/2000) lo0565 hi0565 accepted0565
def lo0566b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨28,by decide⟩
def lo0566b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨29,by decide⟩
def lo0566 : CheckedMoment :=
  CheckedMoment.ofBessel lo0566b1 lo0566b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0566b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨33,by decide⟩
def hi0566b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨34,by decide⟩
def hi0566 : CheckedMoment :=
  CheckedMoment.ofBessel hi0566b1 hi0566b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0566 : meanBracketCheck (1697/10000) lo0566 hi0566=true := by decide +kernel
def bracket0566 : MeanBracket := meanBracketOfMoments (1697/10000) lo0566 hi0566 accepted0566
def lo0567b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨38,by decide⟩
def lo0567b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨39,by decide⟩
def lo0567 : CheckedMoment :=
  CheckedMoment.ofBessel lo0567b1 lo0567b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0567b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨43,by decide⟩
def hi0567b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨44,by decide⟩
def hi0567 : CheckedMoment :=
  CheckedMoment.ofBessel hi0567b1 hi0567b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0567 : meanBracketCheck (1699/10000) lo0567 hi0567=true := by decide +kernel
def bracket0567 : MeanBracket := meanBracketOfMoments (1699/10000) lo0567 hi0567 accepted0567
def lo0568b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨48,by decide⟩
def lo0568b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨49,by decide⟩
def lo0568 : CheckedMoment :=
  CheckedMoment.ofBessel lo0568b1 lo0568b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0568b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨53,by decide⟩
def hi0568b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨54,by decide⟩
def hi0568 : CheckedMoment :=
  CheckedMoment.ofBessel hi0568b1 hi0568b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0568 : meanBracketCheck (1701/10000) lo0568 hi0568=true := by decide +kernel
def bracket0568 : MeanBracket := meanBracketOfMoments (1701/10000) lo0568 hi0568 accepted0568
def lo0569b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨58,by decide⟩
def lo0569b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨59,by decide⟩
def lo0569 : CheckedMoment :=
  CheckedMoment.ofBessel lo0569b1 lo0569b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0569b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨63,by decide⟩
def hi0569b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨0,by decide⟩
def hi0569 : CheckedMoment :=
  CheckedMoment.ofBessel hi0569b1 hi0569b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0569 : meanBracketCheck (1703/10000) lo0569 hi0569=true := by decide +kernel
def bracket0569 : MeanBracket := meanBracketOfMoments (1703/10000) lo0569 hi0569 accepted0569
def lo0570b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨4,by decide⟩
def lo0570b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨5,by decide⟩
def lo0570 : CheckedMoment :=
  CheckedMoment.ofBessel lo0570b1 lo0570b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0570b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨9,by decide⟩
def hi0570b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨10,by decide⟩
def hi0570 : CheckedMoment :=
  CheckedMoment.ofBessel hi0570b1 hi0570b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0570 : meanBracketCheck (341/2000) lo0570 hi0570=true := by decide +kernel
def bracket0570 : MeanBracket := meanBracketOfMoments (341/2000) lo0570 hi0570 accepted0570
def lo0571b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨14,by decide⟩
def lo0571b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨15,by decide⟩
def lo0571 : CheckedMoment :=
  CheckedMoment.ofBessel lo0571b1 lo0571b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0571b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨19,by decide⟩
def hi0571b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨20,by decide⟩
def hi0571 : CheckedMoment :=
  CheckedMoment.ofBessel hi0571b1 hi0571b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0571 : meanBracketCheck (1707/10000) lo0571 hi0571=true := by decide +kernel
def bracket0571 : MeanBracket := meanBracketOfMoments (1707/10000) lo0571 hi0571 accepted0571
def lo0572b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨24,by decide⟩
def lo0572b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨25,by decide⟩
def lo0572 : CheckedMoment :=
  CheckedMoment.ofBessel lo0572b1 lo0572b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0572b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨29,by decide⟩
def hi0572b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨30,by decide⟩
def hi0572 : CheckedMoment :=
  CheckedMoment.ofBessel hi0572b1 hi0572b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0572 : meanBracketCheck (1709/10000) lo0572 hi0572=true := by decide +kernel
def bracket0572 : MeanBracket := meanBracketOfMoments (1709/10000) lo0572 hi0572 accepted0572
def lo0573b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨34,by decide⟩
def lo0573b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨35,by decide⟩
def lo0573 : CheckedMoment :=
  CheckedMoment.ofBessel lo0573b1 lo0573b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0573b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨39,by decide⟩
def hi0573b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨40,by decide⟩
def hi0573 : CheckedMoment :=
  CheckedMoment.ofBessel hi0573b1 hi0573b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0573 : meanBracketCheck (1711/10000) lo0573 hi0573=true := by decide +kernel
def bracket0573 : MeanBracket := meanBracketOfMoments (1711/10000) lo0573 hi0573 accepted0573
def lo0574b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨44,by decide⟩
def lo0574b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨45,by decide⟩
def lo0574 : CheckedMoment :=
  CheckedMoment.ofBessel lo0574b1 lo0574b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0574b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨49,by decide⟩
def hi0574b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨50,by decide⟩
def hi0574 : CheckedMoment :=
  CheckedMoment.ofBessel hi0574b1 hi0574b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0574 : meanBracketCheck (1713/10000) lo0574 hi0574=true := by decide +kernel
def bracket0574 : MeanBracket := meanBracketOfMoments (1713/10000) lo0574 hi0574 accepted0574
def lo0575b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨54,by decide⟩
def lo0575b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨55,by decide⟩
def lo0575 : CheckedMoment :=
  CheckedMoment.ofBessel lo0575b1 lo0575b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0575b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨59,by decide⟩
def hi0575b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨60,by decide⟩
def hi0575 : CheckedMoment :=
  CheckedMoment.ofBessel hi0575b1 hi0575b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0575 : meanBracketCheck (343/2000) lo0575 hi0575=true := by decide +kernel
def bracket0575 : MeanBracket := meanBracketOfMoments (343/2000) lo0575 hi0575 accepted0575
#print axioms bracket0560
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0035
