import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0095
import BecknerOnofri.EntropyScalarCertificate.Bessel0096
import BecknerOnofri.EntropyScalarCertificate.Bessel0097
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0038
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0608b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨0,by decide⟩
def lo0608b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨1,by decide⟩
def lo0608 : CheckedMoment :=
  CheckedMoment.ofBessel lo0608b1 lo0608b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0608b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨5,by decide⟩
def hi0608b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨6,by decide⟩
def hi0608 : CheckedMoment :=
  CheckedMoment.ofBessel hi0608b1 hi0608b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0608 : meanBracketCheck (1781/10000) lo0608 hi0608=true := by decide +kernel
def bracket0608 : MeanBracket := meanBracketOfMoments (1781/10000) lo0608 hi0608 accepted0608
def lo0609b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨10,by decide⟩
def lo0609b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨11,by decide⟩
def lo0609 : CheckedMoment :=
  CheckedMoment.ofBessel lo0609b1 lo0609b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0609b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨15,by decide⟩
def hi0609b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨16,by decide⟩
def hi0609 : CheckedMoment :=
  CheckedMoment.ofBessel hi0609b1 hi0609b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0609 : meanBracketCheck (1783/10000) lo0609 hi0609=true := by decide +kernel
def bracket0609 : MeanBracket := meanBracketOfMoments (1783/10000) lo0609 hi0609 accepted0609
def lo0610b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨20,by decide⟩
def lo0610b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨21,by decide⟩
def lo0610 : CheckedMoment :=
  CheckedMoment.ofBessel lo0610b1 lo0610b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0610b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨25,by decide⟩
def hi0610b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨26,by decide⟩
def hi0610 : CheckedMoment :=
  CheckedMoment.ofBessel hi0610b1 hi0610b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0610 : meanBracketCheck (357/2000) lo0610 hi0610=true := by decide +kernel
def bracket0610 : MeanBracket := meanBracketOfMoments (357/2000) lo0610 hi0610 accepted0610
def lo0611b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨30,by decide⟩
def lo0611b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨31,by decide⟩
def lo0611 : CheckedMoment :=
  CheckedMoment.ofBessel lo0611b1 lo0611b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0611b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨35,by decide⟩
def hi0611b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨36,by decide⟩
def hi0611 : CheckedMoment :=
  CheckedMoment.ofBessel hi0611b1 hi0611b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0611 : meanBracketCheck (1787/10000) lo0611 hi0611=true := by decide +kernel
def bracket0611 : MeanBracket := meanBracketOfMoments (1787/10000) lo0611 hi0611 accepted0611
def lo0612b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨40,by decide⟩
def lo0612b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨41,by decide⟩
def lo0612 : CheckedMoment :=
  CheckedMoment.ofBessel lo0612b1 lo0612b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0612b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨45,by decide⟩
def hi0612b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨46,by decide⟩
def hi0612 : CheckedMoment :=
  CheckedMoment.ofBessel hi0612b1 hi0612b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0612 : meanBracketCheck (1789/10000) lo0612 hi0612=true := by decide +kernel
def bracket0612 : MeanBracket := meanBracketOfMoments (1789/10000) lo0612 hi0612 accepted0612
def lo0613b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨50,by decide⟩
def lo0613b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨51,by decide⟩
def lo0613 : CheckedMoment :=
  CheckedMoment.ofBessel lo0613b1 lo0613b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0613b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨55,by decide⟩
def hi0613b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨56,by decide⟩
def hi0613 : CheckedMoment :=
  CheckedMoment.ofBessel hi0613b1 hi0613b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0613 : meanBracketCheck (1791/10000) lo0613 hi0613=true := by decide +kernel
def bracket0613 : MeanBracket := meanBracketOfMoments (1791/10000) lo0613 hi0613 accepted0613
def lo0614b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨60,by decide⟩
def lo0614b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨61,by decide⟩
def lo0614 : CheckedMoment :=
  CheckedMoment.ofBessel lo0614b1 lo0614b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0614b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨1,by decide⟩
def hi0614b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨2,by decide⟩
def hi0614 : CheckedMoment :=
  CheckedMoment.ofBessel hi0614b1 hi0614b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0614 : meanBracketCheck (1793/10000) lo0614 hi0614=true := by decide +kernel
def bracket0614 : MeanBracket := meanBracketOfMoments (1793/10000) lo0614 hi0614 accepted0614
def lo0615b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨6,by decide⟩
def lo0615b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨7,by decide⟩
def lo0615 : CheckedMoment :=
  CheckedMoment.ofBessel lo0615b1 lo0615b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0615b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨11,by decide⟩
def hi0615b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨12,by decide⟩
def hi0615 : CheckedMoment :=
  CheckedMoment.ofBessel hi0615b1 hi0615b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0615 : meanBracketCheck (359/2000) lo0615 hi0615=true := by decide +kernel
def bracket0615 : MeanBracket := meanBracketOfMoments (359/2000) lo0615 hi0615 accepted0615
def lo0616b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨16,by decide⟩
def lo0616b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨17,by decide⟩
def lo0616 : CheckedMoment :=
  CheckedMoment.ofBessel lo0616b1 lo0616b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0616b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨21,by decide⟩
def hi0616b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨22,by decide⟩
def hi0616 : CheckedMoment :=
  CheckedMoment.ofBessel hi0616b1 hi0616b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0616 : meanBracketCheck (1797/10000) lo0616 hi0616=true := by decide +kernel
def bracket0616 : MeanBracket := meanBracketOfMoments (1797/10000) lo0616 hi0616 accepted0616
def lo0617b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨26,by decide⟩
def lo0617b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨27,by decide⟩
def lo0617 : CheckedMoment :=
  CheckedMoment.ofBessel lo0617b1 lo0617b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0617b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨31,by decide⟩
def hi0617b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨32,by decide⟩
def hi0617 : CheckedMoment :=
  CheckedMoment.ofBessel hi0617b1 hi0617b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0617 : meanBracketCheck (1799/10000) lo0617 hi0617=true := by decide +kernel
def bracket0617 : MeanBracket := meanBracketOfMoments (1799/10000) lo0617 hi0617 accepted0617
def lo0618b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨36,by decide⟩
def lo0618b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨37,by decide⟩
def lo0618 : CheckedMoment :=
  CheckedMoment.ofBessel lo0618b1 lo0618b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0618b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨41,by decide⟩
def hi0618b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨42,by decide⟩
def hi0618 : CheckedMoment :=
  CheckedMoment.ofBessel hi0618b1 hi0618b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0618 : meanBracketCheck (1801/10000) lo0618 hi0618=true := by decide +kernel
def bracket0618 : MeanBracket := meanBracketOfMoments (1801/10000) lo0618 hi0618 accepted0618
def lo0619b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨46,by decide⟩
def lo0619b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨47,by decide⟩
def lo0619 : CheckedMoment :=
  CheckedMoment.ofBessel lo0619b1 lo0619b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0619b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨51,by decide⟩
def hi0619b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨52,by decide⟩
def hi0619 : CheckedMoment :=
  CheckedMoment.ofBessel hi0619b1 hi0619b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0619 : meanBracketCheck (1803/10000) lo0619 hi0619=true := by decide +kernel
def bracket0619 : MeanBracket := meanBracketOfMoments (1803/10000) lo0619 hi0619 accepted0619
def lo0620b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨56,by decide⟩
def lo0620b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨57,by decide⟩
def lo0620 : CheckedMoment :=
  CheckedMoment.ofBessel lo0620b1 lo0620b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0620b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨61,by decide⟩
def hi0620b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨62,by decide⟩
def hi0620 : CheckedMoment :=
  CheckedMoment.ofBessel hi0620b1 hi0620b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0620 : meanBracketCheck (361/2000) lo0620 hi0620=true := by decide +kernel
def bracket0620 : MeanBracket := meanBracketOfMoments (361/2000) lo0620 hi0620 accepted0620
def lo0621b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨2,by decide⟩
def lo0621b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨3,by decide⟩
def lo0621 : CheckedMoment :=
  CheckedMoment.ofBessel lo0621b1 lo0621b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0621b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨7,by decide⟩
def hi0621b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨8,by decide⟩
def hi0621 : CheckedMoment :=
  CheckedMoment.ofBessel hi0621b1 hi0621b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0621 : meanBracketCheck (1807/10000) lo0621 hi0621=true := by decide +kernel
def bracket0621 : MeanBracket := meanBracketOfMoments (1807/10000) lo0621 hi0621 accepted0621
def lo0622b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨12,by decide⟩
def lo0622b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨13,by decide⟩
def lo0622 : CheckedMoment :=
  CheckedMoment.ofBessel lo0622b1 lo0622b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0622b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨17,by decide⟩
def hi0622b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨18,by decide⟩
def hi0622 : CheckedMoment :=
  CheckedMoment.ofBessel hi0622b1 hi0622b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0622 : meanBracketCheck (1809/10000) lo0622 hi0622=true := by decide +kernel
def bracket0622 : MeanBracket := meanBracketOfMoments (1809/10000) lo0622 hi0622 accepted0622
def lo0623b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨22,by decide⟩
def lo0623b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨23,by decide⟩
def lo0623 : CheckedMoment :=
  CheckedMoment.ofBessel lo0623b1 lo0623b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0623b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨27,by decide⟩
def hi0623b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨28,by decide⟩
def hi0623 : CheckedMoment :=
  CheckedMoment.ofBessel hi0623b1 hi0623b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0623 : meanBracketCheck (1811/10000) lo0623 hi0623=true := by decide +kernel
def bracket0623 : MeanBracket := meanBracketOfMoments (1811/10000) lo0623 hi0623 accepted0623
#print axioms bracket0608
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0038
