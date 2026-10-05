import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0085
import BecknerOnofri.EntropyScalarCertificate.Bessel0086
import BecknerOnofri.EntropyScalarCertificate.Bessel0087
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0034
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0544b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨0,by decide⟩
def lo0544b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨1,by decide⟩
def lo0544 : CheckedMoment :=
  CheckedMoment.ofBessel lo0544b1 lo0544b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0544b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨5,by decide⟩
def hi0544b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨6,by decide⟩
def hi0544 : CheckedMoment :=
  CheckedMoment.ofBessel hi0544b1 hi0544b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0544 : meanBracketCheck (1653/10000) lo0544 hi0544=true := by decide +kernel
def bracket0544 : MeanBracket := meanBracketOfMoments (1653/10000) lo0544 hi0544 accepted0544
def lo0545b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨10,by decide⟩
def lo0545b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨11,by decide⟩
def lo0545 : CheckedMoment :=
  CheckedMoment.ofBessel lo0545b1 lo0545b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0545b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨15,by decide⟩
def hi0545b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨16,by decide⟩
def hi0545 : CheckedMoment :=
  CheckedMoment.ofBessel hi0545b1 hi0545b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0545 : meanBracketCheck (331/2000) lo0545 hi0545=true := by decide +kernel
def bracket0545 : MeanBracket := meanBracketOfMoments (331/2000) lo0545 hi0545 accepted0545
def lo0546b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨20,by decide⟩
def lo0546b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨21,by decide⟩
def lo0546 : CheckedMoment :=
  CheckedMoment.ofBessel lo0546b1 lo0546b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0546b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨25,by decide⟩
def hi0546b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨26,by decide⟩
def hi0546 : CheckedMoment :=
  CheckedMoment.ofBessel hi0546b1 hi0546b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0546 : meanBracketCheck (1657/10000) lo0546 hi0546=true := by decide +kernel
def bracket0546 : MeanBracket := meanBracketOfMoments (1657/10000) lo0546 hi0546 accepted0546
def lo0547b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨30,by decide⟩
def lo0547b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨31,by decide⟩
def lo0547 : CheckedMoment :=
  CheckedMoment.ofBessel lo0547b1 lo0547b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0547b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨35,by decide⟩
def hi0547b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨36,by decide⟩
def hi0547 : CheckedMoment :=
  CheckedMoment.ofBessel hi0547b1 hi0547b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0547 : meanBracketCheck (1659/10000) lo0547 hi0547=true := by decide +kernel
def bracket0547 : MeanBracket := meanBracketOfMoments (1659/10000) lo0547 hi0547 accepted0547
def lo0548b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨40,by decide⟩
def lo0548b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨41,by decide⟩
def lo0548 : CheckedMoment :=
  CheckedMoment.ofBessel lo0548b1 lo0548b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0548b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨45,by decide⟩
def hi0548b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨46,by decide⟩
def hi0548 : CheckedMoment :=
  CheckedMoment.ofBessel hi0548b1 hi0548b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0548 : meanBracketCheck (1661/10000) lo0548 hi0548=true := by decide +kernel
def bracket0548 : MeanBracket := meanBracketOfMoments (1661/10000) lo0548 hi0548 accepted0548
def lo0549b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨50,by decide⟩
def lo0549b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨51,by decide⟩
def lo0549 : CheckedMoment :=
  CheckedMoment.ofBessel lo0549b1 lo0549b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0549b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨55,by decide⟩
def hi0549b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨56,by decide⟩
def hi0549 : CheckedMoment :=
  CheckedMoment.ofBessel hi0549b1 hi0549b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0549 : meanBracketCheck (1663/10000) lo0549 hi0549=true := by decide +kernel
def bracket0549 : MeanBracket := meanBracketOfMoments (1663/10000) lo0549 hi0549 accepted0549
def lo0550b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨60,by decide⟩
def lo0550b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨61,by decide⟩
def lo0550 : CheckedMoment :=
  CheckedMoment.ofBessel lo0550b1 lo0550b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0550b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨1,by decide⟩
def hi0550b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨2,by decide⟩
def hi0550 : CheckedMoment :=
  CheckedMoment.ofBessel hi0550b1 hi0550b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0550 : meanBracketCheck (333/2000) lo0550 hi0550=true := by decide +kernel
def bracket0550 : MeanBracket := meanBracketOfMoments (333/2000) lo0550 hi0550 accepted0550
def lo0551b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨6,by decide⟩
def lo0551b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨7,by decide⟩
def lo0551 : CheckedMoment :=
  CheckedMoment.ofBessel lo0551b1 lo0551b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0551b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨11,by decide⟩
def hi0551b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨12,by decide⟩
def hi0551 : CheckedMoment :=
  CheckedMoment.ofBessel hi0551b1 hi0551b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0551 : meanBracketCheck (1667/10000) lo0551 hi0551=true := by decide +kernel
def bracket0551 : MeanBracket := meanBracketOfMoments (1667/10000) lo0551 hi0551 accepted0551
def lo0552b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨16,by decide⟩
def lo0552b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨17,by decide⟩
def lo0552 : CheckedMoment :=
  CheckedMoment.ofBessel lo0552b1 lo0552b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0552b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨21,by decide⟩
def hi0552b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨22,by decide⟩
def hi0552 : CheckedMoment :=
  CheckedMoment.ofBessel hi0552b1 hi0552b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0552 : meanBracketCheck (1669/10000) lo0552 hi0552=true := by decide +kernel
def bracket0552 : MeanBracket := meanBracketOfMoments (1669/10000) lo0552 hi0552 accepted0552
def lo0553b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨26,by decide⟩
def lo0553b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨27,by decide⟩
def lo0553 : CheckedMoment :=
  CheckedMoment.ofBessel lo0553b1 lo0553b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0553b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨31,by decide⟩
def hi0553b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨32,by decide⟩
def hi0553 : CheckedMoment :=
  CheckedMoment.ofBessel hi0553b1 hi0553b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0553 : meanBracketCheck (1671/10000) lo0553 hi0553=true := by decide +kernel
def bracket0553 : MeanBracket := meanBracketOfMoments (1671/10000) lo0553 hi0553 accepted0553
def lo0554b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨36,by decide⟩
def lo0554b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨37,by decide⟩
def lo0554 : CheckedMoment :=
  CheckedMoment.ofBessel lo0554b1 lo0554b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0554b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨41,by decide⟩
def hi0554b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨42,by decide⟩
def hi0554 : CheckedMoment :=
  CheckedMoment.ofBessel hi0554b1 hi0554b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0554 : meanBracketCheck (1673/10000) lo0554 hi0554=true := by decide +kernel
def bracket0554 : MeanBracket := meanBracketOfMoments (1673/10000) lo0554 hi0554 accepted0554
def lo0555b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨46,by decide⟩
def lo0555b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨47,by decide⟩
def lo0555 : CheckedMoment :=
  CheckedMoment.ofBessel lo0555b1 lo0555b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0555b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨51,by decide⟩
def hi0555b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨52,by decide⟩
def hi0555 : CheckedMoment :=
  CheckedMoment.ofBessel hi0555b1 hi0555b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0555 : meanBracketCheck (67/400) lo0555 hi0555=true := by decide +kernel
def bracket0555 : MeanBracket := meanBracketOfMoments (67/400) lo0555 hi0555 accepted0555
def lo0556b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨56,by decide⟩
def lo0556b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨57,by decide⟩
def lo0556 : CheckedMoment :=
  CheckedMoment.ofBessel lo0556b1 lo0556b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0556b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨61,by decide⟩
def hi0556b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨62,by decide⟩
def hi0556 : CheckedMoment :=
  CheckedMoment.ofBessel hi0556b1 hi0556b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0556 : meanBracketCheck (1677/10000) lo0556 hi0556=true := by decide +kernel
def bracket0556 : MeanBracket := meanBracketOfMoments (1677/10000) lo0556 hi0556 accepted0556
def lo0557b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨2,by decide⟩
def lo0557b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨3,by decide⟩
def lo0557 : CheckedMoment :=
  CheckedMoment.ofBessel lo0557b1 lo0557b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0557b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨7,by decide⟩
def hi0557b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨8,by decide⟩
def hi0557 : CheckedMoment :=
  CheckedMoment.ofBessel hi0557b1 hi0557b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0557 : meanBracketCheck (1679/10000) lo0557 hi0557=true := by decide +kernel
def bracket0557 : MeanBracket := meanBracketOfMoments (1679/10000) lo0557 hi0557 accepted0557
def lo0558b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨12,by decide⟩
def lo0558b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨13,by decide⟩
def lo0558 : CheckedMoment :=
  CheckedMoment.ofBessel lo0558b1 lo0558b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0558b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨17,by decide⟩
def hi0558b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨18,by decide⟩
def hi0558 : CheckedMoment :=
  CheckedMoment.ofBessel hi0558b1 hi0558b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0558 : meanBracketCheck (1681/10000) lo0558 hi0558=true := by decide +kernel
def bracket0558 : MeanBracket := meanBracketOfMoments (1681/10000) lo0558 hi0558 accepted0558
def lo0559b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨22,by decide⟩
def lo0559b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨23,by decide⟩
def lo0559 : CheckedMoment :=
  CheckedMoment.ofBessel lo0559b1 lo0559b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0559b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨27,by decide⟩
def hi0559b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨28,by decide⟩
def hi0559 : CheckedMoment :=
  CheckedMoment.ofBessel hi0559b1 hi0559b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0559 : meanBracketCheck (1683/10000) lo0559 hi0559=true := by decide +kernel
def bracket0559 : MeanBracket := meanBracketOfMoments (1683/10000) lo0559 hi0559 accepted0559
#print axioms bracket0544
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0034
