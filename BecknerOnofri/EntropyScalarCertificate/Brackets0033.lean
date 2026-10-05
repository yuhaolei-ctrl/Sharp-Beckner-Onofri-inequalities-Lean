import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0082
import BecknerOnofri.EntropyScalarCertificate.Bessel0083
import BecknerOnofri.EntropyScalarCertificate.Bessel0084
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0033
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0528b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨32,by decide⟩
def lo0528b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨33,by decide⟩
def lo0528 : CheckedMoment :=
  CheckedMoment.ofBessel lo0528b1 lo0528b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0528b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨37,by decide⟩
def hi0528b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨38,by decide⟩
def hi0528 : CheckedMoment :=
  CheckedMoment.ofBessel hi0528b1 hi0528b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0528 : meanBracketCheck (1621/10000) lo0528 hi0528=true := by decide +kernel
def bracket0528 : MeanBracket := meanBracketOfMoments (1621/10000) lo0528 hi0528 accepted0528
def lo0529b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨42,by decide⟩
def lo0529b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨43,by decide⟩
def lo0529 : CheckedMoment :=
  CheckedMoment.ofBessel lo0529b1 lo0529b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0529b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨47,by decide⟩
def hi0529b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨48,by decide⟩
def hi0529 : CheckedMoment :=
  CheckedMoment.ofBessel hi0529b1 hi0529b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0529 : meanBracketCheck (1623/10000) lo0529 hi0529=true := by decide +kernel
def bracket0529 : MeanBracket := meanBracketOfMoments (1623/10000) lo0529 hi0529 accepted0529
def lo0530b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨52,by decide⟩
def lo0530b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨53,by decide⟩
def lo0530 : CheckedMoment :=
  CheckedMoment.ofBessel lo0530b1 lo0530b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0530b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨57,by decide⟩
def hi0530b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨58,by decide⟩
def hi0530 : CheckedMoment :=
  CheckedMoment.ofBessel hi0530b1 hi0530b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0530 : meanBracketCheck (13/80) lo0530 hi0530=true := by decide +kernel
def bracket0530 : MeanBracket := meanBracketOfMoments (13/80) lo0530 hi0530 accepted0530
def lo0531b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨62,by decide⟩
def lo0531b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨63,by decide⟩
def lo0531 : CheckedMoment :=
  CheckedMoment.ofBessel lo0531b1 lo0531b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0531b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨3,by decide⟩
def hi0531b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨4,by decide⟩
def hi0531 : CheckedMoment :=
  CheckedMoment.ofBessel hi0531b1 hi0531b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0531 : meanBracketCheck (1627/10000) lo0531 hi0531=true := by decide +kernel
def bracket0531 : MeanBracket := meanBracketOfMoments (1627/10000) lo0531 hi0531 accepted0531
def lo0532b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨8,by decide⟩
def lo0532b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨9,by decide⟩
def lo0532 : CheckedMoment :=
  CheckedMoment.ofBessel lo0532b1 lo0532b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0532b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨13,by decide⟩
def hi0532b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨14,by decide⟩
def hi0532 : CheckedMoment :=
  CheckedMoment.ofBessel hi0532b1 hi0532b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0532 : meanBracketCheck (1629/10000) lo0532 hi0532=true := by decide +kernel
def bracket0532 : MeanBracket := meanBracketOfMoments (1629/10000) lo0532 hi0532 accepted0532
def lo0533b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨18,by decide⟩
def lo0533b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨19,by decide⟩
def lo0533 : CheckedMoment :=
  CheckedMoment.ofBessel lo0533b1 lo0533b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0533b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨23,by decide⟩
def hi0533b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨24,by decide⟩
def hi0533 : CheckedMoment :=
  CheckedMoment.ofBessel hi0533b1 hi0533b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0533 : meanBracketCheck (1631/10000) lo0533 hi0533=true := by decide +kernel
def bracket0533 : MeanBracket := meanBracketOfMoments (1631/10000) lo0533 hi0533 accepted0533
def lo0534b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨28,by decide⟩
def lo0534b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨29,by decide⟩
def lo0534 : CheckedMoment :=
  CheckedMoment.ofBessel lo0534b1 lo0534b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0534b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨33,by decide⟩
def hi0534b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨34,by decide⟩
def hi0534 : CheckedMoment :=
  CheckedMoment.ofBessel hi0534b1 hi0534b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0534 : meanBracketCheck (1633/10000) lo0534 hi0534=true := by decide +kernel
def bracket0534 : MeanBracket := meanBracketOfMoments (1633/10000) lo0534 hi0534 accepted0534
def lo0535b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨38,by decide⟩
def lo0535b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨39,by decide⟩
def lo0535 : CheckedMoment :=
  CheckedMoment.ofBessel lo0535b1 lo0535b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0535b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨43,by decide⟩
def hi0535b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨44,by decide⟩
def hi0535 : CheckedMoment :=
  CheckedMoment.ofBessel hi0535b1 hi0535b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0535 : meanBracketCheck (327/2000) lo0535 hi0535=true := by decide +kernel
def bracket0535 : MeanBracket := meanBracketOfMoments (327/2000) lo0535 hi0535 accepted0535
def lo0536b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨48,by decide⟩
def lo0536b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨49,by decide⟩
def lo0536 : CheckedMoment :=
  CheckedMoment.ofBessel lo0536b1 lo0536b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0536b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨53,by decide⟩
def hi0536b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨54,by decide⟩
def hi0536 : CheckedMoment :=
  CheckedMoment.ofBessel hi0536b1 hi0536b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0536 : meanBracketCheck (1637/10000) lo0536 hi0536=true := by decide +kernel
def bracket0536 : MeanBracket := meanBracketOfMoments (1637/10000) lo0536 hi0536 accepted0536
def lo0537b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨58,by decide⟩
def lo0537b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨59,by decide⟩
def lo0537 : CheckedMoment :=
  CheckedMoment.ofBessel lo0537b1 lo0537b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0537b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0083.rows BesselBatch0083.accepted ⟨63,by decide⟩
def hi0537b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨0,by decide⟩
def hi0537 : CheckedMoment :=
  CheckedMoment.ofBessel hi0537b1 hi0537b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0537 : meanBracketCheck (1639/10000) lo0537 hi0537=true := by decide +kernel
def bracket0537 : MeanBracket := meanBracketOfMoments (1639/10000) lo0537 hi0537 accepted0537
def lo0538b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨4,by decide⟩
def lo0538b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨5,by decide⟩
def lo0538 : CheckedMoment :=
  CheckedMoment.ofBessel lo0538b1 lo0538b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0538b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨9,by decide⟩
def hi0538b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨10,by decide⟩
def hi0538 : CheckedMoment :=
  CheckedMoment.ofBessel hi0538b1 hi0538b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0538 : meanBracketCheck (1641/10000) lo0538 hi0538=true := by decide +kernel
def bracket0538 : MeanBracket := meanBracketOfMoments (1641/10000) lo0538 hi0538 accepted0538
def lo0539b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨14,by decide⟩
def lo0539b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨15,by decide⟩
def lo0539 : CheckedMoment :=
  CheckedMoment.ofBessel lo0539b1 lo0539b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0539b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨19,by decide⟩
def hi0539b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨20,by decide⟩
def hi0539 : CheckedMoment :=
  CheckedMoment.ofBessel hi0539b1 hi0539b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0539 : meanBracketCheck (1643/10000) lo0539 hi0539=true := by decide +kernel
def bracket0539 : MeanBracket := meanBracketOfMoments (1643/10000) lo0539 hi0539 accepted0539
def lo0540b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨24,by decide⟩
def lo0540b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨25,by decide⟩
def lo0540 : CheckedMoment :=
  CheckedMoment.ofBessel lo0540b1 lo0540b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0540b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨29,by decide⟩
def hi0540b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨30,by decide⟩
def hi0540 : CheckedMoment :=
  CheckedMoment.ofBessel hi0540b1 hi0540b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0540 : meanBracketCheck (329/2000) lo0540 hi0540=true := by decide +kernel
def bracket0540 : MeanBracket := meanBracketOfMoments (329/2000) lo0540 hi0540 accepted0540
def lo0541b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨34,by decide⟩
def lo0541b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨35,by decide⟩
def lo0541 : CheckedMoment :=
  CheckedMoment.ofBessel lo0541b1 lo0541b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0541b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨39,by decide⟩
def hi0541b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨40,by decide⟩
def hi0541 : CheckedMoment :=
  CheckedMoment.ofBessel hi0541b1 hi0541b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0541 : meanBracketCheck (1647/10000) lo0541 hi0541=true := by decide +kernel
def bracket0541 : MeanBracket := meanBracketOfMoments (1647/10000) lo0541 hi0541 accepted0541
def lo0542b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨44,by decide⟩
def lo0542b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨45,by decide⟩
def lo0542 : CheckedMoment :=
  CheckedMoment.ofBessel lo0542b1 lo0542b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0542b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨49,by decide⟩
def hi0542b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨50,by decide⟩
def hi0542 : CheckedMoment :=
  CheckedMoment.ofBessel hi0542b1 hi0542b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0542 : meanBracketCheck (1649/10000) lo0542 hi0542=true := by decide +kernel
def bracket0542 : MeanBracket := meanBracketOfMoments (1649/10000) lo0542 hi0542 accepted0542
def lo0543b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨54,by decide⟩
def lo0543b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨55,by decide⟩
def lo0543 : CheckedMoment :=
  CheckedMoment.ofBessel lo0543b1 lo0543b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0543b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨59,by decide⟩
def hi0543b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0084.rows BesselBatch0084.accepted ⟨60,by decide⟩
def hi0543 : CheckedMoment :=
  CheckedMoment.ofBessel hi0543b1 hi0543b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0543 : meanBracketCheck (1651/10000) lo0543 hi0543=true := by decide +kernel
def bracket0543 : MeanBracket := meanBracketOfMoments (1651/10000) lo0543 hi0543 accepted0543
#print axioms bracket0528
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0033
