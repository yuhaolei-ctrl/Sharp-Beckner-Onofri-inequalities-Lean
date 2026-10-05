module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0077
public import BecknerOnofri.EntropyScalarCertificate.Bessel0078
public import BecknerOnofri.EntropyScalarCertificate.Bessel0079

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0031
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0496b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨32,by decide⟩
def lo0496b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨33,by decide⟩
def lo0496 : CheckedMoment :=
  CheckedMoment.ofBessel lo0496b1 lo0496b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0496b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨37,by decide⟩
def hi0496b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨38,by decide⟩
def hi0496 : CheckedMoment :=
  CheckedMoment.ofBessel hi0496b1 hi0496b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0496 : meanBracketCheck (1557/10000) lo0496 hi0496=true := by decide +kernel
def bracket0496 : MeanBracket := meanBracketOfMoments (1557/10000) lo0496 hi0496 accepted0496
def lo0497b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨42,by decide⟩
def lo0497b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨43,by decide⟩
def lo0497 : CheckedMoment :=
  CheckedMoment.ofBessel lo0497b1 lo0497b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0497b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨47,by decide⟩
def hi0497b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨48,by decide⟩
def hi0497 : CheckedMoment :=
  CheckedMoment.ofBessel hi0497b1 hi0497b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0497 : meanBracketCheck (1559/10000) lo0497 hi0497=true := by decide +kernel
def bracket0497 : MeanBracket := meanBracketOfMoments (1559/10000) lo0497 hi0497 accepted0497
def lo0498b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨52,by decide⟩
def lo0498b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨53,by decide⟩
def lo0498 : CheckedMoment :=
  CheckedMoment.ofBessel lo0498b1 lo0498b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0498b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨57,by decide⟩
def hi0498b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨58,by decide⟩
def hi0498 : CheckedMoment :=
  CheckedMoment.ofBessel hi0498b1 hi0498b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0498 : meanBracketCheck (1561/10000) lo0498 hi0498=true := by decide +kernel
def bracket0498 : MeanBracket := meanBracketOfMoments (1561/10000) lo0498 hi0498 accepted0498
def lo0499b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨62,by decide⟩
def lo0499b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨63,by decide⟩
def lo0499 : CheckedMoment :=
  CheckedMoment.ofBessel lo0499b1 lo0499b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0499b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨3,by decide⟩
def hi0499b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨4,by decide⟩
def hi0499 : CheckedMoment :=
  CheckedMoment.ofBessel hi0499b1 hi0499b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0499 : meanBracketCheck (1563/10000) lo0499 hi0499=true := by decide +kernel
def bracket0499 : MeanBracket := meanBracketOfMoments (1563/10000) lo0499 hi0499 accepted0499
def lo0500b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨8,by decide⟩
def lo0500b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨9,by decide⟩
def lo0500 : CheckedMoment :=
  CheckedMoment.ofBessel lo0500b1 lo0500b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0500b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨13,by decide⟩
def hi0500b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨14,by decide⟩
def hi0500 : CheckedMoment :=
  CheckedMoment.ofBessel hi0500b1 hi0500b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0500 : meanBracketCheck (313/2000) lo0500 hi0500=true := by decide +kernel
def bracket0500 : MeanBracket := meanBracketOfMoments (313/2000) lo0500 hi0500 accepted0500
def lo0501b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨18,by decide⟩
def lo0501b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨19,by decide⟩
def lo0501 : CheckedMoment :=
  CheckedMoment.ofBessel lo0501b1 lo0501b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0501b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨23,by decide⟩
def hi0501b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨24,by decide⟩
def hi0501 : CheckedMoment :=
  CheckedMoment.ofBessel hi0501b1 hi0501b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0501 : meanBracketCheck (1567/10000) lo0501 hi0501=true := by decide +kernel
def bracket0501 : MeanBracket := meanBracketOfMoments (1567/10000) lo0501 hi0501 accepted0501
def lo0502b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨28,by decide⟩
def lo0502b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨29,by decide⟩
def lo0502 : CheckedMoment :=
  CheckedMoment.ofBessel lo0502b1 lo0502b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0502b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨33,by decide⟩
def hi0502b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨34,by decide⟩
def hi0502 : CheckedMoment :=
  CheckedMoment.ofBessel hi0502b1 hi0502b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0502 : meanBracketCheck (1569/10000) lo0502 hi0502=true := by decide +kernel
def bracket0502 : MeanBracket := meanBracketOfMoments (1569/10000) lo0502 hi0502 accepted0502
def lo0503b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨38,by decide⟩
def lo0503b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨39,by decide⟩
def lo0503 : CheckedMoment :=
  CheckedMoment.ofBessel lo0503b1 lo0503b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0503b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨43,by decide⟩
def hi0503b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨44,by decide⟩
def hi0503 : CheckedMoment :=
  CheckedMoment.ofBessel hi0503b1 hi0503b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0503 : meanBracketCheck (1571/10000) lo0503 hi0503=true := by decide +kernel
def bracket0503 : MeanBracket := meanBracketOfMoments (1571/10000) lo0503 hi0503 accepted0503
def lo0504b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨48,by decide⟩
def lo0504b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨49,by decide⟩
def lo0504 : CheckedMoment :=
  CheckedMoment.ofBessel lo0504b1 lo0504b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0504b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨53,by decide⟩
def hi0504b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨54,by decide⟩
def hi0504 : CheckedMoment :=
  CheckedMoment.ofBessel hi0504b1 hi0504b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0504 : meanBracketCheck (1573/10000) lo0504 hi0504=true := by decide +kernel
def bracket0504 : MeanBracket := meanBracketOfMoments (1573/10000) lo0504 hi0504 accepted0504
def lo0505b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨58,by decide⟩
def lo0505b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨59,by decide⟩
def lo0505 : CheckedMoment :=
  CheckedMoment.ofBessel lo0505b1 lo0505b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0505b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨63,by decide⟩
def hi0505b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨0,by decide⟩
def hi0505 : CheckedMoment :=
  CheckedMoment.ofBessel hi0505b1 hi0505b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0505 : meanBracketCheck (63/400) lo0505 hi0505=true := by decide +kernel
def bracket0505 : MeanBracket := meanBracketOfMoments (63/400) lo0505 hi0505 accepted0505
def lo0506b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨4,by decide⟩
def lo0506b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨5,by decide⟩
def lo0506 : CheckedMoment :=
  CheckedMoment.ofBessel lo0506b1 lo0506b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0506b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨9,by decide⟩
def hi0506b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨10,by decide⟩
def hi0506 : CheckedMoment :=
  CheckedMoment.ofBessel hi0506b1 hi0506b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0506 : meanBracketCheck (1577/10000) lo0506 hi0506=true := by decide +kernel
def bracket0506 : MeanBracket := meanBracketOfMoments (1577/10000) lo0506 hi0506 accepted0506
def lo0507b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨14,by decide⟩
def lo0507b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨15,by decide⟩
def lo0507 : CheckedMoment :=
  CheckedMoment.ofBessel lo0507b1 lo0507b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0507b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨19,by decide⟩
def hi0507b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨20,by decide⟩
def hi0507 : CheckedMoment :=
  CheckedMoment.ofBessel hi0507b1 hi0507b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0507 : meanBracketCheck (1579/10000) lo0507 hi0507=true := by decide +kernel
def bracket0507 : MeanBracket := meanBracketOfMoments (1579/10000) lo0507 hi0507 accepted0507
def lo0508b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨24,by decide⟩
def lo0508b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨25,by decide⟩
def lo0508 : CheckedMoment :=
  CheckedMoment.ofBessel lo0508b1 lo0508b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0508b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨29,by decide⟩
def hi0508b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨30,by decide⟩
def hi0508 : CheckedMoment :=
  CheckedMoment.ofBessel hi0508b1 hi0508b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0508 : meanBracketCheck (1581/10000) lo0508 hi0508=true := by decide +kernel
def bracket0508 : MeanBracket := meanBracketOfMoments (1581/10000) lo0508 hi0508 accepted0508
def lo0509b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨34,by decide⟩
def lo0509b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨35,by decide⟩
def lo0509 : CheckedMoment :=
  CheckedMoment.ofBessel lo0509b1 lo0509b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0509b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨39,by decide⟩
def hi0509b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨40,by decide⟩
def hi0509 : CheckedMoment :=
  CheckedMoment.ofBessel hi0509b1 hi0509b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0509 : meanBracketCheck (1583/10000) lo0509 hi0509=true := by decide +kernel
def bracket0509 : MeanBracket := meanBracketOfMoments (1583/10000) lo0509 hi0509 accepted0509
def lo0510b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨44,by decide⟩
def lo0510b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨45,by decide⟩
def lo0510 : CheckedMoment :=
  CheckedMoment.ofBessel lo0510b1 lo0510b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0510b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨49,by decide⟩
def hi0510b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨50,by decide⟩
def hi0510 : CheckedMoment :=
  CheckedMoment.ofBessel hi0510b1 hi0510b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0510 : meanBracketCheck (317/2000) lo0510 hi0510=true := by decide +kernel
def bracket0510 : MeanBracket := meanBracketOfMoments (317/2000) lo0510 hi0510 accepted0510
def lo0511b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨54,by decide⟩
def lo0511b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨55,by decide⟩
def lo0511 : CheckedMoment :=
  CheckedMoment.ofBessel lo0511b1 lo0511b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0511b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨59,by decide⟩
def hi0511b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨60,by decide⟩
def hi0511 : CheckedMoment :=
  CheckedMoment.ofBessel hi0511b1 hi0511b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0511 : meanBracketCheck (1587/10000) lo0511 hi0511=true := by decide +kernel
def bracket0511 : MeanBracket := meanBracketOfMoments (1587/10000) lo0511 hi0511 accepted0511
#print axioms bracket0496
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0031
