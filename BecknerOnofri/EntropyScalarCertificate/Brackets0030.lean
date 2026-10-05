import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0075
import BecknerOnofri.EntropyScalarCertificate.Bessel0076
import BecknerOnofri.EntropyScalarCertificate.Bessel0077
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0030
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0480b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨0,by decide⟩
def lo0480b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨1,by decide⟩
def lo0480 : CheckedMoment :=
  CheckedMoment.ofBessel lo0480b1 lo0480b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0480b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨5,by decide⟩
def hi0480b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨6,by decide⟩
def hi0480 : CheckedMoment :=
  CheckedMoment.ofBessel hi0480b1 hi0480b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0480 : meanBracketCheck (61/400) lo0480 hi0480=true := by decide +kernel
def bracket0480 : MeanBracket := meanBracketOfMoments (61/400) lo0480 hi0480 accepted0480
def lo0481b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨10,by decide⟩
def lo0481b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨11,by decide⟩
def lo0481 : CheckedMoment :=
  CheckedMoment.ofBessel lo0481b1 lo0481b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0481b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨15,by decide⟩
def hi0481b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨16,by decide⟩
def hi0481 : CheckedMoment :=
  CheckedMoment.ofBessel hi0481b1 hi0481b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0481 : meanBracketCheck (1527/10000) lo0481 hi0481=true := by decide +kernel
def bracket0481 : MeanBracket := meanBracketOfMoments (1527/10000) lo0481 hi0481 accepted0481
def lo0482b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨20,by decide⟩
def lo0482b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨21,by decide⟩
def lo0482 : CheckedMoment :=
  CheckedMoment.ofBessel lo0482b1 lo0482b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0482b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨25,by decide⟩
def hi0482b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨26,by decide⟩
def hi0482 : CheckedMoment :=
  CheckedMoment.ofBessel hi0482b1 hi0482b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0482 : meanBracketCheck (1529/10000) lo0482 hi0482=true := by decide +kernel
def bracket0482 : MeanBracket := meanBracketOfMoments (1529/10000) lo0482 hi0482 accepted0482
def lo0483b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨30,by decide⟩
def lo0483b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨31,by decide⟩
def lo0483 : CheckedMoment :=
  CheckedMoment.ofBessel lo0483b1 lo0483b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0483b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨35,by decide⟩
def hi0483b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨36,by decide⟩
def hi0483 : CheckedMoment :=
  CheckedMoment.ofBessel hi0483b1 hi0483b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0483 : meanBracketCheck (1531/10000) lo0483 hi0483=true := by decide +kernel
def bracket0483 : MeanBracket := meanBracketOfMoments (1531/10000) lo0483 hi0483 accepted0483
def lo0484b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨40,by decide⟩
def lo0484b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨41,by decide⟩
def lo0484 : CheckedMoment :=
  CheckedMoment.ofBessel lo0484b1 lo0484b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0484b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨45,by decide⟩
def hi0484b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨46,by decide⟩
def hi0484 : CheckedMoment :=
  CheckedMoment.ofBessel hi0484b1 hi0484b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0484 : meanBracketCheck (1533/10000) lo0484 hi0484=true := by decide +kernel
def bracket0484 : MeanBracket := meanBracketOfMoments (1533/10000) lo0484 hi0484 accepted0484
def lo0485b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨50,by decide⟩
def lo0485b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨51,by decide⟩
def lo0485 : CheckedMoment :=
  CheckedMoment.ofBessel lo0485b1 lo0485b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0485b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨55,by decide⟩
def hi0485b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨56,by decide⟩
def hi0485 : CheckedMoment :=
  CheckedMoment.ofBessel hi0485b1 hi0485b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0485 : meanBracketCheck (307/2000) lo0485 hi0485=true := by decide +kernel
def bracket0485 : MeanBracket := meanBracketOfMoments (307/2000) lo0485 hi0485 accepted0485
def lo0486b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨60,by decide⟩
def lo0486b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨61,by decide⟩
def lo0486 : CheckedMoment :=
  CheckedMoment.ofBessel lo0486b1 lo0486b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0486b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨1,by decide⟩
def hi0486b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨2,by decide⟩
def hi0486 : CheckedMoment :=
  CheckedMoment.ofBessel hi0486b1 hi0486b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0486 : meanBracketCheck (1537/10000) lo0486 hi0486=true := by decide +kernel
def bracket0486 : MeanBracket := meanBracketOfMoments (1537/10000) lo0486 hi0486 accepted0486
def lo0487b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨6,by decide⟩
def lo0487b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨7,by decide⟩
def lo0487 : CheckedMoment :=
  CheckedMoment.ofBessel lo0487b1 lo0487b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0487b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨11,by decide⟩
def hi0487b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨12,by decide⟩
def hi0487 : CheckedMoment :=
  CheckedMoment.ofBessel hi0487b1 hi0487b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0487 : meanBracketCheck (1539/10000) lo0487 hi0487=true := by decide +kernel
def bracket0487 : MeanBracket := meanBracketOfMoments (1539/10000) lo0487 hi0487 accepted0487
def lo0488b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨16,by decide⟩
def lo0488b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨17,by decide⟩
def lo0488 : CheckedMoment :=
  CheckedMoment.ofBessel lo0488b1 lo0488b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0488b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨21,by decide⟩
def hi0488b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨22,by decide⟩
def hi0488 : CheckedMoment :=
  CheckedMoment.ofBessel hi0488b1 hi0488b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0488 : meanBracketCheck (1541/10000) lo0488 hi0488=true := by decide +kernel
def bracket0488 : MeanBracket := meanBracketOfMoments (1541/10000) lo0488 hi0488 accepted0488
def lo0489b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨26,by decide⟩
def lo0489b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨27,by decide⟩
def lo0489 : CheckedMoment :=
  CheckedMoment.ofBessel lo0489b1 lo0489b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0489b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨31,by decide⟩
def hi0489b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨32,by decide⟩
def hi0489 : CheckedMoment :=
  CheckedMoment.ofBessel hi0489b1 hi0489b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0489 : meanBracketCheck (1543/10000) lo0489 hi0489=true := by decide +kernel
def bracket0489 : MeanBracket := meanBracketOfMoments (1543/10000) lo0489 hi0489 accepted0489
def lo0490b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨36,by decide⟩
def lo0490b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨37,by decide⟩
def lo0490 : CheckedMoment :=
  CheckedMoment.ofBessel lo0490b1 lo0490b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0490b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨41,by decide⟩
def hi0490b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨42,by decide⟩
def hi0490 : CheckedMoment :=
  CheckedMoment.ofBessel hi0490b1 hi0490b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0490 : meanBracketCheck (309/2000) lo0490 hi0490=true := by decide +kernel
def bracket0490 : MeanBracket := meanBracketOfMoments (309/2000) lo0490 hi0490 accepted0490
def lo0491b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨46,by decide⟩
def lo0491b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨47,by decide⟩
def lo0491 : CheckedMoment :=
  CheckedMoment.ofBessel lo0491b1 lo0491b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0491b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨51,by decide⟩
def hi0491b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨52,by decide⟩
def hi0491 : CheckedMoment :=
  CheckedMoment.ofBessel hi0491b1 hi0491b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0491 : meanBracketCheck (1547/10000) lo0491 hi0491=true := by decide +kernel
def bracket0491 : MeanBracket := meanBracketOfMoments (1547/10000) lo0491 hi0491 accepted0491
def lo0492b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨56,by decide⟩
def lo0492b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨57,by decide⟩
def lo0492 : CheckedMoment :=
  CheckedMoment.ofBessel lo0492b1 lo0492b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0492b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨61,by decide⟩
def hi0492b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨62,by decide⟩
def hi0492 : CheckedMoment :=
  CheckedMoment.ofBessel hi0492b1 hi0492b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0492 : meanBracketCheck (1549/10000) lo0492 hi0492=true := by decide +kernel
def bracket0492 : MeanBracket := meanBracketOfMoments (1549/10000) lo0492 hi0492 accepted0492
def lo0493b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨2,by decide⟩
def lo0493b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨3,by decide⟩
def lo0493 : CheckedMoment :=
  CheckedMoment.ofBessel lo0493b1 lo0493b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0493b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨7,by decide⟩
def hi0493b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨8,by decide⟩
def hi0493 : CheckedMoment :=
  CheckedMoment.ofBessel hi0493b1 hi0493b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0493 : meanBracketCheck (1551/10000) lo0493 hi0493=true := by decide +kernel
def bracket0493 : MeanBracket := meanBracketOfMoments (1551/10000) lo0493 hi0493 accepted0493
def lo0494b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨12,by decide⟩
def lo0494b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨13,by decide⟩
def lo0494 : CheckedMoment :=
  CheckedMoment.ofBessel lo0494b1 lo0494b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0494b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨17,by decide⟩
def hi0494b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨18,by decide⟩
def hi0494 : CheckedMoment :=
  CheckedMoment.ofBessel hi0494b1 hi0494b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0494 : meanBracketCheck (1553/10000) lo0494 hi0494=true := by decide +kernel
def bracket0494 : MeanBracket := meanBracketOfMoments (1553/10000) lo0494 hi0494 accepted0494
def lo0495b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨22,by decide⟩
def lo0495b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨23,by decide⟩
def lo0495 : CheckedMoment :=
  CheckedMoment.ofBessel lo0495b1 lo0495b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0495b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨27,by decide⟩
def hi0495b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨28,by decide⟩
def hi0495 : CheckedMoment :=
  CheckedMoment.ofBessel hi0495b1 hi0495b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0495 : meanBracketCheck (311/2000) lo0495 hi0495=true := by decide +kernel
def bracket0495 : MeanBracket := meanBracketOfMoments (311/2000) lo0495 hi0495 accepted0495
#print axioms bracket0480
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0030
