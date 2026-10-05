import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0080
import BecknerOnofri.EntropyScalarCertificate.Bessel0081
import BecknerOnofri.EntropyScalarCertificate.Bessel0082
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0032
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0512b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨0,by decide⟩
def lo0512b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨1,by decide⟩
def lo0512 : CheckedMoment :=
  CheckedMoment.ofBessel lo0512b1 lo0512b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0512b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨5,by decide⟩
def hi0512b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨6,by decide⟩
def hi0512 : CheckedMoment :=
  CheckedMoment.ofBessel hi0512b1 hi0512b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0512 : meanBracketCheck (1589/10000) lo0512 hi0512=true := by decide +kernel
def bracket0512 : MeanBracket := meanBracketOfMoments (1589/10000) lo0512 hi0512 accepted0512
def lo0513b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨10,by decide⟩
def lo0513b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨11,by decide⟩
def lo0513 : CheckedMoment :=
  CheckedMoment.ofBessel lo0513b1 lo0513b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0513b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨15,by decide⟩
def hi0513b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨16,by decide⟩
def hi0513 : CheckedMoment :=
  CheckedMoment.ofBessel hi0513b1 hi0513b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0513 : meanBracketCheck (1591/10000) lo0513 hi0513=true := by decide +kernel
def bracket0513 : MeanBracket := meanBracketOfMoments (1591/10000) lo0513 hi0513 accepted0513
def lo0514b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨20,by decide⟩
def lo0514b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨21,by decide⟩
def lo0514 : CheckedMoment :=
  CheckedMoment.ofBessel lo0514b1 lo0514b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0514b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨25,by decide⟩
def hi0514b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨26,by decide⟩
def hi0514 : CheckedMoment :=
  CheckedMoment.ofBessel hi0514b1 hi0514b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0514 : meanBracketCheck (1593/10000) lo0514 hi0514=true := by decide +kernel
def bracket0514 : MeanBracket := meanBracketOfMoments (1593/10000) lo0514 hi0514 accepted0514
def lo0515b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨30,by decide⟩
def lo0515b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨31,by decide⟩
def lo0515 : CheckedMoment :=
  CheckedMoment.ofBessel lo0515b1 lo0515b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0515b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨35,by decide⟩
def hi0515b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨36,by decide⟩
def hi0515 : CheckedMoment :=
  CheckedMoment.ofBessel hi0515b1 hi0515b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0515 : meanBracketCheck (319/2000) lo0515 hi0515=true := by decide +kernel
def bracket0515 : MeanBracket := meanBracketOfMoments (319/2000) lo0515 hi0515 accepted0515
def lo0516b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨40,by decide⟩
def lo0516b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨41,by decide⟩
def lo0516 : CheckedMoment :=
  CheckedMoment.ofBessel lo0516b1 lo0516b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0516b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨45,by decide⟩
def hi0516b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨46,by decide⟩
def hi0516 : CheckedMoment :=
  CheckedMoment.ofBessel hi0516b1 hi0516b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0516 : meanBracketCheck (1597/10000) lo0516 hi0516=true := by decide +kernel
def bracket0516 : MeanBracket := meanBracketOfMoments (1597/10000) lo0516 hi0516 accepted0516
def lo0517b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨50,by decide⟩
def lo0517b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨51,by decide⟩
def lo0517 : CheckedMoment :=
  CheckedMoment.ofBessel lo0517b1 lo0517b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0517b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨55,by decide⟩
def hi0517b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨56,by decide⟩
def hi0517 : CheckedMoment :=
  CheckedMoment.ofBessel hi0517b1 hi0517b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0517 : meanBracketCheck (1599/10000) lo0517 hi0517=true := by decide +kernel
def bracket0517 : MeanBracket := meanBracketOfMoments (1599/10000) lo0517 hi0517 accepted0517
def lo0518b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨60,by decide⟩
def lo0518b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨61,by decide⟩
def lo0518 : CheckedMoment :=
  CheckedMoment.ofBessel lo0518b1 lo0518b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0518b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨1,by decide⟩
def hi0518b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨2,by decide⟩
def hi0518 : CheckedMoment :=
  CheckedMoment.ofBessel hi0518b1 hi0518b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0518 : meanBracketCheck (1601/10000) lo0518 hi0518=true := by decide +kernel
def bracket0518 : MeanBracket := meanBracketOfMoments (1601/10000) lo0518 hi0518 accepted0518
def lo0519b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨6,by decide⟩
def lo0519b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨7,by decide⟩
def lo0519 : CheckedMoment :=
  CheckedMoment.ofBessel lo0519b1 lo0519b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0519b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨11,by decide⟩
def hi0519b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨12,by decide⟩
def hi0519 : CheckedMoment :=
  CheckedMoment.ofBessel hi0519b1 hi0519b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0519 : meanBracketCheck (1603/10000) lo0519 hi0519=true := by decide +kernel
def bracket0519 : MeanBracket := meanBracketOfMoments (1603/10000) lo0519 hi0519 accepted0519
def lo0520b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨16,by decide⟩
def lo0520b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨17,by decide⟩
def lo0520 : CheckedMoment :=
  CheckedMoment.ofBessel lo0520b1 lo0520b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0520b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨21,by decide⟩
def hi0520b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨22,by decide⟩
def hi0520 : CheckedMoment :=
  CheckedMoment.ofBessel hi0520b1 hi0520b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0520 : meanBracketCheck (321/2000) lo0520 hi0520=true := by decide +kernel
def bracket0520 : MeanBracket := meanBracketOfMoments (321/2000) lo0520 hi0520 accepted0520
def lo0521b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨26,by decide⟩
def lo0521b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨27,by decide⟩
def lo0521 : CheckedMoment :=
  CheckedMoment.ofBessel lo0521b1 lo0521b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0521b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨31,by decide⟩
def hi0521b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨32,by decide⟩
def hi0521 : CheckedMoment :=
  CheckedMoment.ofBessel hi0521b1 hi0521b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0521 : meanBracketCheck (1607/10000) lo0521 hi0521=true := by decide +kernel
def bracket0521 : MeanBracket := meanBracketOfMoments (1607/10000) lo0521 hi0521 accepted0521
def lo0522b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨36,by decide⟩
def lo0522b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨37,by decide⟩
def lo0522 : CheckedMoment :=
  CheckedMoment.ofBessel lo0522b1 lo0522b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0522b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨41,by decide⟩
def hi0522b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨42,by decide⟩
def hi0522 : CheckedMoment :=
  CheckedMoment.ofBessel hi0522b1 hi0522b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0522 : meanBracketCheck (1609/10000) lo0522 hi0522=true := by decide +kernel
def bracket0522 : MeanBracket := meanBracketOfMoments (1609/10000) lo0522 hi0522 accepted0522
def lo0523b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨46,by decide⟩
def lo0523b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨47,by decide⟩
def lo0523 : CheckedMoment :=
  CheckedMoment.ofBessel lo0523b1 lo0523b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0523b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨51,by decide⟩
def hi0523b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨52,by decide⟩
def hi0523 : CheckedMoment :=
  CheckedMoment.ofBessel hi0523b1 hi0523b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0523 : meanBracketCheck (1611/10000) lo0523 hi0523=true := by decide +kernel
def bracket0523 : MeanBracket := meanBracketOfMoments (1611/10000) lo0523 hi0523 accepted0523
def lo0524b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨56,by decide⟩
def lo0524b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨57,by decide⟩
def lo0524 : CheckedMoment :=
  CheckedMoment.ofBessel lo0524b1 lo0524b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0524b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨61,by decide⟩
def hi0524b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0081.rows BesselBatch0081.accepted ⟨62,by decide⟩
def hi0524 : CheckedMoment :=
  CheckedMoment.ofBessel hi0524b1 hi0524b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0524 : meanBracketCheck (1613/10000) lo0524 hi0524=true := by decide +kernel
def bracket0524 : MeanBracket := meanBracketOfMoments (1613/10000) lo0524 hi0524 accepted0524
def lo0525b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨2,by decide⟩
def lo0525b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨3,by decide⟩
def lo0525 : CheckedMoment :=
  CheckedMoment.ofBessel lo0525b1 lo0525b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0525b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨7,by decide⟩
def hi0525b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨8,by decide⟩
def hi0525 : CheckedMoment :=
  CheckedMoment.ofBessel hi0525b1 hi0525b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0525 : meanBracketCheck (323/2000) lo0525 hi0525=true := by decide +kernel
def bracket0525 : MeanBracket := meanBracketOfMoments (323/2000) lo0525 hi0525 accepted0525
def lo0526b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨12,by decide⟩
def lo0526b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨13,by decide⟩
def lo0526 : CheckedMoment :=
  CheckedMoment.ofBessel lo0526b1 lo0526b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0526b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨17,by decide⟩
def hi0526b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨18,by decide⟩
def hi0526 : CheckedMoment :=
  CheckedMoment.ofBessel hi0526b1 hi0526b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0526 : meanBracketCheck (1617/10000) lo0526 hi0526=true := by decide +kernel
def bracket0526 : MeanBracket := meanBracketOfMoments (1617/10000) lo0526 hi0526 accepted0526
def lo0527b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨22,by decide⟩
def lo0527b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨23,by decide⟩
def lo0527 : CheckedMoment :=
  CheckedMoment.ofBessel lo0527b1 lo0527b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0527b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨27,by decide⟩
def hi0527b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0082.rows BesselBatch0082.accepted ⟨28,by decide⟩
def hi0527 : CheckedMoment :=
  CheckedMoment.ofBessel hi0527b1 hi0527b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0527 : meanBracketCheck (1619/10000) lo0527 hi0527=true := by decide +kernel
def bracket0527 : MeanBracket := meanBracketOfMoments (1619/10000) lo0527 hi0527 accepted0527
#print axioms bracket0512
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0032
