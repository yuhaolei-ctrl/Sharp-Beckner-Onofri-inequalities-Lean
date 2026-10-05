import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0072
import BecknerOnofri.EntropyScalarCertificate.Bessel0073
import BecknerOnofri.EntropyScalarCertificate.Bessel0074
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0029
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0464b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨32,by decide⟩
def lo0464b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨33,by decide⟩
def lo0464 : CheckedMoment :=
  CheckedMoment.ofBessel lo0464b1 lo0464b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0464b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨37,by decide⟩
def hi0464b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨38,by decide⟩
def hi0464 : CheckedMoment :=
  CheckedMoment.ofBessel hi0464b1 hi0464b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0464 : meanBracketCheck (1493/10000) lo0464 hi0464=true := by decide +kernel
def bracket0464 : MeanBracket := meanBracketOfMoments (1493/10000) lo0464 hi0464 accepted0464
def lo0465b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨42,by decide⟩
def lo0465b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨43,by decide⟩
def lo0465 : CheckedMoment :=
  CheckedMoment.ofBessel lo0465b1 lo0465b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0465b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨47,by decide⟩
def hi0465b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨48,by decide⟩
def hi0465 : CheckedMoment :=
  CheckedMoment.ofBessel hi0465b1 hi0465b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0465 : meanBracketCheck (299/2000) lo0465 hi0465=true := by decide +kernel
def bracket0465 : MeanBracket := meanBracketOfMoments (299/2000) lo0465 hi0465 accepted0465
def lo0466b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨52,by decide⟩
def lo0466b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨53,by decide⟩
def lo0466 : CheckedMoment :=
  CheckedMoment.ofBessel lo0466b1 lo0466b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0466b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨57,by decide⟩
def hi0466b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨58,by decide⟩
def hi0466 : CheckedMoment :=
  CheckedMoment.ofBessel hi0466b1 hi0466b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0466 : meanBracketCheck (1497/10000) lo0466 hi0466=true := by decide +kernel
def bracket0466 : MeanBracket := meanBracketOfMoments (1497/10000) lo0466 hi0466 accepted0466
def lo0467b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨62,by decide⟩
def lo0467b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨63,by decide⟩
def lo0467 : CheckedMoment :=
  CheckedMoment.ofBessel lo0467b1 lo0467b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0467b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨3,by decide⟩
def hi0467b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨4,by decide⟩
def hi0467 : CheckedMoment :=
  CheckedMoment.ofBessel hi0467b1 hi0467b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0467 : meanBracketCheck (1499/10000) lo0467 hi0467=true := by decide +kernel
def bracket0467 : MeanBracket := meanBracketOfMoments (1499/10000) lo0467 hi0467 accepted0467
def lo0468b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨8,by decide⟩
def lo0468b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨9,by decide⟩
def lo0468 : CheckedMoment :=
  CheckedMoment.ofBessel lo0468b1 lo0468b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0468b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨13,by decide⟩
def hi0468b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨14,by decide⟩
def hi0468 : CheckedMoment :=
  CheckedMoment.ofBessel hi0468b1 hi0468b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0468 : meanBracketCheck (1501/10000) lo0468 hi0468=true := by decide +kernel
def bracket0468 : MeanBracket := meanBracketOfMoments (1501/10000) lo0468 hi0468 accepted0468
def lo0469b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨18,by decide⟩
def lo0469b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨19,by decide⟩
def lo0469 : CheckedMoment :=
  CheckedMoment.ofBessel lo0469b1 lo0469b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0469b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨23,by decide⟩
def hi0469b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨24,by decide⟩
def hi0469 : CheckedMoment :=
  CheckedMoment.ofBessel hi0469b1 hi0469b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0469 : meanBracketCheck (1503/10000) lo0469 hi0469=true := by decide +kernel
def bracket0469 : MeanBracket := meanBracketOfMoments (1503/10000) lo0469 hi0469 accepted0469
def lo0470b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨28,by decide⟩
def lo0470b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨29,by decide⟩
def lo0470 : CheckedMoment :=
  CheckedMoment.ofBessel lo0470b1 lo0470b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0470b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨33,by decide⟩
def hi0470b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨34,by decide⟩
def hi0470 : CheckedMoment :=
  CheckedMoment.ofBessel hi0470b1 hi0470b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0470 : meanBracketCheck (301/2000) lo0470 hi0470=true := by decide +kernel
def bracket0470 : MeanBracket := meanBracketOfMoments (301/2000) lo0470 hi0470 accepted0470
def lo0471b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨38,by decide⟩
def lo0471b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨39,by decide⟩
def lo0471 : CheckedMoment :=
  CheckedMoment.ofBessel lo0471b1 lo0471b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0471b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨43,by decide⟩
def hi0471b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨44,by decide⟩
def hi0471 : CheckedMoment :=
  CheckedMoment.ofBessel hi0471b1 hi0471b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0471 : meanBracketCheck (1507/10000) lo0471 hi0471=true := by decide +kernel
def bracket0471 : MeanBracket := meanBracketOfMoments (1507/10000) lo0471 hi0471 accepted0471
def lo0472b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨48,by decide⟩
def lo0472b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨49,by decide⟩
def lo0472 : CheckedMoment :=
  CheckedMoment.ofBessel lo0472b1 lo0472b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0472b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨53,by decide⟩
def hi0472b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨54,by decide⟩
def hi0472 : CheckedMoment :=
  CheckedMoment.ofBessel hi0472b1 hi0472b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0472 : meanBracketCheck (1509/10000) lo0472 hi0472=true := by decide +kernel
def bracket0472 : MeanBracket := meanBracketOfMoments (1509/10000) lo0472 hi0472 accepted0472
def lo0473b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨58,by decide⟩
def lo0473b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨59,by decide⟩
def lo0473 : CheckedMoment :=
  CheckedMoment.ofBessel lo0473b1 lo0473b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0473b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨63,by decide⟩
def hi0473b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨0,by decide⟩
def hi0473 : CheckedMoment :=
  CheckedMoment.ofBessel hi0473b1 hi0473b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0473 : meanBracketCheck (1511/10000) lo0473 hi0473=true := by decide +kernel
def bracket0473 : MeanBracket := meanBracketOfMoments (1511/10000) lo0473 hi0473 accepted0473
def lo0474b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨4,by decide⟩
def lo0474b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨5,by decide⟩
def lo0474 : CheckedMoment :=
  CheckedMoment.ofBessel lo0474b1 lo0474b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0474b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨9,by decide⟩
def hi0474b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨10,by decide⟩
def hi0474 : CheckedMoment :=
  CheckedMoment.ofBessel hi0474b1 hi0474b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0474 : meanBracketCheck (1513/10000) lo0474 hi0474=true := by decide +kernel
def bracket0474 : MeanBracket := meanBracketOfMoments (1513/10000) lo0474 hi0474 accepted0474
def lo0475b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨14,by decide⟩
def lo0475b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨15,by decide⟩
def lo0475 : CheckedMoment :=
  CheckedMoment.ofBessel lo0475b1 lo0475b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0475b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨19,by decide⟩
def hi0475b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨20,by decide⟩
def hi0475 : CheckedMoment :=
  CheckedMoment.ofBessel hi0475b1 hi0475b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0475 : meanBracketCheck (303/2000) lo0475 hi0475=true := by decide +kernel
def bracket0475 : MeanBracket := meanBracketOfMoments (303/2000) lo0475 hi0475 accepted0475
def lo0476b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨24,by decide⟩
def lo0476b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨25,by decide⟩
def lo0476 : CheckedMoment :=
  CheckedMoment.ofBessel lo0476b1 lo0476b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0476b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨29,by decide⟩
def hi0476b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨30,by decide⟩
def hi0476 : CheckedMoment :=
  CheckedMoment.ofBessel hi0476b1 hi0476b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0476 : meanBracketCheck (1517/10000) lo0476 hi0476=true := by decide +kernel
def bracket0476 : MeanBracket := meanBracketOfMoments (1517/10000) lo0476 hi0476 accepted0476
def lo0477b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨34,by decide⟩
def lo0477b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨35,by decide⟩
def lo0477 : CheckedMoment :=
  CheckedMoment.ofBessel lo0477b1 lo0477b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0477b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨39,by decide⟩
def hi0477b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨40,by decide⟩
def hi0477 : CheckedMoment :=
  CheckedMoment.ofBessel hi0477b1 hi0477b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0477 : meanBracketCheck (1519/10000) lo0477 hi0477=true := by decide +kernel
def bracket0477 : MeanBracket := meanBracketOfMoments (1519/10000) lo0477 hi0477 accepted0477
def lo0478b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨44,by decide⟩
def lo0478b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨45,by decide⟩
def lo0478 : CheckedMoment :=
  CheckedMoment.ofBessel lo0478b1 lo0478b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0478b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨49,by decide⟩
def hi0478b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨50,by decide⟩
def hi0478 : CheckedMoment :=
  CheckedMoment.ofBessel hi0478b1 hi0478b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0478 : meanBracketCheck (1521/10000) lo0478 hi0478=true := by decide +kernel
def bracket0478 : MeanBracket := meanBracketOfMoments (1521/10000) lo0478 hi0478 accepted0478
def lo0479b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨54,by decide⟩
def lo0479b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨55,by decide⟩
def lo0479 : CheckedMoment :=
  CheckedMoment.ofBessel lo0479b1 lo0479b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0479b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨59,by decide⟩
def hi0479b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨60,by decide⟩
def hi0479 : CheckedMoment :=
  CheckedMoment.ofBessel hi0479b1 hi0479b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0479 : meanBracketCheck (1523/10000) lo0479 hi0479=true := by decide +kernel
def bracket0479 : MeanBracket := meanBracketOfMoments (1523/10000) lo0479 hi0479 accepted0479
#print axioms bracket0464
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0029
