import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0062
import BecknerOnofri.EntropyScalarCertificate.Bessel0063
import BecknerOnofri.EntropyScalarCertificate.Bessel0064
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0025
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0400b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨32,by decide⟩
def lo0400b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨33,by decide⟩
def lo0400 : CheckedMoment :=
  CheckedMoment.ofBessel lo0400b1 lo0400b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0400b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨37,by decide⟩
def hi0400b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨38,by decide⟩
def hi0400 : CheckedMoment :=
  CheckedMoment.ofBessel hi0400b1 hi0400b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0400 : meanBracketCheck (273/2000) lo0400 hi0400=true := by decide +kernel
def bracket0400 : MeanBracket := meanBracketOfMoments (273/2000) lo0400 hi0400 accepted0400
def lo0401b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨42,by decide⟩
def lo0401b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨43,by decide⟩
def lo0401 : CheckedMoment :=
  CheckedMoment.ofBessel lo0401b1 lo0401b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0401b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨47,by decide⟩
def hi0401b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨48,by decide⟩
def hi0401 : CheckedMoment :=
  CheckedMoment.ofBessel hi0401b1 hi0401b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0401 : meanBracketCheck (1367/10000) lo0401 hi0401=true := by decide +kernel
def bracket0401 : MeanBracket := meanBracketOfMoments (1367/10000) lo0401 hi0401 accepted0401
def lo0402b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨52,by decide⟩
def lo0402b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨53,by decide⟩
def lo0402 : CheckedMoment :=
  CheckedMoment.ofBessel lo0402b1 lo0402b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0402b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨57,by decide⟩
def hi0402b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨58,by decide⟩
def hi0402 : CheckedMoment :=
  CheckedMoment.ofBessel hi0402b1 hi0402b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0402 : meanBracketCheck (1369/10000) lo0402 hi0402=true := by decide +kernel
def bracket0402 : MeanBracket := meanBracketOfMoments (1369/10000) lo0402 hi0402 accepted0402
def lo0403b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨62,by decide⟩
def lo0403b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨63,by decide⟩
def lo0403 : CheckedMoment :=
  CheckedMoment.ofBessel lo0403b1 lo0403b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0403b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨3,by decide⟩
def hi0403b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨4,by decide⟩
def hi0403 : CheckedMoment :=
  CheckedMoment.ofBessel hi0403b1 hi0403b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0403 : meanBracketCheck (1371/10000) lo0403 hi0403=true := by decide +kernel
def bracket0403 : MeanBracket := meanBracketOfMoments (1371/10000) lo0403 hi0403 accepted0403
def lo0404b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨8,by decide⟩
def lo0404b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨9,by decide⟩
def lo0404 : CheckedMoment :=
  CheckedMoment.ofBessel lo0404b1 lo0404b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0404b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨13,by decide⟩
def hi0404b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨14,by decide⟩
def hi0404 : CheckedMoment :=
  CheckedMoment.ofBessel hi0404b1 hi0404b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0404 : meanBracketCheck (1373/10000) lo0404 hi0404=true := by decide +kernel
def bracket0404 : MeanBracket := meanBracketOfMoments (1373/10000) lo0404 hi0404 accepted0404
def lo0405b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨18,by decide⟩
def lo0405b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨19,by decide⟩
def lo0405 : CheckedMoment :=
  CheckedMoment.ofBessel lo0405b1 lo0405b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0405b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨23,by decide⟩
def hi0405b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨24,by decide⟩
def hi0405 : CheckedMoment :=
  CheckedMoment.ofBessel hi0405b1 hi0405b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0405 : meanBracketCheck (11/80) lo0405 hi0405=true := by decide +kernel
def bracket0405 : MeanBracket := meanBracketOfMoments (11/80) lo0405 hi0405 accepted0405
def lo0406b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨28,by decide⟩
def lo0406b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨29,by decide⟩
def lo0406 : CheckedMoment :=
  CheckedMoment.ofBessel lo0406b1 lo0406b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0406b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨33,by decide⟩
def hi0406b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨34,by decide⟩
def hi0406 : CheckedMoment :=
  CheckedMoment.ofBessel hi0406b1 hi0406b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0406 : meanBracketCheck (1377/10000) lo0406 hi0406=true := by decide +kernel
def bracket0406 : MeanBracket := meanBracketOfMoments (1377/10000) lo0406 hi0406 accepted0406
def lo0407b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨38,by decide⟩
def lo0407b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨39,by decide⟩
def lo0407 : CheckedMoment :=
  CheckedMoment.ofBessel lo0407b1 lo0407b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0407b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨43,by decide⟩
def hi0407b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨44,by decide⟩
def hi0407 : CheckedMoment :=
  CheckedMoment.ofBessel hi0407b1 hi0407b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0407 : meanBracketCheck (1379/10000) lo0407 hi0407=true := by decide +kernel
def bracket0407 : MeanBracket := meanBracketOfMoments (1379/10000) lo0407 hi0407 accepted0407
def lo0408b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨48,by decide⟩
def lo0408b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨49,by decide⟩
def lo0408 : CheckedMoment :=
  CheckedMoment.ofBessel lo0408b1 lo0408b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0408b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨53,by decide⟩
def hi0408b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨54,by decide⟩
def hi0408 : CheckedMoment :=
  CheckedMoment.ofBessel hi0408b1 hi0408b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0408 : meanBracketCheck (1381/10000) lo0408 hi0408=true := by decide +kernel
def bracket0408 : MeanBracket := meanBracketOfMoments (1381/10000) lo0408 hi0408 accepted0408
def lo0409b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨58,by decide⟩
def lo0409b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨59,by decide⟩
def lo0409 : CheckedMoment :=
  CheckedMoment.ofBessel lo0409b1 lo0409b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0409b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨63,by decide⟩
def hi0409b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨0,by decide⟩
def hi0409 : CheckedMoment :=
  CheckedMoment.ofBessel hi0409b1 hi0409b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0409 : meanBracketCheck (1383/10000) lo0409 hi0409=true := by decide +kernel
def bracket0409 : MeanBracket := meanBracketOfMoments (1383/10000) lo0409 hi0409 accepted0409
def lo0410b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨4,by decide⟩
def lo0410b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨5,by decide⟩
def lo0410 : CheckedMoment :=
  CheckedMoment.ofBessel lo0410b1 lo0410b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0410b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨9,by decide⟩
def hi0410b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨10,by decide⟩
def hi0410 : CheckedMoment :=
  CheckedMoment.ofBessel hi0410b1 hi0410b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0410 : meanBracketCheck (277/2000) lo0410 hi0410=true := by decide +kernel
def bracket0410 : MeanBracket := meanBracketOfMoments (277/2000) lo0410 hi0410 accepted0410
def lo0411b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨14,by decide⟩
def lo0411b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨15,by decide⟩
def lo0411 : CheckedMoment :=
  CheckedMoment.ofBessel lo0411b1 lo0411b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0411b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨19,by decide⟩
def hi0411b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨20,by decide⟩
def hi0411 : CheckedMoment :=
  CheckedMoment.ofBessel hi0411b1 hi0411b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0411 : meanBracketCheck (1387/10000) lo0411 hi0411=true := by decide +kernel
def bracket0411 : MeanBracket := meanBracketOfMoments (1387/10000) lo0411 hi0411 accepted0411
def lo0412b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨24,by decide⟩
def lo0412b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨25,by decide⟩
def lo0412 : CheckedMoment :=
  CheckedMoment.ofBessel lo0412b1 lo0412b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0412b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨29,by decide⟩
def hi0412b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨30,by decide⟩
def hi0412 : CheckedMoment :=
  CheckedMoment.ofBessel hi0412b1 hi0412b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0412 : meanBracketCheck (1389/10000) lo0412 hi0412=true := by decide +kernel
def bracket0412 : MeanBracket := meanBracketOfMoments (1389/10000) lo0412 hi0412 accepted0412
def lo0413b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨34,by decide⟩
def lo0413b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨35,by decide⟩
def lo0413 : CheckedMoment :=
  CheckedMoment.ofBessel lo0413b1 lo0413b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0413b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨39,by decide⟩
def hi0413b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨40,by decide⟩
def hi0413 : CheckedMoment :=
  CheckedMoment.ofBessel hi0413b1 hi0413b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0413 : meanBracketCheck (1391/10000) lo0413 hi0413=true := by decide +kernel
def bracket0413 : MeanBracket := meanBracketOfMoments (1391/10000) lo0413 hi0413 accepted0413
def lo0414b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨44,by decide⟩
def lo0414b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨45,by decide⟩
def lo0414 : CheckedMoment :=
  CheckedMoment.ofBessel lo0414b1 lo0414b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0414b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨49,by decide⟩
def hi0414b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨50,by decide⟩
def hi0414 : CheckedMoment :=
  CheckedMoment.ofBessel hi0414b1 hi0414b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0414 : meanBracketCheck (1393/10000) lo0414 hi0414=true := by decide +kernel
def bracket0414 : MeanBracket := meanBracketOfMoments (1393/10000) lo0414 hi0414 accepted0414
def lo0415b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨54,by decide⟩
def lo0415b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨55,by decide⟩
def lo0415 : CheckedMoment :=
  CheckedMoment.ofBessel lo0415b1 lo0415b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0415b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨59,by decide⟩
def hi0415b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨60,by decide⟩
def hi0415 : CheckedMoment :=
  CheckedMoment.ofBessel hi0415b1 hi0415b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0415 : meanBracketCheck (279/2000) lo0415 hi0415=true := by decide +kernel
def bracket0415 : MeanBracket := meanBracketOfMoments (279/2000) lo0415 hi0415 accepted0415
#print axioms bracket0400
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0025
