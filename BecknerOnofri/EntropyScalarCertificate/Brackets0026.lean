import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0065
import BecknerOnofri.EntropyScalarCertificate.Bessel0066
import BecknerOnofri.EntropyScalarCertificate.Bessel0067
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0026
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0416b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨0,by decide⟩
def lo0416b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨1,by decide⟩
def lo0416 : CheckedMoment :=
  CheckedMoment.ofBessel lo0416b1 lo0416b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0416b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨5,by decide⟩
def hi0416b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨6,by decide⟩
def hi0416 : CheckedMoment :=
  CheckedMoment.ofBessel hi0416b1 hi0416b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0416 : meanBracketCheck (1397/10000) lo0416 hi0416=true := by decide +kernel
def bracket0416 : MeanBracket := meanBracketOfMoments (1397/10000) lo0416 hi0416 accepted0416
def lo0417b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨10,by decide⟩
def lo0417b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨11,by decide⟩
def lo0417 : CheckedMoment :=
  CheckedMoment.ofBessel lo0417b1 lo0417b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0417b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨15,by decide⟩
def hi0417b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨16,by decide⟩
def hi0417 : CheckedMoment :=
  CheckedMoment.ofBessel hi0417b1 hi0417b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0417 : meanBracketCheck (1399/10000) lo0417 hi0417=true := by decide +kernel
def bracket0417 : MeanBracket := meanBracketOfMoments (1399/10000) lo0417 hi0417 accepted0417
def lo0418b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨20,by decide⟩
def lo0418b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨21,by decide⟩
def lo0418 : CheckedMoment :=
  CheckedMoment.ofBessel lo0418b1 lo0418b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0418b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨25,by decide⟩
def hi0418b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨26,by decide⟩
def hi0418 : CheckedMoment :=
  CheckedMoment.ofBessel hi0418b1 hi0418b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0418 : meanBracketCheck (1401/10000) lo0418 hi0418=true := by decide +kernel
def bracket0418 : MeanBracket := meanBracketOfMoments (1401/10000) lo0418 hi0418 accepted0418
def lo0419b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨30,by decide⟩
def lo0419b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨31,by decide⟩
def lo0419 : CheckedMoment :=
  CheckedMoment.ofBessel lo0419b1 lo0419b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0419b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨35,by decide⟩
def hi0419b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨36,by decide⟩
def hi0419 : CheckedMoment :=
  CheckedMoment.ofBessel hi0419b1 hi0419b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0419 : meanBracketCheck (1403/10000) lo0419 hi0419=true := by decide +kernel
def bracket0419 : MeanBracket := meanBracketOfMoments (1403/10000) lo0419 hi0419 accepted0419
def lo0420b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨40,by decide⟩
def lo0420b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨41,by decide⟩
def lo0420 : CheckedMoment :=
  CheckedMoment.ofBessel lo0420b1 lo0420b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0420b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨45,by decide⟩
def hi0420b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨46,by decide⟩
def hi0420 : CheckedMoment :=
  CheckedMoment.ofBessel hi0420b1 hi0420b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0420 : meanBracketCheck (281/2000) lo0420 hi0420=true := by decide +kernel
def bracket0420 : MeanBracket := meanBracketOfMoments (281/2000) lo0420 hi0420 accepted0420
def lo0421b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨50,by decide⟩
def lo0421b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨51,by decide⟩
def lo0421 : CheckedMoment :=
  CheckedMoment.ofBessel lo0421b1 lo0421b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0421b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨55,by decide⟩
def hi0421b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨56,by decide⟩
def hi0421 : CheckedMoment :=
  CheckedMoment.ofBessel hi0421b1 hi0421b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0421 : meanBracketCheck (1407/10000) lo0421 hi0421=true := by decide +kernel
def bracket0421 : MeanBracket := meanBracketOfMoments (1407/10000) lo0421 hi0421 accepted0421
def lo0422b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨60,by decide⟩
def lo0422b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨61,by decide⟩
def lo0422 : CheckedMoment :=
  CheckedMoment.ofBessel lo0422b1 lo0422b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0422b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨1,by decide⟩
def hi0422b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨2,by decide⟩
def hi0422 : CheckedMoment :=
  CheckedMoment.ofBessel hi0422b1 hi0422b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0422 : meanBracketCheck (1409/10000) lo0422 hi0422=true := by decide +kernel
def bracket0422 : MeanBracket := meanBracketOfMoments (1409/10000) lo0422 hi0422 accepted0422
def lo0423b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨6,by decide⟩
def lo0423b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨7,by decide⟩
def lo0423 : CheckedMoment :=
  CheckedMoment.ofBessel lo0423b1 lo0423b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0423b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨11,by decide⟩
def hi0423b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨12,by decide⟩
def hi0423 : CheckedMoment :=
  CheckedMoment.ofBessel hi0423b1 hi0423b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0423 : meanBracketCheck (1411/10000) lo0423 hi0423=true := by decide +kernel
def bracket0423 : MeanBracket := meanBracketOfMoments (1411/10000) lo0423 hi0423 accepted0423
def lo0424b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨16,by decide⟩
def lo0424b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨17,by decide⟩
def lo0424 : CheckedMoment :=
  CheckedMoment.ofBessel lo0424b1 lo0424b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0424b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨21,by decide⟩
def hi0424b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨22,by decide⟩
def hi0424 : CheckedMoment :=
  CheckedMoment.ofBessel hi0424b1 hi0424b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0424 : meanBracketCheck (1413/10000) lo0424 hi0424=true := by decide +kernel
def bracket0424 : MeanBracket := meanBracketOfMoments (1413/10000) lo0424 hi0424 accepted0424
def lo0425b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨26,by decide⟩
def lo0425b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨27,by decide⟩
def lo0425 : CheckedMoment :=
  CheckedMoment.ofBessel lo0425b1 lo0425b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0425b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨31,by decide⟩
def hi0425b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨32,by decide⟩
def hi0425 : CheckedMoment :=
  CheckedMoment.ofBessel hi0425b1 hi0425b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0425 : meanBracketCheck (283/2000) lo0425 hi0425=true := by decide +kernel
def bracket0425 : MeanBracket := meanBracketOfMoments (283/2000) lo0425 hi0425 accepted0425
def lo0426b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨36,by decide⟩
def lo0426b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨37,by decide⟩
def lo0426 : CheckedMoment :=
  CheckedMoment.ofBessel lo0426b1 lo0426b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0426b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨41,by decide⟩
def hi0426b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨42,by decide⟩
def hi0426 : CheckedMoment :=
  CheckedMoment.ofBessel hi0426b1 hi0426b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0426 : meanBracketCheck (1417/10000) lo0426 hi0426=true := by decide +kernel
def bracket0426 : MeanBracket := meanBracketOfMoments (1417/10000) lo0426 hi0426 accepted0426
def lo0427b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨46,by decide⟩
def lo0427b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨47,by decide⟩
def lo0427 : CheckedMoment :=
  CheckedMoment.ofBessel lo0427b1 lo0427b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0427b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨51,by decide⟩
def hi0427b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨52,by decide⟩
def hi0427 : CheckedMoment :=
  CheckedMoment.ofBessel hi0427b1 hi0427b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0427 : meanBracketCheck (1419/10000) lo0427 hi0427=true := by decide +kernel
def bracket0427 : MeanBracket := meanBracketOfMoments (1419/10000) lo0427 hi0427 accepted0427
def lo0428b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨56,by decide⟩
def lo0428b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨57,by decide⟩
def lo0428 : CheckedMoment :=
  CheckedMoment.ofBessel lo0428b1 lo0428b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0428b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨61,by decide⟩
def hi0428b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨62,by decide⟩
def hi0428 : CheckedMoment :=
  CheckedMoment.ofBessel hi0428b1 hi0428b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0428 : meanBracketCheck (1421/10000) lo0428 hi0428=true := by decide +kernel
def bracket0428 : MeanBracket := meanBracketOfMoments (1421/10000) lo0428 hi0428 accepted0428
def lo0429b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨2,by decide⟩
def lo0429b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨3,by decide⟩
def lo0429 : CheckedMoment :=
  CheckedMoment.ofBessel lo0429b1 lo0429b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0429b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨7,by decide⟩
def hi0429b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨8,by decide⟩
def hi0429 : CheckedMoment :=
  CheckedMoment.ofBessel hi0429b1 hi0429b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0429 : meanBracketCheck (1423/10000) lo0429 hi0429=true := by decide +kernel
def bracket0429 : MeanBracket := meanBracketOfMoments (1423/10000) lo0429 hi0429 accepted0429
def lo0430b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨12,by decide⟩
def lo0430b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨13,by decide⟩
def lo0430 : CheckedMoment :=
  CheckedMoment.ofBessel lo0430b1 lo0430b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0430b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨17,by decide⟩
def hi0430b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨18,by decide⟩
def hi0430 : CheckedMoment :=
  CheckedMoment.ofBessel hi0430b1 hi0430b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0430 : meanBracketCheck (57/400) lo0430 hi0430=true := by decide +kernel
def bracket0430 : MeanBracket := meanBracketOfMoments (57/400) lo0430 hi0430 accepted0430
def lo0431b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨22,by decide⟩
def lo0431b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨23,by decide⟩
def lo0431 : CheckedMoment :=
  CheckedMoment.ofBessel lo0431b1 lo0431b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0431b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨27,by decide⟩
def hi0431b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨28,by decide⟩
def hi0431 : CheckedMoment :=
  CheckedMoment.ofBessel hi0431b1 hi0431b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0431 : meanBracketCheck (1427/10000) lo0431 hi0431=true := by decide +kernel
def bracket0431 : MeanBracket := meanBracketOfMoments (1427/10000) lo0431 hi0431 accepted0431
#print axioms bracket0416
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0026
