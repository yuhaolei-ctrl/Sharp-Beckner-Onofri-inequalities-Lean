import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0375
import BecknerOnofri.EntropyScalarCertificate.Bessel0376
import BecknerOnofri.EntropyScalarCertificate.Bessel0377
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0150
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2400b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨0,by decide⟩
def lo2400b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨1,by decide⟩
def lo2400 : CheckedMoment :=
  CheckedMoment.ofBessel lo2400b1 lo2400b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2400b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨5,by decide⟩
def hi2400b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨6,by decide⟩
def hi2400 : CheckedMoment :=
  CheckedMoment.ofBessel hi2400b1 hi2400b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2400 : meanBracketCheck (24761/25000) lo2400 hi2400=true := by decide +kernel
def bracket2400 : MeanBracket := meanBracketOfMoments (24761/25000) lo2400 hi2400 accepted2400
def lo2401b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨10,by decide⟩
def lo2401b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨11,by decide⟩
def lo2401 : CheckedMoment :=
  CheckedMoment.ofBessel lo2401b1 lo2401b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2401b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨15,by decide⟩
def hi2401b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨16,by decide⟩
def hi2401 : CheckedMoment :=
  CheckedMoment.ofBessel hi2401b1 hi2401b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2401 : meanBracketCheck (49523/50000) lo2401 hi2401=true := by decide +kernel
def bracket2401 : MeanBracket := meanBracketOfMoments (49523/50000) lo2401 hi2401 accepted2401
def lo2402b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨20,by decide⟩
def lo2402b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨21,by decide⟩
def lo2402 : CheckedMoment :=
  CheckedMoment.ofBessel lo2402b1 lo2402b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2402b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨25,by decide⟩
def hi2402b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨26,by decide⟩
def hi2402 : CheckedMoment :=
  CheckedMoment.ofBessel hi2402b1 hi2402b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2402 : meanBracketCheck (12381/12500) lo2402 hi2402=true := by decide +kernel
def bracket2402 : MeanBracket := meanBracketOfMoments (12381/12500) lo2402 hi2402 accepted2402
def lo2403b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨30,by decide⟩
def lo2403b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨31,by decide⟩
def lo2403 : CheckedMoment :=
  CheckedMoment.ofBessel lo2403b1 lo2403b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2403b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨35,by decide⟩
def hi2403b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨36,by decide⟩
def hi2403 : CheckedMoment :=
  CheckedMoment.ofBessel hi2403b1 hi2403b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2403 : meanBracketCheck (1981/2000) lo2403 hi2403=true := by decide +kernel
def bracket2403 : MeanBracket := meanBracketOfMoments (1981/2000) lo2403 hi2403 accepted2403
def lo2404b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨40,by decide⟩
def lo2404b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨41,by decide⟩
def lo2404 : CheckedMoment :=
  CheckedMoment.ofBessel lo2404b1 lo2404b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2404b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨45,by decide⟩
def hi2404b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨46,by decide⟩
def hi2404 : CheckedMoment :=
  CheckedMoment.ofBessel hi2404b1 hi2404b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2404 : meanBracketCheck (24763/25000) lo2404 hi2404=true := by decide +kernel
def bracket2404 : MeanBracket := meanBracketOfMoments (24763/25000) lo2404 hi2404 accepted2404
def lo2405b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨50,by decide⟩
def lo2405b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨51,by decide⟩
def lo2405 : CheckedMoment :=
  CheckedMoment.ofBessel lo2405b1 lo2405b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2405b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨55,by decide⟩
def hi2405b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨56,by decide⟩
def hi2405 : CheckedMoment :=
  CheckedMoment.ofBessel hi2405b1 hi2405b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2405 : meanBracketCheck (49527/50000) lo2405 hi2405=true := by decide +kernel
def bracket2405 : MeanBracket := meanBracketOfMoments (49527/50000) lo2405 hi2405 accepted2405
def lo2406b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨60,by decide⟩
def lo2406b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨61,by decide⟩
def lo2406 : CheckedMoment :=
  CheckedMoment.ofBessel lo2406b1 lo2406b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2406b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨1,by decide⟩
def hi2406b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨2,by decide⟩
def hi2406 : CheckedMoment :=
  CheckedMoment.ofBessel hi2406b1 hi2406b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2406 : meanBracketCheck (6191/6250) lo2406 hi2406=true := by decide +kernel
def bracket2406 : MeanBracket := meanBracketOfMoments (6191/6250) lo2406 hi2406 accepted2406
def lo2407b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨6,by decide⟩
def lo2407b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨7,by decide⟩
def lo2407 : CheckedMoment :=
  CheckedMoment.ofBessel lo2407b1 lo2407b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2407b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨11,by decide⟩
def hi2407b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨12,by decide⟩
def hi2407 : CheckedMoment :=
  CheckedMoment.ofBessel hi2407b1 hi2407b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2407 : meanBracketCheck (49529/50000) lo2407 hi2407=true := by decide +kernel
def bracket2407 : MeanBracket := meanBracketOfMoments (49529/50000) lo2407 hi2407 accepted2407
def lo2408b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨16,by decide⟩
def lo2408b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨17,by decide⟩
def lo2408 : CheckedMoment :=
  CheckedMoment.ofBessel lo2408b1 lo2408b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2408b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨21,by decide⟩
def hi2408b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨22,by decide⟩
def hi2408 : CheckedMoment :=
  CheckedMoment.ofBessel hi2408b1 hi2408b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2408 : meanBracketCheck (4953/5000) lo2408 hi2408=true := by decide +kernel
def bracket2408 : MeanBracket := meanBracketOfMoments (4953/5000) lo2408 hi2408 accepted2408
def lo2409b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨26,by decide⟩
def lo2409b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨27,by decide⟩
def lo2409 : CheckedMoment :=
  CheckedMoment.ofBessel lo2409b1 lo2409b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2409b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨31,by decide⟩
def hi2409b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨32,by decide⟩
def hi2409 : CheckedMoment :=
  CheckedMoment.ofBessel hi2409b1 hi2409b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2409 : meanBracketCheck (49531/50000) lo2409 hi2409=true := by decide +kernel
def bracket2409 : MeanBracket := meanBracketOfMoments (49531/50000) lo2409 hi2409 accepted2409
def lo2410b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨36,by decide⟩
def lo2410b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨37,by decide⟩
def lo2410 : CheckedMoment :=
  CheckedMoment.ofBessel lo2410b1 lo2410b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2410b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨41,by decide⟩
def hi2410b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨42,by decide⟩
def hi2410 : CheckedMoment :=
  CheckedMoment.ofBessel hi2410b1 hi2410b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2410 : meanBracketCheck (12383/12500) lo2410 hi2410=true := by decide +kernel
def bracket2410 : MeanBracket := meanBracketOfMoments (12383/12500) lo2410 hi2410 accepted2410
def lo2411b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨46,by decide⟩
def lo2411b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨47,by decide⟩
def lo2411 : CheckedMoment :=
  CheckedMoment.ofBessel lo2411b1 lo2411b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2411b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨51,by decide⟩
def hi2411b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨52,by decide⟩
def hi2411 : CheckedMoment :=
  CheckedMoment.ofBessel hi2411b1 hi2411b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2411 : meanBracketCheck (49533/50000) lo2411 hi2411=true := by decide +kernel
def bracket2411 : MeanBracket := meanBracketOfMoments (49533/50000) lo2411 hi2411 accepted2411
def lo2412b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨56,by decide⟩
def lo2412b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨57,by decide⟩
def lo2412 : CheckedMoment :=
  CheckedMoment.ofBessel lo2412b1 lo2412b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2412b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨61,by decide⟩
def hi2412b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨62,by decide⟩
def hi2412 : CheckedMoment :=
  CheckedMoment.ofBessel hi2412b1 hi2412b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2412 : meanBracketCheck (24767/25000) lo2412 hi2412=true := by decide +kernel
def bracket2412 : MeanBracket := meanBracketOfMoments (24767/25000) lo2412 hi2412 accepted2412
def lo2413b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨2,by decide⟩
def lo2413b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨3,by decide⟩
def lo2413 : CheckedMoment :=
  CheckedMoment.ofBessel lo2413b1 lo2413b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2413b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨7,by decide⟩
def hi2413b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨8,by decide⟩
def hi2413 : CheckedMoment :=
  CheckedMoment.ofBessel hi2413b1 hi2413b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2413 : meanBracketCheck (9907/10000) lo2413 hi2413=true := by decide +kernel
def bracket2413 : MeanBracket := meanBracketOfMoments (9907/10000) lo2413 hi2413 accepted2413
def lo2414b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨12,by decide⟩
def lo2414b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨13,by decide⟩
def lo2414 : CheckedMoment :=
  CheckedMoment.ofBessel lo2414b1 lo2414b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2414b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨17,by decide⟩
def hi2414b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨18,by decide⟩
def hi2414 : CheckedMoment :=
  CheckedMoment.ofBessel hi2414b1 hi2414b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2414 : meanBracketCheck (3096/3125) lo2414 hi2414=true := by decide +kernel
def bracket2414 : MeanBracket := meanBracketOfMoments (3096/3125) lo2414 hi2414 accepted2414
def lo2415b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨22,by decide⟩
def lo2415b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨23,by decide⟩
def lo2415 : CheckedMoment :=
  CheckedMoment.ofBessel lo2415b1 lo2415b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2415b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨27,by decide⟩
def hi2415b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨28,by decide⟩
def hi2415 : CheckedMoment :=
  CheckedMoment.ofBessel hi2415b1 hi2415b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2415 : meanBracketCheck (49537/50000) lo2415 hi2415=true := by decide +kernel
def bracket2415 : MeanBracket := meanBracketOfMoments (49537/50000) lo2415 hi2415 accepted2415
#print axioms bracket2400
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0150
