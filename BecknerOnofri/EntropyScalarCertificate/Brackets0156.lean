module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0390
public import BecknerOnofri.EntropyScalarCertificate.Bessel0391
public import BecknerOnofri.EntropyScalarCertificate.Bessel0392

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0156
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2496b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨0,by decide⟩
def lo2496b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨1,by decide⟩
def lo2496 : CheckedMoment :=
  CheckedMoment.ofBessel lo2496b1 lo2496b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2496b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨5,by decide⟩
def hi2496b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨6,by decide⟩
def hi2496 : CheckedMoment :=
  CheckedMoment.ofBessel hi2496b1 hi2496b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2496 : meanBracketCheck (24809/25000) lo2496 hi2496=true := by decide +kernel
def bracket2496 : MeanBracket := meanBracketOfMoments (24809/25000) lo2496 hi2496 accepted2496
def lo2497b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨10,by decide⟩
def lo2497b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨11,by decide⟩
def lo2497 : CheckedMoment :=
  CheckedMoment.ofBessel lo2497b1 lo2497b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2497b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨15,by decide⟩
def hi2497b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨16,by decide⟩
def hi2497 : CheckedMoment :=
  CheckedMoment.ofBessel hi2497b1 hi2497b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2497 : meanBracketCheck (49619/50000) lo2497 hi2497=true := by decide +kernel
def bracket2497 : MeanBracket := meanBracketOfMoments (49619/50000) lo2497 hi2497 accepted2497
def lo2498b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨20,by decide⟩
def lo2498b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨21,by decide⟩
def lo2498 : CheckedMoment :=
  CheckedMoment.ofBessel lo2498b1 lo2498b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2498b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨25,by decide⟩
def hi2498b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨26,by decide⟩
def hi2498 : CheckedMoment :=
  CheckedMoment.ofBessel hi2498b1 hi2498b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2498 : meanBracketCheck (2481/2500) lo2498 hi2498=true := by decide +kernel
def bracket2498 : MeanBracket := meanBracketOfMoments (2481/2500) lo2498 hi2498 accepted2498
def lo2499b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨30,by decide⟩
def lo2499b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨31,by decide⟩
def lo2499 : CheckedMoment :=
  CheckedMoment.ofBessel lo2499b1 lo2499b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2499b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨35,by decide⟩
def hi2499b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨36,by decide⟩
def hi2499 : CheckedMoment :=
  CheckedMoment.ofBessel hi2499b1 hi2499b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2499 : meanBracketCheck (49621/50000) lo2499 hi2499=true := by decide +kernel
def bracket2499 : MeanBracket := meanBracketOfMoments (49621/50000) lo2499 hi2499 accepted2499
def lo2500b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨40,by decide⟩
def lo2500b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨41,by decide⟩
def lo2500 : CheckedMoment :=
  CheckedMoment.ofBessel lo2500b1 lo2500b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2500b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨45,by decide⟩
def hi2500b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨46,by decide⟩
def hi2500 : CheckedMoment :=
  CheckedMoment.ofBessel hi2500b1 hi2500b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2500 : meanBracketCheck (24811/25000) lo2500 hi2500=true := by decide +kernel
def bracket2500 : MeanBracket := meanBracketOfMoments (24811/25000) lo2500 hi2500 accepted2500
def lo2501b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨50,by decide⟩
def lo2501b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨51,by decide⟩
def lo2501 : CheckedMoment :=
  CheckedMoment.ofBessel lo2501b1 lo2501b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2501b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨55,by decide⟩
def hi2501b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨56,by decide⟩
def hi2501 : CheckedMoment :=
  CheckedMoment.ofBessel hi2501b1 hi2501b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2501 : meanBracketCheck (49623/50000) lo2501 hi2501=true := by decide +kernel
def bracket2501 : MeanBracket := meanBracketOfMoments (49623/50000) lo2501 hi2501 accepted2501
def lo2502b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨60,by decide⟩
def lo2502b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨61,by decide⟩
def lo2502 : CheckedMoment :=
  CheckedMoment.ofBessel lo2502b1 lo2502b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2502b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨1,by decide⟩
def hi2502b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨2,by decide⟩
def hi2502 : CheckedMoment :=
  CheckedMoment.ofBessel hi2502b1 hi2502b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2502 : meanBracketCheck (6203/6250) lo2502 hi2502=true := by decide +kernel
def bracket2502 : MeanBracket := meanBracketOfMoments (6203/6250) lo2502 hi2502 accepted2502
def lo2503b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨6,by decide⟩
def lo2503b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨7,by decide⟩
def lo2503 : CheckedMoment :=
  CheckedMoment.ofBessel lo2503b1 lo2503b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2503b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨11,by decide⟩
def hi2503b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨12,by decide⟩
def hi2503 : CheckedMoment :=
  CheckedMoment.ofBessel hi2503b1 hi2503b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2503 : meanBracketCheck (397/400) lo2503 hi2503=true := by decide +kernel
def bracket2503 : MeanBracket := meanBracketOfMoments (397/400) lo2503 hi2503 accepted2503
def lo2504b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨16,by decide⟩
def lo2504b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨17,by decide⟩
def lo2504 : CheckedMoment :=
  CheckedMoment.ofBessel lo2504b1 lo2504b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2504b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨21,by decide⟩
def hi2504b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨22,by decide⟩
def hi2504 : CheckedMoment :=
  CheckedMoment.ofBessel hi2504b1 hi2504b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2504 : meanBracketCheck (24813/25000) lo2504 hi2504=true := by decide +kernel
def bracket2504 : MeanBracket := meanBracketOfMoments (24813/25000) lo2504 hi2504 accepted2504
def lo2505b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨26,by decide⟩
def lo2505b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨27,by decide⟩
def lo2505 : CheckedMoment :=
  CheckedMoment.ofBessel lo2505b1 lo2505b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2505b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨31,by decide⟩
def hi2505b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨32,by decide⟩
def hi2505 : CheckedMoment :=
  CheckedMoment.ofBessel hi2505b1 hi2505b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2505 : meanBracketCheck (49627/50000) lo2505 hi2505=true := by decide +kernel
def bracket2505 : MeanBracket := meanBracketOfMoments (49627/50000) lo2505 hi2505 accepted2505
def lo2506b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨36,by decide⟩
def lo2506b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨37,by decide⟩
def lo2506 : CheckedMoment :=
  CheckedMoment.ofBessel lo2506b1 lo2506b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2506b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨41,by decide⟩
def hi2506b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨42,by decide⟩
def hi2506 : CheckedMoment :=
  CheckedMoment.ofBessel hi2506b1 hi2506b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2506 : meanBracketCheck (12407/12500) lo2506 hi2506=true := by decide +kernel
def bracket2506 : MeanBracket := meanBracketOfMoments (12407/12500) lo2506 hi2506 accepted2506
def lo2507b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨46,by decide⟩
def lo2507b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨47,by decide⟩
def lo2507 : CheckedMoment :=
  CheckedMoment.ofBessel lo2507b1 lo2507b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2507b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨51,by decide⟩
def hi2507b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨52,by decide⟩
def hi2507 : CheckedMoment :=
  CheckedMoment.ofBessel hi2507b1 hi2507b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2507 : meanBracketCheck (49629/50000) lo2507 hi2507=true := by decide +kernel
def bracket2507 : MeanBracket := meanBracketOfMoments (49629/50000) lo2507 hi2507 accepted2507
def lo2508b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨56,by decide⟩
def lo2508b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨57,by decide⟩
def lo2508 : CheckedMoment :=
  CheckedMoment.ofBessel lo2508b1 lo2508b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2508b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨61,by decide⟩
def hi2508b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨62,by decide⟩
def hi2508 : CheckedMoment :=
  CheckedMoment.ofBessel hi2508b1 hi2508b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2508 : meanBracketCheck (4963/5000) lo2508 hi2508=true := by decide +kernel
def bracket2508 : MeanBracket := meanBracketOfMoments (4963/5000) lo2508 hi2508 accepted2508
def lo2509b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨2,by decide⟩
def lo2509b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨3,by decide⟩
def lo2509 : CheckedMoment :=
  CheckedMoment.ofBessel lo2509b1 lo2509b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2509b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨7,by decide⟩
def hi2509b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨8,by decide⟩
def hi2509 : CheckedMoment :=
  CheckedMoment.ofBessel hi2509b1 hi2509b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2509 : meanBracketCheck (49631/50000) lo2509 hi2509=true := by decide +kernel
def bracket2509 : MeanBracket := meanBracketOfMoments (49631/50000) lo2509 hi2509 accepted2509
def lo2510b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨12,by decide⟩
def lo2510b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨13,by decide⟩
def lo2510 : CheckedMoment :=
  CheckedMoment.ofBessel lo2510b1 lo2510b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2510b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨17,by decide⟩
def hi2510b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨18,by decide⟩
def hi2510 : CheckedMoment :=
  CheckedMoment.ofBessel hi2510b1 hi2510b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2510 : meanBracketCheck (3102/3125) lo2510 hi2510=true := by decide +kernel
def bracket2510 : MeanBracket := meanBracketOfMoments (3102/3125) lo2510 hi2510 accepted2510
def lo2511b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨22,by decide⟩
def lo2511b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨23,by decide⟩
def lo2511 : CheckedMoment :=
  CheckedMoment.ofBessel lo2511b1 lo2511b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2511b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨27,by decide⟩
def hi2511b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨28,by decide⟩
def hi2511 : CheckedMoment :=
  CheckedMoment.ofBessel hi2511b1 hi2511b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2511 : meanBracketCheck (49633/50000) lo2511 hi2511=true := by decide +kernel
def bracket2511 : MeanBracket := meanBracketOfMoments (49633/50000) lo2511 hi2511 accepted2511
#print axioms bracket2496
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0156
