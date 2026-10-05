module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0382
public import BecknerOnofri.EntropyScalarCertificate.Bessel0383
public import BecknerOnofri.EntropyScalarCertificate.Bessel0384

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0153
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2448b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨32,by decide⟩
def lo2448b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨33,by decide⟩
def lo2448 : CheckedMoment :=
  CheckedMoment.ofBessel lo2448b1 lo2448b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2448b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨37,by decide⟩
def hi2448b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨38,by decide⟩
def hi2448 : CheckedMoment :=
  CheckedMoment.ofBessel hi2448b1 hi2448b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2448 : meanBracketCheck (4957/5000) lo2448 hi2448=true := by decide +kernel
def bracket2448 : MeanBracket := meanBracketOfMoments (4957/5000) lo2448 hi2448 accepted2448
def lo2449b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨42,by decide⟩
def lo2449b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨43,by decide⟩
def lo2449 : CheckedMoment :=
  CheckedMoment.ofBessel lo2449b1 lo2449b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2449b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨47,by decide⟩
def hi2449b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨48,by decide⟩
def hi2449 : CheckedMoment :=
  CheckedMoment.ofBessel hi2449b1 hi2449b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2449 : meanBracketCheck (49571/50000) lo2449 hi2449=true := by decide +kernel
def bracket2449 : MeanBracket := meanBracketOfMoments (49571/50000) lo2449 hi2449 accepted2449
def lo2450b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨52,by decide⟩
def lo2450b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨53,by decide⟩
def lo2450 : CheckedMoment :=
  CheckedMoment.ofBessel lo2450b1 lo2450b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2450b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨57,by decide⟩
def hi2450b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨58,by decide⟩
def hi2450 : CheckedMoment :=
  CheckedMoment.ofBessel hi2450b1 hi2450b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2450 : meanBracketCheck (12393/12500) lo2450 hi2450=true := by decide +kernel
def bracket2450 : MeanBracket := meanBracketOfMoments (12393/12500) lo2450 hi2450 accepted2450
def lo2451b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨62,by decide⟩
def lo2451b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨63,by decide⟩
def lo2451 : CheckedMoment :=
  CheckedMoment.ofBessel lo2451b1 lo2451b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2451b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨3,by decide⟩
def hi2451b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨4,by decide⟩
def hi2451 : CheckedMoment :=
  CheckedMoment.ofBessel hi2451b1 hi2451b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2451 : meanBracketCheck (49573/50000) lo2451 hi2451=true := by decide +kernel
def bracket2451 : MeanBracket := meanBracketOfMoments (49573/50000) lo2451 hi2451 accepted2451
def lo2452b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨8,by decide⟩
def lo2452b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨9,by decide⟩
def lo2452 : CheckedMoment :=
  CheckedMoment.ofBessel lo2452b1 lo2452b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2452b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨13,by decide⟩
def hi2452b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨14,by decide⟩
def hi2452 : CheckedMoment :=
  CheckedMoment.ofBessel hi2452b1 hi2452b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2452 : meanBracketCheck (24787/25000) lo2452 hi2452=true := by decide +kernel
def bracket2452 : MeanBracket := meanBracketOfMoments (24787/25000) lo2452 hi2452 accepted2452
def lo2453b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨18,by decide⟩
def lo2453b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨19,by decide⟩
def lo2453 : CheckedMoment :=
  CheckedMoment.ofBessel lo2453b1 lo2453b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2453b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨23,by decide⟩
def hi2453b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨24,by decide⟩
def hi2453 : CheckedMoment :=
  CheckedMoment.ofBessel hi2453b1 hi2453b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2453 : meanBracketCheck (1983/2000) lo2453 hi2453=true := by decide +kernel
def bracket2453 : MeanBracket := meanBracketOfMoments (1983/2000) lo2453 hi2453 accepted2453
def lo2454b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨28,by decide⟩
def lo2454b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨29,by decide⟩
def lo2454 : CheckedMoment :=
  CheckedMoment.ofBessel lo2454b1 lo2454b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2454b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨33,by decide⟩
def hi2454b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨34,by decide⟩
def hi2454 : CheckedMoment :=
  CheckedMoment.ofBessel hi2454b1 hi2454b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2454 : meanBracketCheck (6197/6250) lo2454 hi2454=true := by decide +kernel
def bracket2454 : MeanBracket := meanBracketOfMoments (6197/6250) lo2454 hi2454 accepted2454
def lo2455b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨38,by decide⟩
def lo2455b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨39,by decide⟩
def lo2455 : CheckedMoment :=
  CheckedMoment.ofBessel lo2455b1 lo2455b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2455b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨43,by decide⟩
def hi2455b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨44,by decide⟩
def hi2455 : CheckedMoment :=
  CheckedMoment.ofBessel hi2455b1 hi2455b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2455 : meanBracketCheck (49577/50000) lo2455 hi2455=true := by decide +kernel
def bracket2455 : MeanBracket := meanBracketOfMoments (49577/50000) lo2455 hi2455 accepted2455
def lo2456b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨48,by decide⟩
def lo2456b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨49,by decide⟩
def lo2456 : CheckedMoment :=
  CheckedMoment.ofBessel lo2456b1 lo2456b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2456b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨53,by decide⟩
def hi2456b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨54,by decide⟩
def hi2456 : CheckedMoment :=
  CheckedMoment.ofBessel hi2456b1 hi2456b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2456 : meanBracketCheck (24789/25000) lo2456 hi2456=true := by decide +kernel
def bracket2456 : MeanBracket := meanBracketOfMoments (24789/25000) lo2456 hi2456 accepted2456
def lo2457b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨58,by decide⟩
def lo2457b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨59,by decide⟩
def lo2457 : CheckedMoment :=
  CheckedMoment.ofBessel lo2457b1 lo2457b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2457b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨63,by decide⟩
def hi2457b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨0,by decide⟩
def hi2457 : CheckedMoment :=
  CheckedMoment.ofBessel hi2457b1 hi2457b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2457 : meanBracketCheck (49579/50000) lo2457 hi2457=true := by decide +kernel
def bracket2457 : MeanBracket := meanBracketOfMoments (49579/50000) lo2457 hi2457 accepted2457
def lo2458b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨4,by decide⟩
def lo2458b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨5,by decide⟩
def lo2458 : CheckedMoment :=
  CheckedMoment.ofBessel lo2458b1 lo2458b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2458b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨9,by decide⟩
def hi2458b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨10,by decide⟩
def hi2458 : CheckedMoment :=
  CheckedMoment.ofBessel hi2458b1 hi2458b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2458 : meanBracketCheck (2479/2500) lo2458 hi2458=true := by decide +kernel
def bracket2458 : MeanBracket := meanBracketOfMoments (2479/2500) lo2458 hi2458 accepted2458
def lo2459b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨14,by decide⟩
def lo2459b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨15,by decide⟩
def lo2459 : CheckedMoment :=
  CheckedMoment.ofBessel lo2459b1 lo2459b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2459b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨19,by decide⟩
def hi2459b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨20,by decide⟩
def hi2459 : CheckedMoment :=
  CheckedMoment.ofBessel hi2459b1 hi2459b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2459 : meanBracketCheck (49581/50000) lo2459 hi2459=true := by decide +kernel
def bracket2459 : MeanBracket := meanBracketOfMoments (49581/50000) lo2459 hi2459 accepted2459
def lo2460b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨24,by decide⟩
def lo2460b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨25,by decide⟩
def lo2460 : CheckedMoment :=
  CheckedMoment.ofBessel lo2460b1 lo2460b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2460b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨29,by decide⟩
def hi2460b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨30,by decide⟩
def hi2460 : CheckedMoment :=
  CheckedMoment.ofBessel hi2460b1 hi2460b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2460 : meanBracketCheck (24791/25000) lo2460 hi2460=true := by decide +kernel
def bracket2460 : MeanBracket := meanBracketOfMoments (24791/25000) lo2460 hi2460 accepted2460
def lo2461b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨34,by decide⟩
def lo2461b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨35,by decide⟩
def lo2461 : CheckedMoment :=
  CheckedMoment.ofBessel lo2461b1 lo2461b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2461b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨39,by decide⟩
def hi2461b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨40,by decide⟩
def hi2461 : CheckedMoment :=
  CheckedMoment.ofBessel hi2461b1 hi2461b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2461 : meanBracketCheck (49583/50000) lo2461 hi2461=true := by decide +kernel
def bracket2461 : MeanBracket := meanBracketOfMoments (49583/50000) lo2461 hi2461 accepted2461
def lo2462b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨44,by decide⟩
def lo2462b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨45,by decide⟩
def lo2462 : CheckedMoment :=
  CheckedMoment.ofBessel lo2462b1 lo2462b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2462b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨49,by decide⟩
def hi2462b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨50,by decide⟩
def hi2462 : CheckedMoment :=
  CheckedMoment.ofBessel hi2462b1 hi2462b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2462 : meanBracketCheck (3099/3125) lo2462 hi2462=true := by decide +kernel
def bracket2462 : MeanBracket := meanBracketOfMoments (3099/3125) lo2462 hi2462 accepted2462
def lo2463b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨54,by decide⟩
def lo2463b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨55,by decide⟩
def lo2463 : CheckedMoment :=
  CheckedMoment.ofBessel lo2463b1 lo2463b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2463b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨59,by decide⟩
def hi2463b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0384.rows BesselBatch0384.accepted ⟨60,by decide⟩
def hi2463 : CheckedMoment :=
  CheckedMoment.ofBessel hi2463b1 hi2463b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2463 : meanBracketCheck (9917/10000) lo2463 hi2463=true := by decide +kernel
def bracket2463 : MeanBracket := meanBracketOfMoments (9917/10000) lo2463 hi2463 accepted2463
#print axioms bracket2448
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0153
