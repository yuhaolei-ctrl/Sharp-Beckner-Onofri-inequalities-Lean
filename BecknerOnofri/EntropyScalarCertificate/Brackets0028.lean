module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0070
public import BecknerOnofri.EntropyScalarCertificate.Bessel0071
public import BecknerOnofri.EntropyScalarCertificate.Bessel0072

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0028
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0448b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨0,by decide⟩
def lo0448b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨1,by decide⟩
def lo0448 : CheckedMoment :=
  CheckedMoment.ofBessel lo0448b1 lo0448b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0448b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨5,by decide⟩
def hi0448b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨6,by decide⟩
def hi0448 : CheckedMoment :=
  CheckedMoment.ofBessel hi0448b1 hi0448b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0448 : meanBracketCheck (1461/10000) lo0448 hi0448=true := by decide +kernel
def bracket0448 : MeanBracket := meanBracketOfMoments (1461/10000) lo0448 hi0448 accepted0448
def lo0449b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨10,by decide⟩
def lo0449b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨11,by decide⟩
def lo0449 : CheckedMoment :=
  CheckedMoment.ofBessel lo0449b1 lo0449b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0449b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨15,by decide⟩
def hi0449b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨16,by decide⟩
def hi0449 : CheckedMoment :=
  CheckedMoment.ofBessel hi0449b1 hi0449b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0449 : meanBracketCheck (1463/10000) lo0449 hi0449=true := by decide +kernel
def bracket0449 : MeanBracket := meanBracketOfMoments (1463/10000) lo0449 hi0449 accepted0449
def lo0450b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨20,by decide⟩
def lo0450b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨21,by decide⟩
def lo0450 : CheckedMoment :=
  CheckedMoment.ofBessel lo0450b1 lo0450b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0450b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨25,by decide⟩
def hi0450b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨26,by decide⟩
def hi0450 : CheckedMoment :=
  CheckedMoment.ofBessel hi0450b1 hi0450b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0450 : meanBracketCheck (293/2000) lo0450 hi0450=true := by decide +kernel
def bracket0450 : MeanBracket := meanBracketOfMoments (293/2000) lo0450 hi0450 accepted0450
def lo0451b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨30,by decide⟩
def lo0451b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨31,by decide⟩
def lo0451 : CheckedMoment :=
  CheckedMoment.ofBessel lo0451b1 lo0451b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0451b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨35,by decide⟩
def hi0451b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨36,by decide⟩
def hi0451 : CheckedMoment :=
  CheckedMoment.ofBessel hi0451b1 hi0451b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0451 : meanBracketCheck (1467/10000) lo0451 hi0451=true := by decide +kernel
def bracket0451 : MeanBracket := meanBracketOfMoments (1467/10000) lo0451 hi0451 accepted0451
def lo0452b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨40,by decide⟩
def lo0452b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨41,by decide⟩
def lo0452 : CheckedMoment :=
  CheckedMoment.ofBessel lo0452b1 lo0452b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0452b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨45,by decide⟩
def hi0452b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨46,by decide⟩
def hi0452 : CheckedMoment :=
  CheckedMoment.ofBessel hi0452b1 hi0452b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0452 : meanBracketCheck (1469/10000) lo0452 hi0452=true := by decide +kernel
def bracket0452 : MeanBracket := meanBracketOfMoments (1469/10000) lo0452 hi0452 accepted0452
def lo0453b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨50,by decide⟩
def lo0453b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨51,by decide⟩
def lo0453 : CheckedMoment :=
  CheckedMoment.ofBessel lo0453b1 lo0453b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0453b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨55,by decide⟩
def hi0453b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨56,by decide⟩
def hi0453 : CheckedMoment :=
  CheckedMoment.ofBessel hi0453b1 hi0453b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0453 : meanBracketCheck (1471/10000) lo0453 hi0453=true := by decide +kernel
def bracket0453 : MeanBracket := meanBracketOfMoments (1471/10000) lo0453 hi0453 accepted0453
def lo0454b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨60,by decide⟩
def lo0454b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨61,by decide⟩
def lo0454 : CheckedMoment :=
  CheckedMoment.ofBessel lo0454b1 lo0454b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0454b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨1,by decide⟩
def hi0454b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨2,by decide⟩
def hi0454 : CheckedMoment :=
  CheckedMoment.ofBessel hi0454b1 hi0454b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0454 : meanBracketCheck (1473/10000) lo0454 hi0454=true := by decide +kernel
def bracket0454 : MeanBracket := meanBracketOfMoments (1473/10000) lo0454 hi0454 accepted0454
def lo0455b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨6,by decide⟩
def lo0455b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨7,by decide⟩
def lo0455 : CheckedMoment :=
  CheckedMoment.ofBessel lo0455b1 lo0455b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0455b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨11,by decide⟩
def hi0455b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨12,by decide⟩
def hi0455 : CheckedMoment :=
  CheckedMoment.ofBessel hi0455b1 hi0455b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0455 : meanBracketCheck (59/400) lo0455 hi0455=true := by decide +kernel
def bracket0455 : MeanBracket := meanBracketOfMoments (59/400) lo0455 hi0455 accepted0455
def lo0456b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨16,by decide⟩
def lo0456b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨17,by decide⟩
def lo0456 : CheckedMoment :=
  CheckedMoment.ofBessel lo0456b1 lo0456b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0456b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨21,by decide⟩
def hi0456b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨22,by decide⟩
def hi0456 : CheckedMoment :=
  CheckedMoment.ofBessel hi0456b1 hi0456b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0456 : meanBracketCheck (1477/10000) lo0456 hi0456=true := by decide +kernel
def bracket0456 : MeanBracket := meanBracketOfMoments (1477/10000) lo0456 hi0456 accepted0456
def lo0457b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨26,by decide⟩
def lo0457b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨27,by decide⟩
def lo0457 : CheckedMoment :=
  CheckedMoment.ofBessel lo0457b1 lo0457b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0457b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨31,by decide⟩
def hi0457b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨32,by decide⟩
def hi0457 : CheckedMoment :=
  CheckedMoment.ofBessel hi0457b1 hi0457b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0457 : meanBracketCheck (1479/10000) lo0457 hi0457=true := by decide +kernel
def bracket0457 : MeanBracket := meanBracketOfMoments (1479/10000) lo0457 hi0457 accepted0457
def lo0458b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨36,by decide⟩
def lo0458b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨37,by decide⟩
def lo0458 : CheckedMoment :=
  CheckedMoment.ofBessel lo0458b1 lo0458b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0458b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨41,by decide⟩
def hi0458b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨42,by decide⟩
def hi0458 : CheckedMoment :=
  CheckedMoment.ofBessel hi0458b1 hi0458b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0458 : meanBracketCheck (1481/10000) lo0458 hi0458=true := by decide +kernel
def bracket0458 : MeanBracket := meanBracketOfMoments (1481/10000) lo0458 hi0458 accepted0458
def lo0459b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨46,by decide⟩
def lo0459b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨47,by decide⟩
def lo0459 : CheckedMoment :=
  CheckedMoment.ofBessel lo0459b1 lo0459b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0459b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨51,by decide⟩
def hi0459b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨52,by decide⟩
def hi0459 : CheckedMoment :=
  CheckedMoment.ofBessel hi0459b1 hi0459b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0459 : meanBracketCheck (1483/10000) lo0459 hi0459=true := by decide +kernel
def bracket0459 : MeanBracket := meanBracketOfMoments (1483/10000) lo0459 hi0459 accepted0459
def lo0460b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨56,by decide⟩
def lo0460b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨57,by decide⟩
def lo0460 : CheckedMoment :=
  CheckedMoment.ofBessel lo0460b1 lo0460b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0460b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨61,by decide⟩
def hi0460b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨62,by decide⟩
def hi0460 : CheckedMoment :=
  CheckedMoment.ofBessel hi0460b1 hi0460b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0460 : meanBracketCheck (297/2000) lo0460 hi0460=true := by decide +kernel
def bracket0460 : MeanBracket := meanBracketOfMoments (297/2000) lo0460 hi0460 accepted0460
def lo0461b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨2,by decide⟩
def lo0461b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨3,by decide⟩
def lo0461 : CheckedMoment :=
  CheckedMoment.ofBessel lo0461b1 lo0461b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0461b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨7,by decide⟩
def hi0461b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨8,by decide⟩
def hi0461 : CheckedMoment :=
  CheckedMoment.ofBessel hi0461b1 hi0461b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0461 : meanBracketCheck (1487/10000) lo0461 hi0461=true := by decide +kernel
def bracket0461 : MeanBracket := meanBracketOfMoments (1487/10000) lo0461 hi0461 accepted0461
def lo0462b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨12,by decide⟩
def lo0462b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨13,by decide⟩
def lo0462 : CheckedMoment :=
  CheckedMoment.ofBessel lo0462b1 lo0462b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0462b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨17,by decide⟩
def hi0462b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨18,by decide⟩
def hi0462 : CheckedMoment :=
  CheckedMoment.ofBessel hi0462b1 hi0462b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0462 : meanBracketCheck (1489/10000) lo0462 hi0462=true := by decide +kernel
def bracket0462 : MeanBracket := meanBracketOfMoments (1489/10000) lo0462 hi0462 accepted0462
def lo0463b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨22,by decide⟩
def lo0463b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨23,by decide⟩
def lo0463 : CheckedMoment :=
  CheckedMoment.ofBessel lo0463b1 lo0463b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0463b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨27,by decide⟩
def hi0463b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨28,by decide⟩
def hi0463 : CheckedMoment :=
  CheckedMoment.ofBessel hi0463b1 hi0463b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0463 : meanBracketCheck (1491/10000) lo0463 hi0463=true := by decide +kernel
def bracket0463 : MeanBracket := meanBracketOfMoments (1491/10000) lo0463 hi0463 accepted0463
#print axioms bracket0448
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0028
