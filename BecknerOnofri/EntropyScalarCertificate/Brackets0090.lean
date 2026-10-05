module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0225
public import BecknerOnofri.EntropyScalarCertificate.Bessel0226
public import BecknerOnofri.EntropyScalarCertificate.Bessel0227

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0090
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1440b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨0,by decide⟩
def lo1440b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨1,by decide⟩
def lo1440 : CheckedMoment :=
  CheckedMoment.ofBessel lo1440b1 lo1440b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1440b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨5,by decide⟩
def hi1440b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨6,by decide⟩
def hi1440 : CheckedMoment :=
  CheckedMoment.ofBessel hi1440b1 hi1440b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1440 : meanBracketCheck (4181/5000) lo1440 hi1440=true := by decide +kernel
def bracket1440 : MeanBracket := meanBracketOfMoments (4181/5000) lo1440 hi1440 accepted1440
def lo1441b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨10,by decide⟩
def lo1441b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨11,by decide⟩
def lo1441 : CheckedMoment :=
  CheckedMoment.ofBessel lo1441b1 lo1441b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1441b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨15,by decide⟩
def hi1441b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨16,by decide⟩
def hi1441 : CheckedMoment :=
  CheckedMoment.ofBessel hi1441b1 hi1441b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1441 : meanBracketCheck (8363/10000) lo1441 hi1441=true := by decide +kernel
def bracket1441 : MeanBracket := meanBracketOfMoments (8363/10000) lo1441 hi1441 accepted1441
def lo1442b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨20,by decide⟩
def lo1442b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨21,by decide⟩
def lo1442 : CheckedMoment :=
  CheckedMoment.ofBessel lo1442b1 lo1442b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1442b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨25,by decide⟩
def hi1442b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨26,by decide⟩
def hi1442 : CheckedMoment :=
  CheckedMoment.ofBessel hi1442b1 hi1442b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1442 : meanBracketCheck (2091/2500) lo1442 hi1442=true := by decide +kernel
def bracket1442 : MeanBracket := meanBracketOfMoments (2091/2500) lo1442 hi1442 accepted1442
def lo1443b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨30,by decide⟩
def lo1443b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨31,by decide⟩
def lo1443 : CheckedMoment :=
  CheckedMoment.ofBessel lo1443b1 lo1443b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1443b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨35,by decide⟩
def hi1443b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨36,by decide⟩
def hi1443 : CheckedMoment :=
  CheckedMoment.ofBessel hi1443b1 hi1443b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1443 : meanBracketCheck (1673/2000) lo1443 hi1443=true := by decide +kernel
def bracket1443 : MeanBracket := meanBracketOfMoments (1673/2000) lo1443 hi1443 accepted1443
def lo1444b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨40,by decide⟩
def lo1444b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨41,by decide⟩
def lo1444 : CheckedMoment :=
  CheckedMoment.ofBessel lo1444b1 lo1444b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1444b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨45,by decide⟩
def hi1444b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨46,by decide⟩
def hi1444 : CheckedMoment :=
  CheckedMoment.ofBessel hi1444b1 hi1444b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1444 : meanBracketCheck (4183/5000) lo1444 hi1444=true := by decide +kernel
def bracket1444 : MeanBracket := meanBracketOfMoments (4183/5000) lo1444 hi1444 accepted1444
def lo1445b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨50,by decide⟩
def lo1445b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨51,by decide⟩
def lo1445 : CheckedMoment :=
  CheckedMoment.ofBessel lo1445b1 lo1445b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1445b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨55,by decide⟩
def hi1445b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨56,by decide⟩
def hi1445 : CheckedMoment :=
  CheckedMoment.ofBessel hi1445b1 hi1445b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1445 : meanBracketCheck (8367/10000) lo1445 hi1445=true := by decide +kernel
def bracket1445 : MeanBracket := meanBracketOfMoments (8367/10000) lo1445 hi1445 accepted1445
def lo1446b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨60,by decide⟩
def lo1446b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨61,by decide⟩
def lo1446 : CheckedMoment :=
  CheckedMoment.ofBessel lo1446b1 lo1446b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1446b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨1,by decide⟩
def hi1446b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨2,by decide⟩
def hi1446 : CheckedMoment :=
  CheckedMoment.ofBessel hi1446b1 hi1446b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1446 : meanBracketCheck (523/625) lo1446 hi1446=true := by decide +kernel
def bracket1446 : MeanBracket := meanBracketOfMoments (523/625) lo1446 hi1446 accepted1446
def lo1447b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨6,by decide⟩
def lo1447b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨7,by decide⟩
def lo1447 : CheckedMoment :=
  CheckedMoment.ofBessel lo1447b1 lo1447b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1447b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨11,by decide⟩
def hi1447b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨12,by decide⟩
def hi1447 : CheckedMoment :=
  CheckedMoment.ofBessel hi1447b1 hi1447b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1447 : meanBracketCheck (8369/10000) lo1447 hi1447=true := by decide +kernel
def bracket1447 : MeanBracket := meanBracketOfMoments (8369/10000) lo1447 hi1447 accepted1447
def lo1448b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨16,by decide⟩
def lo1448b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨17,by decide⟩
def lo1448 : CheckedMoment :=
  CheckedMoment.ofBessel lo1448b1 lo1448b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1448b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨21,by decide⟩
def hi1448b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨22,by decide⟩
def hi1448 : CheckedMoment :=
  CheckedMoment.ofBessel hi1448b1 hi1448b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1448 : meanBracketCheck (837/1000) lo1448 hi1448=true := by decide +kernel
def bracket1448 : MeanBracket := meanBracketOfMoments (837/1000) lo1448 hi1448 accepted1448
def lo1449b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨26,by decide⟩
def lo1449b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨27,by decide⟩
def lo1449 : CheckedMoment :=
  CheckedMoment.ofBessel lo1449b1 lo1449b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1449b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨31,by decide⟩
def hi1449b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨32,by decide⟩
def hi1449 : CheckedMoment :=
  CheckedMoment.ofBessel hi1449b1 hi1449b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1449 : meanBracketCheck (8371/10000) lo1449 hi1449=true := by decide +kernel
def bracket1449 : MeanBracket := meanBracketOfMoments (8371/10000) lo1449 hi1449 accepted1449
def lo1450b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨36,by decide⟩
def lo1450b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨37,by decide⟩
def lo1450 : CheckedMoment :=
  CheckedMoment.ofBessel lo1450b1 lo1450b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1450b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨41,by decide⟩
def hi1450b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨42,by decide⟩
def hi1450 : CheckedMoment :=
  CheckedMoment.ofBessel hi1450b1 hi1450b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1450 : meanBracketCheck (2093/2500) lo1450 hi1450=true := by decide +kernel
def bracket1450 : MeanBracket := meanBracketOfMoments (2093/2500) lo1450 hi1450 accepted1450
def lo1451b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨46,by decide⟩
def lo1451b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨47,by decide⟩
def lo1451 : CheckedMoment :=
  CheckedMoment.ofBessel lo1451b1 lo1451b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1451b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨51,by decide⟩
def hi1451b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨52,by decide⟩
def hi1451 : CheckedMoment :=
  CheckedMoment.ofBessel hi1451b1 hi1451b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1451 : meanBracketCheck (8373/10000) lo1451 hi1451=true := by decide +kernel
def bracket1451 : MeanBracket := meanBracketOfMoments (8373/10000) lo1451 hi1451 accepted1451
def lo1452b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨56,by decide⟩
def lo1452b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨57,by decide⟩
def lo1452 : CheckedMoment :=
  CheckedMoment.ofBessel lo1452b1 lo1452b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1452b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨61,by decide⟩
def hi1452b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨62,by decide⟩
def hi1452 : CheckedMoment :=
  CheckedMoment.ofBessel hi1452b1 hi1452b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1452 : meanBracketCheck (4187/5000) lo1452 hi1452=true := by decide +kernel
def bracket1452 : MeanBracket := meanBracketOfMoments (4187/5000) lo1452 hi1452 accepted1452
def lo1453b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨2,by decide⟩
def lo1453b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨3,by decide⟩
def lo1453 : CheckedMoment :=
  CheckedMoment.ofBessel lo1453b1 lo1453b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1453b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨7,by decide⟩
def hi1453b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨8,by decide⟩
def hi1453 : CheckedMoment :=
  CheckedMoment.ofBessel hi1453b1 hi1453b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1453 : meanBracketCheck (67/80) lo1453 hi1453=true := by decide +kernel
def bracket1453 : MeanBracket := meanBracketOfMoments (67/80) lo1453 hi1453 accepted1453
def lo1454b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨12,by decide⟩
def lo1454b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨13,by decide⟩
def lo1454 : CheckedMoment :=
  CheckedMoment.ofBessel lo1454b1 lo1454b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1454b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨17,by decide⟩
def hi1454b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨18,by decide⟩
def hi1454 : CheckedMoment :=
  CheckedMoment.ofBessel hi1454b1 hi1454b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1454 : meanBracketCheck (1047/1250) lo1454 hi1454=true := by decide +kernel
def bracket1454 : MeanBracket := meanBracketOfMoments (1047/1250) lo1454 hi1454 accepted1454
def lo1455b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨22,by decide⟩
def lo1455b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨23,by decide⟩
def lo1455 : CheckedMoment :=
  CheckedMoment.ofBessel lo1455b1 lo1455b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1455b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨27,by decide⟩
def hi1455b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨28,by decide⟩
def hi1455 : CheckedMoment :=
  CheckedMoment.ofBessel hi1455b1 hi1455b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1455 : meanBracketCheck (8377/10000) lo1455 hi1455=true := by decide +kernel
def bracket1455 : MeanBracket := meanBracketOfMoments (8377/10000) lo1455 hi1455 accepted1455
#print axioms bracket1440
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0090
