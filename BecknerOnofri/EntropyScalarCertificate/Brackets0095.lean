module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0237
public import BecknerOnofri.EntropyScalarCertificate.Bessel0238
public import BecknerOnofri.EntropyScalarCertificate.Bessel0239

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0095
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1520b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨32,by decide⟩
def lo1520b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨33,by decide⟩
def lo1520 : CheckedMoment :=
  CheckedMoment.ofBessel lo1520b1 lo1520b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1520b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨37,by decide⟩
def hi1520b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨38,by decide⟩
def hi1520 : CheckedMoment :=
  CheckedMoment.ofBessel hi1520b1 hi1520b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1520 : meanBracketCheck (4221/5000) lo1520 hi1520=true := by decide +kernel
def bracket1520 : MeanBracket := meanBracketOfMoments (4221/5000) lo1520 hi1520 accepted1520
def lo1521b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨42,by decide⟩
def lo1521b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨43,by decide⟩
def lo1521 : CheckedMoment :=
  CheckedMoment.ofBessel lo1521b1 lo1521b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1521b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨47,by decide⟩
def hi1521b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨48,by decide⟩
def hi1521 : CheckedMoment :=
  CheckedMoment.ofBessel hi1521b1 hi1521b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1521 : meanBracketCheck (8443/10000) lo1521 hi1521=true := by decide +kernel
def bracket1521 : MeanBracket := meanBracketOfMoments (8443/10000) lo1521 hi1521 accepted1521
def lo1522b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨52,by decide⟩
def lo1522b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨53,by decide⟩
def lo1522 : CheckedMoment :=
  CheckedMoment.ofBessel lo1522b1 lo1522b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1522b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨57,by decide⟩
def hi1522b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨58,by decide⟩
def hi1522 : CheckedMoment :=
  CheckedMoment.ofBessel hi1522b1 hi1522b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1522 : meanBracketCheck (2111/2500) lo1522 hi1522=true := by decide +kernel
def bracket1522 : MeanBracket := meanBracketOfMoments (2111/2500) lo1522 hi1522 accepted1522
def lo1523b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨62,by decide⟩
def lo1523b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨63,by decide⟩
def lo1523 : CheckedMoment :=
  CheckedMoment.ofBessel lo1523b1 lo1523b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1523b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨3,by decide⟩
def hi1523b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨4,by decide⟩
def hi1523 : CheckedMoment :=
  CheckedMoment.ofBessel hi1523b1 hi1523b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1523 : meanBracketCheck (1689/2000) lo1523 hi1523=true := by decide +kernel
def bracket1523 : MeanBracket := meanBracketOfMoments (1689/2000) lo1523 hi1523 accepted1523
def lo1524b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨8,by decide⟩
def lo1524b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨9,by decide⟩
def lo1524 : CheckedMoment :=
  CheckedMoment.ofBessel lo1524b1 lo1524b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1524b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨13,by decide⟩
def hi1524b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨14,by decide⟩
def hi1524 : CheckedMoment :=
  CheckedMoment.ofBessel hi1524b1 hi1524b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1524 : meanBracketCheck (4223/5000) lo1524 hi1524=true := by decide +kernel
def bracket1524 : MeanBracket := meanBracketOfMoments (4223/5000) lo1524 hi1524 accepted1524
def lo1525b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨18,by decide⟩
def lo1525b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨19,by decide⟩
def lo1525 : CheckedMoment :=
  CheckedMoment.ofBessel lo1525b1 lo1525b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1525b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨23,by decide⟩
def hi1525b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨24,by decide⟩
def hi1525 : CheckedMoment :=
  CheckedMoment.ofBessel hi1525b1 hi1525b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1525 : meanBracketCheck (8447/10000) lo1525 hi1525=true := by decide +kernel
def bracket1525 : MeanBracket := meanBracketOfMoments (8447/10000) lo1525 hi1525 accepted1525
def lo1526b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨28,by decide⟩
def lo1526b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨29,by decide⟩
def lo1526 : CheckedMoment :=
  CheckedMoment.ofBessel lo1526b1 lo1526b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1526b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨33,by decide⟩
def hi1526b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨34,by decide⟩
def hi1526 : CheckedMoment :=
  CheckedMoment.ofBessel hi1526b1 hi1526b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1526 : meanBracketCheck (528/625) lo1526 hi1526=true := by decide +kernel
def bracket1526 : MeanBracket := meanBracketOfMoments (528/625) lo1526 hi1526 accepted1526
def lo1527b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨38,by decide⟩
def lo1527b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨39,by decide⟩
def lo1527 : CheckedMoment :=
  CheckedMoment.ofBessel lo1527b1 lo1527b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1527b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨43,by decide⟩
def hi1527b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨44,by decide⟩
def hi1527 : CheckedMoment :=
  CheckedMoment.ofBessel hi1527b1 hi1527b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1527 : meanBracketCheck (8449/10000) lo1527 hi1527=true := by decide +kernel
def bracket1527 : MeanBracket := meanBracketOfMoments (8449/10000) lo1527 hi1527 accepted1527
def lo1528b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨48,by decide⟩
def lo1528b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨49,by decide⟩
def lo1528 : CheckedMoment :=
  CheckedMoment.ofBessel lo1528b1 lo1528b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1528b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨53,by decide⟩
def hi1528b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨54,by decide⟩
def hi1528 : CheckedMoment :=
  CheckedMoment.ofBessel hi1528b1 hi1528b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1528 : meanBracketCheck (169/200) lo1528 hi1528=true := by decide +kernel
def bracket1528 : MeanBracket := meanBracketOfMoments (169/200) lo1528 hi1528 accepted1528
def lo1529b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨58,by decide⟩
def lo1529b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨59,by decide⟩
def lo1529 : CheckedMoment :=
  CheckedMoment.ofBessel lo1529b1 lo1529b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1529b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨63,by decide⟩
def hi1529b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨0,by decide⟩
def hi1529 : CheckedMoment :=
  CheckedMoment.ofBessel hi1529b1 hi1529b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1529 : meanBracketCheck (8451/10000) lo1529 hi1529=true := by decide +kernel
def bracket1529 : MeanBracket := meanBracketOfMoments (8451/10000) lo1529 hi1529 accepted1529
def lo1530b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨4,by decide⟩
def lo1530b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨5,by decide⟩
def lo1530 : CheckedMoment :=
  CheckedMoment.ofBessel lo1530b1 lo1530b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1530b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨9,by decide⟩
def hi1530b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨10,by decide⟩
def hi1530 : CheckedMoment :=
  CheckedMoment.ofBessel hi1530b1 hi1530b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1530 : meanBracketCheck (2113/2500) lo1530 hi1530=true := by decide +kernel
def bracket1530 : MeanBracket := meanBracketOfMoments (2113/2500) lo1530 hi1530 accepted1530
def lo1531b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨14,by decide⟩
def lo1531b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨15,by decide⟩
def lo1531 : CheckedMoment :=
  CheckedMoment.ofBessel lo1531b1 lo1531b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1531b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨19,by decide⟩
def hi1531b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨20,by decide⟩
def hi1531 : CheckedMoment :=
  CheckedMoment.ofBessel hi1531b1 hi1531b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1531 : meanBracketCheck (8453/10000) lo1531 hi1531=true := by decide +kernel
def bracket1531 : MeanBracket := meanBracketOfMoments (8453/10000) lo1531 hi1531 accepted1531
def lo1532b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨24,by decide⟩
def lo1532b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨25,by decide⟩
def lo1532 : CheckedMoment :=
  CheckedMoment.ofBessel lo1532b1 lo1532b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1532b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨29,by decide⟩
def hi1532b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨30,by decide⟩
def hi1532 : CheckedMoment :=
  CheckedMoment.ofBessel hi1532b1 hi1532b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1532 : meanBracketCheck (4227/5000) lo1532 hi1532=true := by decide +kernel
def bracket1532 : MeanBracket := meanBracketOfMoments (4227/5000) lo1532 hi1532 accepted1532
def lo1533b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨34,by decide⟩
def lo1533b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨35,by decide⟩
def lo1533 : CheckedMoment :=
  CheckedMoment.ofBessel lo1533b1 lo1533b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1533b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨39,by decide⟩
def hi1533b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨40,by decide⟩
def hi1533 : CheckedMoment :=
  CheckedMoment.ofBessel hi1533b1 hi1533b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1533 : meanBracketCheck (1691/2000) lo1533 hi1533=true := by decide +kernel
def bracket1533 : MeanBracket := meanBracketOfMoments (1691/2000) lo1533 hi1533 accepted1533
def lo1534b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨44,by decide⟩
def lo1534b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨45,by decide⟩
def lo1534 : CheckedMoment :=
  CheckedMoment.ofBessel lo1534b1 lo1534b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1534b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨49,by decide⟩
def hi1534b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨50,by decide⟩
def hi1534 : CheckedMoment :=
  CheckedMoment.ofBessel hi1534b1 hi1534b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1534 : meanBracketCheck (1057/1250) lo1534 hi1534=true := by decide +kernel
def bracket1534 : MeanBracket := meanBracketOfMoments (1057/1250) lo1534 hi1534 accepted1534
def lo1535b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨54,by decide⟩
def lo1535b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨55,by decide⟩
def lo1535 : CheckedMoment :=
  CheckedMoment.ofBessel lo1535b1 lo1535b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1535b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨59,by decide⟩
def hi1535b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨60,by decide⟩
def hi1535 : CheckedMoment :=
  CheckedMoment.ofBessel hi1535b1 hi1535b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1535 : meanBracketCheck (8457/10000) lo1535 hi1535=true := by decide +kernel
def bracket1535 : MeanBracket := meanBracketOfMoments (8457/10000) lo1535 hi1535 accepted1535
#print axioms bracket1520
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0095
