module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0242
public import BecknerOnofri.EntropyScalarCertificate.Bessel0243
public import BecknerOnofri.EntropyScalarCertificate.Bessel0244

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0097
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1552b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨32,by decide⟩
def lo1552b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨33,by decide⟩
def lo1552 : CheckedMoment :=
  CheckedMoment.ofBessel lo1552b1 lo1552b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1552b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨37,by decide⟩
def hi1552b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨38,by decide⟩
def hi1552 : CheckedMoment :=
  CheckedMoment.ofBessel hi1552b1 hi1552b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1552 : meanBracketCheck (4237/5000) lo1552 hi1552=true := by decide +kernel
def bracket1552 : MeanBracket := meanBracketOfMoments (4237/5000) lo1552 hi1552 accepted1552
def lo1553b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨42,by decide⟩
def lo1553b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨43,by decide⟩
def lo1553 : CheckedMoment :=
  CheckedMoment.ofBessel lo1553b1 lo1553b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1553b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨47,by decide⟩
def hi1553b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨48,by decide⟩
def hi1553 : CheckedMoment :=
  CheckedMoment.ofBessel hi1553b1 hi1553b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1553 : meanBracketCheck (339/400) lo1553 hi1553=true := by decide +kernel
def bracket1553 : MeanBracket := meanBracketOfMoments (339/400) lo1553 hi1553 accepted1553
def lo1554b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨52,by decide⟩
def lo1554b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨53,by decide⟩
def lo1554 : CheckedMoment :=
  CheckedMoment.ofBessel lo1554b1 lo1554b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1554b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨57,by decide⟩
def hi1554b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨58,by decide⟩
def hi1554 : CheckedMoment :=
  CheckedMoment.ofBessel hi1554b1 hi1554b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1554 : meanBracketCheck (2119/2500) lo1554 hi1554=true := by decide +kernel
def bracket1554 : MeanBracket := meanBracketOfMoments (2119/2500) lo1554 hi1554 accepted1554
def lo1555b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨62,by decide⟩
def lo1555b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0242.rows BesselBatch0242.accepted ⟨63,by decide⟩
def lo1555 : CheckedMoment :=
  CheckedMoment.ofBessel lo1555b1 lo1555b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1555b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨3,by decide⟩
def hi1555b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨4,by decide⟩
def hi1555 : CheckedMoment :=
  CheckedMoment.ofBessel hi1555b1 hi1555b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1555 : meanBracketCheck (8477/10000) lo1555 hi1555=true := by decide +kernel
def bracket1555 : MeanBracket := meanBracketOfMoments (8477/10000) lo1555 hi1555 accepted1555
def lo1556b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨8,by decide⟩
def lo1556b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨9,by decide⟩
def lo1556 : CheckedMoment :=
  CheckedMoment.ofBessel lo1556b1 lo1556b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1556b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨13,by decide⟩
def hi1556b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨14,by decide⟩
def hi1556 : CheckedMoment :=
  CheckedMoment.ofBessel hi1556b1 hi1556b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1556 : meanBracketCheck (4239/5000) lo1556 hi1556=true := by decide +kernel
def bracket1556 : MeanBracket := meanBracketOfMoments (4239/5000) lo1556 hi1556 accepted1556
def lo1557b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨18,by decide⟩
def lo1557b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨19,by decide⟩
def lo1557 : CheckedMoment :=
  CheckedMoment.ofBessel lo1557b1 lo1557b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1557b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨23,by decide⟩
def hi1557b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨24,by decide⟩
def hi1557 : CheckedMoment :=
  CheckedMoment.ofBessel hi1557b1 hi1557b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1557 : meanBracketCheck (8479/10000) lo1557 hi1557=true := by decide +kernel
def bracket1557 : MeanBracket := meanBracketOfMoments (8479/10000) lo1557 hi1557 accepted1557
def lo1558b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨28,by decide⟩
def lo1558b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨29,by decide⟩
def lo1558 : CheckedMoment :=
  CheckedMoment.ofBessel lo1558b1 lo1558b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1558b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨33,by decide⟩
def hi1558b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨34,by decide⟩
def hi1558 : CheckedMoment :=
  CheckedMoment.ofBessel hi1558b1 hi1558b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1558 : meanBracketCheck (106/125) lo1558 hi1558=true := by decide +kernel
def bracket1558 : MeanBracket := meanBracketOfMoments (106/125) lo1558 hi1558 accepted1558
def lo1559b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨38,by decide⟩
def lo1559b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨39,by decide⟩
def lo1559 : CheckedMoment :=
  CheckedMoment.ofBessel lo1559b1 lo1559b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1559b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨43,by decide⟩
def hi1559b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨44,by decide⟩
def hi1559 : CheckedMoment :=
  CheckedMoment.ofBessel hi1559b1 hi1559b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1559 : meanBracketCheck (8481/10000) lo1559 hi1559=true := by decide +kernel
def bracket1559 : MeanBracket := meanBracketOfMoments (8481/10000) lo1559 hi1559 accepted1559
def lo1560b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨48,by decide⟩
def lo1560b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨49,by decide⟩
def lo1560 : CheckedMoment :=
  CheckedMoment.ofBessel lo1560b1 lo1560b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1560b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨53,by decide⟩
def hi1560b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨54,by decide⟩
def hi1560 : CheckedMoment :=
  CheckedMoment.ofBessel hi1560b1 hi1560b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1560 : meanBracketCheck (4241/5000) lo1560 hi1560=true := by decide +kernel
def bracket1560 : MeanBracket := meanBracketOfMoments (4241/5000) lo1560 hi1560 accepted1560
def lo1561b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨58,by decide⟩
def lo1561b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨59,by decide⟩
def lo1561 : CheckedMoment :=
  CheckedMoment.ofBessel lo1561b1 lo1561b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1561b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0243.rows BesselBatch0243.accepted ⟨63,by decide⟩
def hi1561b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨0,by decide⟩
def hi1561 : CheckedMoment :=
  CheckedMoment.ofBessel hi1561b1 hi1561b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1561 : meanBracketCheck (8483/10000) lo1561 hi1561=true := by decide +kernel
def bracket1561 : MeanBracket := meanBracketOfMoments (8483/10000) lo1561 hi1561 accepted1561
def lo1562b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨4,by decide⟩
def lo1562b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨5,by decide⟩
def lo1562 : CheckedMoment :=
  CheckedMoment.ofBessel lo1562b1 lo1562b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1562b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨9,by decide⟩
def hi1562b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨10,by decide⟩
def hi1562 : CheckedMoment :=
  CheckedMoment.ofBessel hi1562b1 hi1562b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1562 : meanBracketCheck (2121/2500) lo1562 hi1562=true := by decide +kernel
def bracket1562 : MeanBracket := meanBracketOfMoments (2121/2500) lo1562 hi1562 accepted1562
def lo1563b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨14,by decide⟩
def lo1563b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨15,by decide⟩
def lo1563 : CheckedMoment :=
  CheckedMoment.ofBessel lo1563b1 lo1563b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1563b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨19,by decide⟩
def hi1563b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨20,by decide⟩
def hi1563 : CheckedMoment :=
  CheckedMoment.ofBessel hi1563b1 hi1563b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1563 : meanBracketCheck (1697/2000) lo1563 hi1563=true := by decide +kernel
def bracket1563 : MeanBracket := meanBracketOfMoments (1697/2000) lo1563 hi1563 accepted1563
def lo1564b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨24,by decide⟩
def lo1564b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨25,by decide⟩
def lo1564 : CheckedMoment :=
  CheckedMoment.ofBessel lo1564b1 lo1564b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1564b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨29,by decide⟩
def hi1564b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨30,by decide⟩
def hi1564 : CheckedMoment :=
  CheckedMoment.ofBessel hi1564b1 hi1564b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1564 : meanBracketCheck (4243/5000) lo1564 hi1564=true := by decide +kernel
def bracket1564 : MeanBracket := meanBracketOfMoments (4243/5000) lo1564 hi1564 accepted1564
def lo1565b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨34,by decide⟩
def lo1565b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨35,by decide⟩
def lo1565 : CheckedMoment :=
  CheckedMoment.ofBessel lo1565b1 lo1565b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1565b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨39,by decide⟩
def hi1565b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨40,by decide⟩
def hi1565 : CheckedMoment :=
  CheckedMoment.ofBessel hi1565b1 hi1565b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1565 : meanBracketCheck (8487/10000) lo1565 hi1565=true := by decide +kernel
def bracket1565 : MeanBracket := meanBracketOfMoments (8487/10000) lo1565 hi1565 accepted1565
def lo1566b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨44,by decide⟩
def lo1566b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨45,by decide⟩
def lo1566 : CheckedMoment :=
  CheckedMoment.ofBessel lo1566b1 lo1566b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1566b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨49,by decide⟩
def hi1566b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨50,by decide⟩
def hi1566 : CheckedMoment :=
  CheckedMoment.ofBessel hi1566b1 hi1566b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1566 : meanBracketCheck (1061/1250) lo1566 hi1566=true := by decide +kernel
def bracket1566 : MeanBracket := meanBracketOfMoments (1061/1250) lo1566 hi1566 accepted1566
def lo1567b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨54,by decide⟩
def lo1567b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨55,by decide⟩
def lo1567 : CheckedMoment :=
  CheckedMoment.ofBessel lo1567b1 lo1567b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1567b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨59,by decide⟩
def hi1567b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0244.rows BesselBatch0244.accepted ⟨60,by decide⟩
def hi1567 : CheckedMoment :=
  CheckedMoment.ofBessel hi1567b1 hi1567b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1567 : meanBracketCheck (8489/10000) lo1567 hi1567=true := by decide +kernel
def bracket1567 : MeanBracket := meanBracketOfMoments (8489/10000) lo1567 hi1567 accepted1567
#print axioms bracket1552
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0097
