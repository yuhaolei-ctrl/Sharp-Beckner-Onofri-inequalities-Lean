module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0092
public import BecknerOnofri.EntropyScalarCertificate.Bessel0093
public import BecknerOnofri.EntropyScalarCertificate.Bessel0094

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0037
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0592b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨32,by decide⟩
def lo0592b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨33,by decide⟩
def lo0592 : CheckedMoment :=
  CheckedMoment.ofBessel lo0592b1 lo0592b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0592b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨37,by decide⟩
def hi0592b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨38,by decide⟩
def hi0592 : CheckedMoment :=
  CheckedMoment.ofBessel hi0592b1 hi0592b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0592 : meanBracketCheck (1749/10000) lo0592 hi0592=true := by decide +kernel
def bracket0592 : MeanBracket := meanBracketOfMoments (1749/10000) lo0592 hi0592 accepted0592
def lo0593b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨42,by decide⟩
def lo0593b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨43,by decide⟩
def lo0593 : CheckedMoment :=
  CheckedMoment.ofBessel lo0593b1 lo0593b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0593b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨47,by decide⟩
def hi0593b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨48,by decide⟩
def hi0593 : CheckedMoment :=
  CheckedMoment.ofBessel hi0593b1 hi0593b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0593 : meanBracketCheck (1751/10000) lo0593 hi0593=true := by decide +kernel
def bracket0593 : MeanBracket := meanBracketOfMoments (1751/10000) lo0593 hi0593 accepted0593
def lo0594b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨52,by decide⟩
def lo0594b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨53,by decide⟩
def lo0594 : CheckedMoment :=
  CheckedMoment.ofBessel lo0594b1 lo0594b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0594b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨57,by decide⟩
def hi0594b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨58,by decide⟩
def hi0594 : CheckedMoment :=
  CheckedMoment.ofBessel hi0594b1 hi0594b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0594 : meanBracketCheck (1753/10000) lo0594 hi0594=true := by decide +kernel
def bracket0594 : MeanBracket := meanBracketOfMoments (1753/10000) lo0594 hi0594 accepted0594
def lo0595b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨62,by decide⟩
def lo0595b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨63,by decide⟩
def lo0595 : CheckedMoment :=
  CheckedMoment.ofBessel lo0595b1 lo0595b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0595b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨3,by decide⟩
def hi0595b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨4,by decide⟩
def hi0595 : CheckedMoment :=
  CheckedMoment.ofBessel hi0595b1 hi0595b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0595 : meanBracketCheck (351/2000) lo0595 hi0595=true := by decide +kernel
def bracket0595 : MeanBracket := meanBracketOfMoments (351/2000) lo0595 hi0595 accepted0595
def lo0596b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨8,by decide⟩
def lo0596b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨9,by decide⟩
def lo0596 : CheckedMoment :=
  CheckedMoment.ofBessel lo0596b1 lo0596b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0596b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨13,by decide⟩
def hi0596b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨14,by decide⟩
def hi0596 : CheckedMoment :=
  CheckedMoment.ofBessel hi0596b1 hi0596b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0596 : meanBracketCheck (1757/10000) lo0596 hi0596=true := by decide +kernel
def bracket0596 : MeanBracket := meanBracketOfMoments (1757/10000) lo0596 hi0596 accepted0596
def lo0597b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨18,by decide⟩
def lo0597b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨19,by decide⟩
def lo0597 : CheckedMoment :=
  CheckedMoment.ofBessel lo0597b1 lo0597b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0597b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨23,by decide⟩
def hi0597b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨24,by decide⟩
def hi0597 : CheckedMoment :=
  CheckedMoment.ofBessel hi0597b1 hi0597b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0597 : meanBracketCheck (1759/10000) lo0597 hi0597=true := by decide +kernel
def bracket0597 : MeanBracket := meanBracketOfMoments (1759/10000) lo0597 hi0597 accepted0597
def lo0598b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨28,by decide⟩
def lo0598b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨29,by decide⟩
def lo0598 : CheckedMoment :=
  CheckedMoment.ofBessel lo0598b1 lo0598b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0598b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨33,by decide⟩
def hi0598b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨34,by decide⟩
def hi0598 : CheckedMoment :=
  CheckedMoment.ofBessel hi0598b1 hi0598b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0598 : meanBracketCheck (1761/10000) lo0598 hi0598=true := by decide +kernel
def bracket0598 : MeanBracket := meanBracketOfMoments (1761/10000) lo0598 hi0598 accepted0598
def lo0599b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨38,by decide⟩
def lo0599b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨39,by decide⟩
def lo0599 : CheckedMoment :=
  CheckedMoment.ofBessel lo0599b1 lo0599b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0599b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨43,by decide⟩
def hi0599b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨44,by decide⟩
def hi0599 : CheckedMoment :=
  CheckedMoment.ofBessel hi0599b1 hi0599b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0599 : meanBracketCheck (1763/10000) lo0599 hi0599=true := by decide +kernel
def bracket0599 : MeanBracket := meanBracketOfMoments (1763/10000) lo0599 hi0599 accepted0599
def lo0600b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨48,by decide⟩
def lo0600b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨49,by decide⟩
def lo0600 : CheckedMoment :=
  CheckedMoment.ofBessel lo0600b1 lo0600b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0600b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨53,by decide⟩
def hi0600b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨54,by decide⟩
def hi0600 : CheckedMoment :=
  CheckedMoment.ofBessel hi0600b1 hi0600b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0600 : meanBracketCheck (353/2000) lo0600 hi0600=true := by decide +kernel
def bracket0600 : MeanBracket := meanBracketOfMoments (353/2000) lo0600 hi0600 accepted0600
def lo0601b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨58,by decide⟩
def lo0601b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨59,by decide⟩
def lo0601 : CheckedMoment :=
  CheckedMoment.ofBessel lo0601b1 lo0601b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0601b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨63,by decide⟩
def hi0601b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨0,by decide⟩
def hi0601 : CheckedMoment :=
  CheckedMoment.ofBessel hi0601b1 hi0601b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0601 : meanBracketCheck (1767/10000) lo0601 hi0601=true := by decide +kernel
def bracket0601 : MeanBracket := meanBracketOfMoments (1767/10000) lo0601 hi0601 accepted0601
def lo0602b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨4,by decide⟩
def lo0602b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨5,by decide⟩
def lo0602 : CheckedMoment :=
  CheckedMoment.ofBessel lo0602b1 lo0602b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0602b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨9,by decide⟩
def hi0602b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨10,by decide⟩
def hi0602 : CheckedMoment :=
  CheckedMoment.ofBessel hi0602b1 hi0602b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0602 : meanBracketCheck (1769/10000) lo0602 hi0602=true := by decide +kernel
def bracket0602 : MeanBracket := meanBracketOfMoments (1769/10000) lo0602 hi0602 accepted0602
def lo0603b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨14,by decide⟩
def lo0603b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨15,by decide⟩
def lo0603 : CheckedMoment :=
  CheckedMoment.ofBessel lo0603b1 lo0603b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0603b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨19,by decide⟩
def hi0603b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨20,by decide⟩
def hi0603 : CheckedMoment :=
  CheckedMoment.ofBessel hi0603b1 hi0603b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0603 : meanBracketCheck (1771/10000) lo0603 hi0603=true := by decide +kernel
def bracket0603 : MeanBracket := meanBracketOfMoments (1771/10000) lo0603 hi0603 accepted0603
def lo0604b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨24,by decide⟩
def lo0604b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨25,by decide⟩
def lo0604 : CheckedMoment :=
  CheckedMoment.ofBessel lo0604b1 lo0604b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0604b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨29,by decide⟩
def hi0604b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨30,by decide⟩
def hi0604 : CheckedMoment :=
  CheckedMoment.ofBessel hi0604b1 hi0604b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0604 : meanBracketCheck (1773/10000) lo0604 hi0604=true := by decide +kernel
def bracket0604 : MeanBracket := meanBracketOfMoments (1773/10000) lo0604 hi0604 accepted0604
def lo0605b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨34,by decide⟩
def lo0605b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨35,by decide⟩
def lo0605 : CheckedMoment :=
  CheckedMoment.ofBessel lo0605b1 lo0605b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0605b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨39,by decide⟩
def hi0605b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨40,by decide⟩
def hi0605 : CheckedMoment :=
  CheckedMoment.ofBessel hi0605b1 hi0605b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0605 : meanBracketCheck (71/400) lo0605 hi0605=true := by decide +kernel
def bracket0605 : MeanBracket := meanBracketOfMoments (71/400) lo0605 hi0605 accepted0605
def lo0606b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨44,by decide⟩
def lo0606b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨45,by decide⟩
def lo0606 : CheckedMoment :=
  CheckedMoment.ofBessel lo0606b1 lo0606b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0606b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨49,by decide⟩
def hi0606b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨50,by decide⟩
def hi0606 : CheckedMoment :=
  CheckedMoment.ofBessel hi0606b1 hi0606b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0606 : meanBracketCheck (1777/10000) lo0606 hi0606=true := by decide +kernel
def bracket0606 : MeanBracket := meanBracketOfMoments (1777/10000) lo0606 hi0606 accepted0606
def lo0607b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨54,by decide⟩
def lo0607b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨55,by decide⟩
def lo0607 : CheckedMoment :=
  CheckedMoment.ofBessel lo0607b1 lo0607b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0607b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨59,by decide⟩
def hi0607b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0094.rows BesselBatch0094.accepted ⟨60,by decide⟩
def hi0607 : CheckedMoment :=
  CheckedMoment.ofBessel hi0607b1 hi0607b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0607 : meanBracketCheck (1779/10000) lo0607 hi0607=true := by decide +kernel
def bracket0607 : MeanBracket := meanBracketOfMoments (1779/10000) lo0607 hi0607 accepted0607
#print axioms bracket0592
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0037
