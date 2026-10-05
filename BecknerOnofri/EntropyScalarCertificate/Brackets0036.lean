module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0090
public import BecknerOnofri.EntropyScalarCertificate.Bessel0091
public import BecknerOnofri.EntropyScalarCertificate.Bessel0092

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0036
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0576b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨0,by decide⟩
def lo0576b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨1,by decide⟩
def lo0576 : CheckedMoment :=
  CheckedMoment.ofBessel lo0576b1 lo0576b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0576b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨5,by decide⟩
def hi0576b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨6,by decide⟩
def hi0576 : CheckedMoment :=
  CheckedMoment.ofBessel hi0576b1 hi0576b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0576 : meanBracketCheck (1717/10000) lo0576 hi0576=true := by decide +kernel
def bracket0576 : MeanBracket := meanBracketOfMoments (1717/10000) lo0576 hi0576 accepted0576
def lo0577b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨10,by decide⟩
def lo0577b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨11,by decide⟩
def lo0577 : CheckedMoment :=
  CheckedMoment.ofBessel lo0577b1 lo0577b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0577b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨15,by decide⟩
def hi0577b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨16,by decide⟩
def hi0577 : CheckedMoment :=
  CheckedMoment.ofBessel hi0577b1 hi0577b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0577 : meanBracketCheck (1719/10000) lo0577 hi0577=true := by decide +kernel
def bracket0577 : MeanBracket := meanBracketOfMoments (1719/10000) lo0577 hi0577 accepted0577
def lo0578b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨20,by decide⟩
def lo0578b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨21,by decide⟩
def lo0578 : CheckedMoment :=
  CheckedMoment.ofBessel lo0578b1 lo0578b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0578b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨25,by decide⟩
def hi0578b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨26,by decide⟩
def hi0578 : CheckedMoment :=
  CheckedMoment.ofBessel hi0578b1 hi0578b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0578 : meanBracketCheck (1721/10000) lo0578 hi0578=true := by decide +kernel
def bracket0578 : MeanBracket := meanBracketOfMoments (1721/10000) lo0578 hi0578 accepted0578
def lo0579b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨30,by decide⟩
def lo0579b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨31,by decide⟩
def lo0579 : CheckedMoment :=
  CheckedMoment.ofBessel lo0579b1 lo0579b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0579b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨35,by decide⟩
def hi0579b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨36,by decide⟩
def hi0579 : CheckedMoment :=
  CheckedMoment.ofBessel hi0579b1 hi0579b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0579 : meanBracketCheck (1723/10000) lo0579 hi0579=true := by decide +kernel
def bracket0579 : MeanBracket := meanBracketOfMoments (1723/10000) lo0579 hi0579 accepted0579
def lo0580b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨40,by decide⟩
def lo0580b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨41,by decide⟩
def lo0580 : CheckedMoment :=
  CheckedMoment.ofBessel lo0580b1 lo0580b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0580b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨45,by decide⟩
def hi0580b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨46,by decide⟩
def hi0580 : CheckedMoment :=
  CheckedMoment.ofBessel hi0580b1 hi0580b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0580 : meanBracketCheck (69/400) lo0580 hi0580=true := by decide +kernel
def bracket0580 : MeanBracket := meanBracketOfMoments (69/400) lo0580 hi0580 accepted0580
def lo0581b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨50,by decide⟩
def lo0581b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨51,by decide⟩
def lo0581 : CheckedMoment :=
  CheckedMoment.ofBessel lo0581b1 lo0581b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0581b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨55,by decide⟩
def hi0581b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨56,by decide⟩
def hi0581 : CheckedMoment :=
  CheckedMoment.ofBessel hi0581b1 hi0581b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0581 : meanBracketCheck (1727/10000) lo0581 hi0581=true := by decide +kernel
def bracket0581 : MeanBracket := meanBracketOfMoments (1727/10000) lo0581 hi0581 accepted0581
def lo0582b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨60,by decide⟩
def lo0582b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨61,by decide⟩
def lo0582 : CheckedMoment :=
  CheckedMoment.ofBessel lo0582b1 lo0582b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0582b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨1,by decide⟩
def hi0582b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨2,by decide⟩
def hi0582 : CheckedMoment :=
  CheckedMoment.ofBessel hi0582b1 hi0582b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0582 : meanBracketCheck (1729/10000) lo0582 hi0582=true := by decide +kernel
def bracket0582 : MeanBracket := meanBracketOfMoments (1729/10000) lo0582 hi0582 accepted0582
def lo0583b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨6,by decide⟩
def lo0583b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨7,by decide⟩
def lo0583 : CheckedMoment :=
  CheckedMoment.ofBessel lo0583b1 lo0583b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0583b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨11,by decide⟩
def hi0583b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨12,by decide⟩
def hi0583 : CheckedMoment :=
  CheckedMoment.ofBessel hi0583b1 hi0583b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0583 : meanBracketCheck (1731/10000) lo0583 hi0583=true := by decide +kernel
def bracket0583 : MeanBracket := meanBracketOfMoments (1731/10000) lo0583 hi0583 accepted0583
def lo0584b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨16,by decide⟩
def lo0584b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨17,by decide⟩
def lo0584 : CheckedMoment :=
  CheckedMoment.ofBessel lo0584b1 lo0584b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0584b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨21,by decide⟩
def hi0584b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨22,by decide⟩
def hi0584 : CheckedMoment :=
  CheckedMoment.ofBessel hi0584b1 hi0584b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0584 : meanBracketCheck (1733/10000) lo0584 hi0584=true := by decide +kernel
def bracket0584 : MeanBracket := meanBracketOfMoments (1733/10000) lo0584 hi0584 accepted0584
def lo0585b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨26,by decide⟩
def lo0585b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨27,by decide⟩
def lo0585 : CheckedMoment :=
  CheckedMoment.ofBessel lo0585b1 lo0585b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0585b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨31,by decide⟩
def hi0585b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨32,by decide⟩
def hi0585 : CheckedMoment :=
  CheckedMoment.ofBessel hi0585b1 hi0585b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0585 : meanBracketCheck (347/2000) lo0585 hi0585=true := by decide +kernel
def bracket0585 : MeanBracket := meanBracketOfMoments (347/2000) lo0585 hi0585 accepted0585
def lo0586b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨36,by decide⟩
def lo0586b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨37,by decide⟩
def lo0586 : CheckedMoment :=
  CheckedMoment.ofBessel lo0586b1 lo0586b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0586b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨41,by decide⟩
def hi0586b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨42,by decide⟩
def hi0586 : CheckedMoment :=
  CheckedMoment.ofBessel hi0586b1 hi0586b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0586 : meanBracketCheck (1737/10000) lo0586 hi0586=true := by decide +kernel
def bracket0586 : MeanBracket := meanBracketOfMoments (1737/10000) lo0586 hi0586 accepted0586
def lo0587b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨46,by decide⟩
def lo0587b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨47,by decide⟩
def lo0587 : CheckedMoment :=
  CheckedMoment.ofBessel lo0587b1 lo0587b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0587b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨51,by decide⟩
def hi0587b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨52,by decide⟩
def hi0587 : CheckedMoment :=
  CheckedMoment.ofBessel hi0587b1 hi0587b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0587 : meanBracketCheck (1739/10000) lo0587 hi0587=true := by decide +kernel
def bracket0587 : MeanBracket := meanBracketOfMoments (1739/10000) lo0587 hi0587 accepted0587
def lo0588b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨56,by decide⟩
def lo0588b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨57,by decide⟩
def lo0588 : CheckedMoment :=
  CheckedMoment.ofBessel lo0588b1 lo0588b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0588b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨61,by decide⟩
def hi0588b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨62,by decide⟩
def hi0588 : CheckedMoment :=
  CheckedMoment.ofBessel hi0588b1 hi0588b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0588 : meanBracketCheck (1741/10000) lo0588 hi0588=true := by decide +kernel
def bracket0588 : MeanBracket := meanBracketOfMoments (1741/10000) lo0588 hi0588 accepted0588
def lo0589b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨2,by decide⟩
def lo0589b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨3,by decide⟩
def lo0589 : CheckedMoment :=
  CheckedMoment.ofBessel lo0589b1 lo0589b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0589b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨7,by decide⟩
def hi0589b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨8,by decide⟩
def hi0589 : CheckedMoment :=
  CheckedMoment.ofBessel hi0589b1 hi0589b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0589 : meanBracketCheck (1743/10000) lo0589 hi0589=true := by decide +kernel
def bracket0589 : MeanBracket := meanBracketOfMoments (1743/10000) lo0589 hi0589 accepted0589
def lo0590b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨12,by decide⟩
def lo0590b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨13,by decide⟩
def lo0590 : CheckedMoment :=
  CheckedMoment.ofBessel lo0590b1 lo0590b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0590b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨17,by decide⟩
def hi0590b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨18,by decide⟩
def hi0590 : CheckedMoment :=
  CheckedMoment.ofBessel hi0590b1 hi0590b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0590 : meanBracketCheck (349/2000) lo0590 hi0590=true := by decide +kernel
def bracket0590 : MeanBracket := meanBracketOfMoments (349/2000) lo0590 hi0590 accepted0590
def lo0591b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨22,by decide⟩
def lo0591b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨23,by decide⟩
def lo0591 : CheckedMoment :=
  CheckedMoment.ofBessel lo0591b1 lo0591b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0591b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨27,by decide⟩
def hi0591b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨28,by decide⟩
def hi0591 : CheckedMoment :=
  CheckedMoment.ofBessel hi0591b1 hi0591b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0591 : meanBracketCheck (1747/10000) lo0591 hi0591=true := by decide +kernel
def bracket0591 : MeanBracket := meanBracketOfMoments (1747/10000) lo0591 hi0591 accepted0591
#print axioms bracket0576
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0036
