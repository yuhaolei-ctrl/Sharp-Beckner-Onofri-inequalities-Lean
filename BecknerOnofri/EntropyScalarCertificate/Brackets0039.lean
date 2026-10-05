import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0097
import BecknerOnofri.EntropyScalarCertificate.Bessel0098
import BecknerOnofri.EntropyScalarCertificate.Bessel0099
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0039
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0624b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨32,by decide⟩
def lo0624b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨33,by decide⟩
def lo0624 : CheckedMoment :=
  CheckedMoment.ofBessel lo0624b1 lo0624b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0624b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨37,by decide⟩
def hi0624b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨38,by decide⟩
def hi0624 : CheckedMoment :=
  CheckedMoment.ofBessel hi0624b1 hi0624b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0624 : meanBracketCheck (1813/10000) lo0624 hi0624=true := by decide +kernel
def bracket0624 : MeanBracket := meanBracketOfMoments (1813/10000) lo0624 hi0624 accepted0624
def lo0625b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨42,by decide⟩
def lo0625b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨43,by decide⟩
def lo0625 : CheckedMoment :=
  CheckedMoment.ofBessel lo0625b1 lo0625b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0625b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨47,by decide⟩
def hi0625b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨48,by decide⟩
def hi0625 : CheckedMoment :=
  CheckedMoment.ofBessel hi0625b1 hi0625b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0625 : meanBracketCheck (363/2000) lo0625 hi0625=true := by decide +kernel
def bracket0625 : MeanBracket := meanBracketOfMoments (363/2000) lo0625 hi0625 accepted0625
def lo0626b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨52,by decide⟩
def lo0626b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨53,by decide⟩
def lo0626 : CheckedMoment :=
  CheckedMoment.ofBessel lo0626b1 lo0626b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0626b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨57,by decide⟩
def hi0626b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨58,by decide⟩
def hi0626 : CheckedMoment :=
  CheckedMoment.ofBessel hi0626b1 hi0626b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0626 : meanBracketCheck (1817/10000) lo0626 hi0626=true := by decide +kernel
def bracket0626 : MeanBracket := meanBracketOfMoments (1817/10000) lo0626 hi0626 accepted0626
def lo0627b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨62,by decide⟩
def lo0627b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨63,by decide⟩
def lo0627 : CheckedMoment :=
  CheckedMoment.ofBessel lo0627b1 lo0627b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0627b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨3,by decide⟩
def hi0627b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨4,by decide⟩
def hi0627 : CheckedMoment :=
  CheckedMoment.ofBessel hi0627b1 hi0627b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0627 : meanBracketCheck (1819/10000) lo0627 hi0627=true := by decide +kernel
def bracket0627 : MeanBracket := meanBracketOfMoments (1819/10000) lo0627 hi0627 accepted0627
def lo0628b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨8,by decide⟩
def lo0628b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨9,by decide⟩
def lo0628 : CheckedMoment :=
  CheckedMoment.ofBessel lo0628b1 lo0628b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0628b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨13,by decide⟩
def hi0628b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨14,by decide⟩
def hi0628 : CheckedMoment :=
  CheckedMoment.ofBessel hi0628b1 hi0628b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0628 : meanBracketCheck (1821/10000) lo0628 hi0628=true := by decide +kernel
def bracket0628 : MeanBracket := meanBracketOfMoments (1821/10000) lo0628 hi0628 accepted0628
def lo0629b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨18,by decide⟩
def lo0629b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨19,by decide⟩
def lo0629 : CheckedMoment :=
  CheckedMoment.ofBessel lo0629b1 lo0629b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0629b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨23,by decide⟩
def hi0629b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨24,by decide⟩
def hi0629 : CheckedMoment :=
  CheckedMoment.ofBessel hi0629b1 hi0629b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0629 : meanBracketCheck (1823/10000) lo0629 hi0629=true := by decide +kernel
def bracket0629 : MeanBracket := meanBracketOfMoments (1823/10000) lo0629 hi0629 accepted0629
def lo0630b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨28,by decide⟩
def lo0630b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨29,by decide⟩
def lo0630 : CheckedMoment :=
  CheckedMoment.ofBessel lo0630b1 lo0630b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0630b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨33,by decide⟩
def hi0630b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨34,by decide⟩
def hi0630 : CheckedMoment :=
  CheckedMoment.ofBessel hi0630b1 hi0630b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0630 : meanBracketCheck (73/400) lo0630 hi0630=true := by decide +kernel
def bracket0630 : MeanBracket := meanBracketOfMoments (73/400) lo0630 hi0630 accepted0630
def lo0631b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨38,by decide⟩
def lo0631b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨39,by decide⟩
def lo0631 : CheckedMoment :=
  CheckedMoment.ofBessel lo0631b1 lo0631b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0631b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨43,by decide⟩
def hi0631b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨44,by decide⟩
def hi0631 : CheckedMoment :=
  CheckedMoment.ofBessel hi0631b1 hi0631b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0631 : meanBracketCheck (1827/10000) lo0631 hi0631=true := by decide +kernel
def bracket0631 : MeanBracket := meanBracketOfMoments (1827/10000) lo0631 hi0631 accepted0631
def lo0632b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨48,by decide⟩
def lo0632b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨49,by decide⟩
def lo0632 : CheckedMoment :=
  CheckedMoment.ofBessel lo0632b1 lo0632b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0632b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨53,by decide⟩
def hi0632b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨54,by decide⟩
def hi0632 : CheckedMoment :=
  CheckedMoment.ofBessel hi0632b1 hi0632b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0632 : meanBracketCheck (1829/10000) lo0632 hi0632=true := by decide +kernel
def bracket0632 : MeanBracket := meanBracketOfMoments (1829/10000) lo0632 hi0632 accepted0632
def lo0633b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨58,by decide⟩
def lo0633b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨59,by decide⟩
def lo0633 : CheckedMoment :=
  CheckedMoment.ofBessel lo0633b1 lo0633b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0633b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨63,by decide⟩
def hi0633b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨0,by decide⟩
def hi0633 : CheckedMoment :=
  CheckedMoment.ofBessel hi0633b1 hi0633b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0633 : meanBracketCheck (1831/10000) lo0633 hi0633=true := by decide +kernel
def bracket0633 : MeanBracket := meanBracketOfMoments (1831/10000) lo0633 hi0633 accepted0633
def lo0634b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨4,by decide⟩
def lo0634b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨5,by decide⟩
def lo0634 : CheckedMoment :=
  CheckedMoment.ofBessel lo0634b1 lo0634b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0634b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨9,by decide⟩
def hi0634b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨10,by decide⟩
def hi0634 : CheckedMoment :=
  CheckedMoment.ofBessel hi0634b1 hi0634b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0634 : meanBracketCheck (1833/10000) lo0634 hi0634=true := by decide +kernel
def bracket0634 : MeanBracket := meanBracketOfMoments (1833/10000) lo0634 hi0634 accepted0634
def lo0635b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨14,by decide⟩
def lo0635b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨15,by decide⟩
def lo0635 : CheckedMoment :=
  CheckedMoment.ofBessel lo0635b1 lo0635b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0635b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨19,by decide⟩
def hi0635b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨20,by decide⟩
def hi0635 : CheckedMoment :=
  CheckedMoment.ofBessel hi0635b1 hi0635b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0635 : meanBracketCheck (367/2000) lo0635 hi0635=true := by decide +kernel
def bracket0635 : MeanBracket := meanBracketOfMoments (367/2000) lo0635 hi0635 accepted0635
def lo0636b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨24,by decide⟩
def lo0636b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨25,by decide⟩
def lo0636 : CheckedMoment :=
  CheckedMoment.ofBessel lo0636b1 lo0636b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0636b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨29,by decide⟩
def hi0636b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨30,by decide⟩
def hi0636 : CheckedMoment :=
  CheckedMoment.ofBessel hi0636b1 hi0636b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0636 : meanBracketCheck (1837/10000) lo0636 hi0636=true := by decide +kernel
def bracket0636 : MeanBracket := meanBracketOfMoments (1837/10000) lo0636 hi0636 accepted0636
def lo0637b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨34,by decide⟩
def lo0637b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨35,by decide⟩
def lo0637 : CheckedMoment :=
  CheckedMoment.ofBessel lo0637b1 lo0637b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0637b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨39,by decide⟩
def hi0637b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨40,by decide⟩
def hi0637 : CheckedMoment :=
  CheckedMoment.ofBessel hi0637b1 hi0637b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0637 : meanBracketCheck (1839/10000) lo0637 hi0637=true := by decide +kernel
def bracket0637 : MeanBracket := meanBracketOfMoments (1839/10000) lo0637 hi0637 accepted0637
def lo0638b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨44,by decide⟩
def lo0638b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨45,by decide⟩
def lo0638 : CheckedMoment :=
  CheckedMoment.ofBessel lo0638b1 lo0638b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0638b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨49,by decide⟩
def hi0638b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨50,by decide⟩
def hi0638 : CheckedMoment :=
  CheckedMoment.ofBessel hi0638b1 hi0638b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0638 : meanBracketCheck (1841/10000) lo0638 hi0638=true := by decide +kernel
def bracket0638 : MeanBracket := meanBracketOfMoments (1841/10000) lo0638 hi0638 accepted0638
def lo0639b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨54,by decide⟩
def lo0639b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨55,by decide⟩
def lo0639 : CheckedMoment :=
  CheckedMoment.ofBessel lo0639b1 lo0639b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0639b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨59,by decide⟩
def hi0639b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨60,by decide⟩
def hi0639 : CheckedMoment :=
  CheckedMoment.ofBessel hi0639b1 hi0639b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0639 : meanBracketCheck (1843/10000) lo0639 hi0639=true := by decide +kernel
def bracket0639 : MeanBracket := meanBracketOfMoments (1843/10000) lo0639 hi0639 accepted0639
#print axioms bracket0624
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0039
