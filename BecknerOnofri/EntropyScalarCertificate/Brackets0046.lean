import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0115
import BecknerOnofri.EntropyScalarCertificate.Bessel0116
import BecknerOnofri.EntropyScalarCertificate.Bessel0117
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0046
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0736b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨0,by decide⟩
def lo0736b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨1,by decide⟩
def lo0736 : CheckedMoment :=
  CheckedMoment.ofBessel lo0736b1 lo0736b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0736b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨5,by decide⟩
def hi0736b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨6,by decide⟩
def hi0736 : CheckedMoment :=
  CheckedMoment.ofBessel hi0736b1 hi0736b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0736 : meanBracketCheck (109/500) lo0736 hi0736=true := by decide +kernel
def bracket0736 : MeanBracket := meanBracketOfMoments (109/500) lo0736 hi0736 accepted0736
def lo0737b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨10,by decide⟩
def lo0737b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨11,by decide⟩
def lo0737 : CheckedMoment :=
  CheckedMoment.ofBessel lo0737b1 lo0737b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0737b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨15,by decide⟩
def hi0737b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨16,by decide⟩
def hi0737 : CheckedMoment :=
  CheckedMoment.ofBessel hi0737b1 hi0737b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0737 : meanBracketCheck (219/1000) lo0737 hi0737=true := by decide +kernel
def bracket0737 : MeanBracket := meanBracketOfMoments (219/1000) lo0737 hi0737 accepted0737
def lo0738b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨20,by decide⟩
def lo0738b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨21,by decide⟩
def lo0738 : CheckedMoment :=
  CheckedMoment.ofBessel lo0738b1 lo0738b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0738b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨25,by decide⟩
def hi0738b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨26,by decide⟩
def hi0738 : CheckedMoment :=
  CheckedMoment.ofBessel hi0738b1 hi0738b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0738 : meanBracketCheck (11/50) lo0738 hi0738=true := by decide +kernel
def bracket0738 : MeanBracket := meanBracketOfMoments (11/50) lo0738 hi0738 accepted0738
def lo0739b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨30,by decide⟩
def lo0739b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨31,by decide⟩
def lo0739 : CheckedMoment :=
  CheckedMoment.ofBessel lo0739b1 lo0739b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0739b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨35,by decide⟩
def hi0739b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨36,by decide⟩
def hi0739 : CheckedMoment :=
  CheckedMoment.ofBessel hi0739b1 hi0739b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0739 : meanBracketCheck (221/1000) lo0739 hi0739=true := by decide +kernel
def bracket0739 : MeanBracket := meanBracketOfMoments (221/1000) lo0739 hi0739 accepted0739
def lo0740b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨40,by decide⟩
def lo0740b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨41,by decide⟩
def lo0740 : CheckedMoment :=
  CheckedMoment.ofBessel lo0740b1 lo0740b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0740b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨45,by decide⟩
def hi0740b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨46,by decide⟩
def hi0740 : CheckedMoment :=
  CheckedMoment.ofBessel hi0740b1 hi0740b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0740 : meanBracketCheck (111/500) lo0740 hi0740=true := by decide +kernel
def bracket0740 : MeanBracket := meanBracketOfMoments (111/500) lo0740 hi0740 accepted0740
def lo0741b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨50,by decide⟩
def lo0741b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨51,by decide⟩
def lo0741 : CheckedMoment :=
  CheckedMoment.ofBessel lo0741b1 lo0741b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0741b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨55,by decide⟩
def hi0741b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨56,by decide⟩
def hi0741 : CheckedMoment :=
  CheckedMoment.ofBessel hi0741b1 hi0741b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0741 : meanBracketCheck (223/1000) lo0741 hi0741=true := by decide +kernel
def bracket0741 : MeanBracket := meanBracketOfMoments (223/1000) lo0741 hi0741 accepted0741
def lo0742b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨60,by decide⟩
def lo0742b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨61,by decide⟩
def lo0742 : CheckedMoment :=
  CheckedMoment.ofBessel lo0742b1 lo0742b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0742b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨1,by decide⟩
def hi0742b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨2,by decide⟩
def hi0742 : CheckedMoment :=
  CheckedMoment.ofBessel hi0742b1 hi0742b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0742 : meanBracketCheck (28/125) lo0742 hi0742=true := by decide +kernel
def bracket0742 : MeanBracket := meanBracketOfMoments (28/125) lo0742 hi0742 accepted0742
def lo0743b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨6,by decide⟩
def lo0743b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨7,by decide⟩
def lo0743 : CheckedMoment :=
  CheckedMoment.ofBessel lo0743b1 lo0743b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0743b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨11,by decide⟩
def hi0743b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨12,by decide⟩
def hi0743 : CheckedMoment :=
  CheckedMoment.ofBessel hi0743b1 hi0743b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0743 : meanBracketCheck (9/40) lo0743 hi0743=true := by decide +kernel
def bracket0743 : MeanBracket := meanBracketOfMoments (9/40) lo0743 hi0743 accepted0743
def lo0744b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨16,by decide⟩
def lo0744b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨17,by decide⟩
def lo0744 : CheckedMoment :=
  CheckedMoment.ofBessel lo0744b1 lo0744b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0744b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨21,by decide⟩
def hi0744b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨22,by decide⟩
def hi0744 : CheckedMoment :=
  CheckedMoment.ofBessel hi0744b1 hi0744b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0744 : meanBracketCheck (113/500) lo0744 hi0744=true := by decide +kernel
def bracket0744 : MeanBracket := meanBracketOfMoments (113/500) lo0744 hi0744 accepted0744
def lo0745b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨26,by decide⟩
def lo0745b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨27,by decide⟩
def lo0745 : CheckedMoment :=
  CheckedMoment.ofBessel lo0745b1 lo0745b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0745b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨31,by decide⟩
def hi0745b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨32,by decide⟩
def hi0745 : CheckedMoment :=
  CheckedMoment.ofBessel hi0745b1 hi0745b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0745 : meanBracketCheck (227/1000) lo0745 hi0745=true := by decide +kernel
def bracket0745 : MeanBracket := meanBracketOfMoments (227/1000) lo0745 hi0745 accepted0745
def lo0746b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨36,by decide⟩
def lo0746b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨37,by decide⟩
def lo0746 : CheckedMoment :=
  CheckedMoment.ofBessel lo0746b1 lo0746b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0746b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨41,by decide⟩
def hi0746b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨42,by decide⟩
def hi0746 : CheckedMoment :=
  CheckedMoment.ofBessel hi0746b1 hi0746b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0746 : meanBracketCheck (57/250) lo0746 hi0746=true := by decide +kernel
def bracket0746 : MeanBracket := meanBracketOfMoments (57/250) lo0746 hi0746 accepted0746
def lo0747b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨46,by decide⟩
def lo0747b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨47,by decide⟩
def lo0747 : CheckedMoment :=
  CheckedMoment.ofBessel lo0747b1 lo0747b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0747b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨51,by decide⟩
def hi0747b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨52,by decide⟩
def hi0747 : CheckedMoment :=
  CheckedMoment.ofBessel hi0747b1 hi0747b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0747 : meanBracketCheck (229/1000) lo0747 hi0747=true := by decide +kernel
def bracket0747 : MeanBracket := meanBracketOfMoments (229/1000) lo0747 hi0747 accepted0747
def lo0748b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨56,by decide⟩
def lo0748b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨57,by decide⟩
def lo0748 : CheckedMoment :=
  CheckedMoment.ofBessel lo0748b1 lo0748b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0748b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨61,by decide⟩
def hi0748b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0116.rows BesselBatch0116.accepted ⟨62,by decide⟩
def hi0748 : CheckedMoment :=
  CheckedMoment.ofBessel hi0748b1 hi0748b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0748 : meanBracketCheck (23/100) lo0748 hi0748=true := by decide +kernel
def bracket0748 : MeanBracket := meanBracketOfMoments (23/100) lo0748 hi0748 accepted0748
def lo0749b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨2,by decide⟩
def lo0749b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨3,by decide⟩
def lo0749 : CheckedMoment :=
  CheckedMoment.ofBessel lo0749b1 lo0749b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0749b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨7,by decide⟩
def hi0749b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨8,by decide⟩
def hi0749 : CheckedMoment :=
  CheckedMoment.ofBessel hi0749b1 hi0749b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0749 : meanBracketCheck (231/1000) lo0749 hi0749=true := by decide +kernel
def bracket0749 : MeanBracket := meanBracketOfMoments (231/1000) lo0749 hi0749 accepted0749
def lo0750b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨12,by decide⟩
def lo0750b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨13,by decide⟩
def lo0750 : CheckedMoment :=
  CheckedMoment.ofBessel lo0750b1 lo0750b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0750b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨17,by decide⟩
def hi0750b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨18,by decide⟩
def hi0750 : CheckedMoment :=
  CheckedMoment.ofBessel hi0750b1 hi0750b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0750 : meanBracketCheck (29/125) lo0750 hi0750=true := by decide +kernel
def bracket0750 : MeanBracket := meanBracketOfMoments (29/125) lo0750 hi0750 accepted0750
def lo0751b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨22,by decide⟩
def lo0751b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨23,by decide⟩
def lo0751 : CheckedMoment :=
  CheckedMoment.ofBessel lo0751b1 lo0751b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0751b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨27,by decide⟩
def hi0751b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨28,by decide⟩
def hi0751 : CheckedMoment :=
  CheckedMoment.ofBessel hi0751b1 hi0751b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0751 : meanBracketCheck (233/1000) lo0751 hi0751=true := by decide +kernel
def bracket0751 : MeanBracket := meanBracketOfMoments (233/1000) lo0751 hi0751 accepted0751
#print axioms bracket0736
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0046
