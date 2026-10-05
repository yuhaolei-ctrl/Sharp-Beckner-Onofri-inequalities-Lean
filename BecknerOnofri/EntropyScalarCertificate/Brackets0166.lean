import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0415
import BecknerOnofri.EntropyScalarCertificate.Bessel0416
import BecknerOnofri.EntropyScalarCertificate.Bessel0417
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0166
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2656b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨0,by decide⟩
def lo2656b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨1,by decide⟩
def lo2656 : CheckedMoment :=
  CheckedMoment.ofBessel lo2656b1 lo2656b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2656b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨5,by decide⟩
def hi2656b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨6,by decide⟩
def hi2656 : CheckedMoment :=
  CheckedMoment.ofBessel hi2656b1 hi2656b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2656 : meanBracketCheck (24889/25000) lo2656 hi2656=true := by decide +kernel
def bracket2656 : MeanBracket := meanBracketOfMoments (24889/25000) lo2656 hi2656 accepted2656
def lo2657b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨10,by decide⟩
def lo2657b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨11,by decide⟩
def lo2657 : CheckedMoment :=
  CheckedMoment.ofBessel lo2657b1 lo2657b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2657b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨15,by decide⟩
def hi2657b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨16,by decide⟩
def hi2657 : CheckedMoment :=
  CheckedMoment.ofBessel hi2657b1 hi2657b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2657 : meanBracketCheck (49779/50000) lo2657 hi2657=true := by decide +kernel
def bracket2657 : MeanBracket := meanBracketOfMoments (49779/50000) lo2657 hi2657 accepted2657
def lo2658b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨20,by decide⟩
def lo2658b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨21,by decide⟩
def lo2658 : CheckedMoment :=
  CheckedMoment.ofBessel lo2658b1 lo2658b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2658b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨25,by decide⟩
def hi2658b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨26,by decide⟩
def hi2658 : CheckedMoment :=
  CheckedMoment.ofBessel hi2658b1 hi2658b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2658 : meanBracketCheck (2489/2500) lo2658 hi2658=true := by decide +kernel
def bracket2658 : MeanBracket := meanBracketOfMoments (2489/2500) lo2658 hi2658 accepted2658
def lo2659b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨30,by decide⟩
def lo2659b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨31,by decide⟩
def lo2659 : CheckedMoment :=
  CheckedMoment.ofBessel lo2659b1 lo2659b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2659b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨35,by decide⟩
def hi2659b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨36,by decide⟩
def hi2659 : CheckedMoment :=
  CheckedMoment.ofBessel hi2659b1 hi2659b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2659 : meanBracketCheck (49781/50000) lo2659 hi2659=true := by decide +kernel
def bracket2659 : MeanBracket := meanBracketOfMoments (49781/50000) lo2659 hi2659 accepted2659
def lo2660b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨40,by decide⟩
def lo2660b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨41,by decide⟩
def lo2660 : CheckedMoment :=
  CheckedMoment.ofBessel lo2660b1 lo2660b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2660b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨45,by decide⟩
def hi2660b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨46,by decide⟩
def hi2660 : CheckedMoment :=
  CheckedMoment.ofBessel hi2660b1 hi2660b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2660 : meanBracketCheck (24891/25000) lo2660 hi2660=true := by decide +kernel
def bracket2660 : MeanBracket := meanBracketOfMoments (24891/25000) lo2660 hi2660 accepted2660
def lo2661b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨50,by decide⟩
def lo2661b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨51,by decide⟩
def lo2661 : CheckedMoment :=
  CheckedMoment.ofBessel lo2661b1 lo2661b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2661b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨55,by decide⟩
def hi2661b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨56,by decide⟩
def hi2661 : CheckedMoment :=
  CheckedMoment.ofBessel hi2661b1 hi2661b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2661 : meanBracketCheck (49783/50000) lo2661 hi2661=true := by decide +kernel
def bracket2661 : MeanBracket := meanBracketOfMoments (49783/50000) lo2661 hi2661 accepted2661
def lo2662b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨60,by decide⟩
def lo2662b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨61,by decide⟩
def lo2662 : CheckedMoment :=
  CheckedMoment.ofBessel lo2662b1 lo2662b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2662b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨1,by decide⟩
def hi2662b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨2,by decide⟩
def hi2662 : CheckedMoment :=
  CheckedMoment.ofBessel hi2662b1 hi2662b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2662 : meanBracketCheck (6223/6250) lo2662 hi2662=true := by decide +kernel
def bracket2662 : MeanBracket := meanBracketOfMoments (6223/6250) lo2662 hi2662 accepted2662
def lo2663b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨6,by decide⟩
def lo2663b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨7,by decide⟩
def lo2663 : CheckedMoment :=
  CheckedMoment.ofBessel lo2663b1 lo2663b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2663b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨11,by decide⟩
def hi2663b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨12,by decide⟩
def hi2663 : CheckedMoment :=
  CheckedMoment.ofBessel hi2663b1 hi2663b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2663 : meanBracketCheck (9957/10000) lo2663 hi2663=true := by decide +kernel
def bracket2663 : MeanBracket := meanBracketOfMoments (9957/10000) lo2663 hi2663 accepted2663
def lo2664b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨16,by decide⟩
def lo2664b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨17,by decide⟩
def lo2664 : CheckedMoment :=
  CheckedMoment.ofBessel lo2664b1 lo2664b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2664b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨21,by decide⟩
def hi2664b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨22,by decide⟩
def hi2664 : CheckedMoment :=
  CheckedMoment.ofBessel hi2664b1 hi2664b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2664 : meanBracketCheck (24893/25000) lo2664 hi2664=true := by decide +kernel
def bracket2664 : MeanBracket := meanBracketOfMoments (24893/25000) lo2664 hi2664 accepted2664
def lo2665b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨26,by decide⟩
def lo2665b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨27,by decide⟩
def lo2665 : CheckedMoment :=
  CheckedMoment.ofBessel lo2665b1 lo2665b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2665b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨31,by decide⟩
def hi2665b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨32,by decide⟩
def hi2665 : CheckedMoment :=
  CheckedMoment.ofBessel hi2665b1 hi2665b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2665 : meanBracketCheck (49787/50000) lo2665 hi2665=true := by decide +kernel
def bracket2665 : MeanBracket := meanBracketOfMoments (49787/50000) lo2665 hi2665 accepted2665
def lo2666b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨36,by decide⟩
def lo2666b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨37,by decide⟩
def lo2666 : CheckedMoment :=
  CheckedMoment.ofBessel lo2666b1 lo2666b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2666b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨41,by decide⟩
def hi2666b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨42,by decide⟩
def hi2666 : CheckedMoment :=
  CheckedMoment.ofBessel hi2666b1 hi2666b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2666 : meanBracketCheck (12447/12500) lo2666 hi2666=true := by decide +kernel
def bracket2666 : MeanBracket := meanBracketOfMoments (12447/12500) lo2666 hi2666 accepted2666
def lo2667b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨46,by decide⟩
def lo2667b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨47,by decide⟩
def lo2667 : CheckedMoment :=
  CheckedMoment.ofBessel lo2667b1 lo2667b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2667b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨51,by decide⟩
def hi2667b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨52,by decide⟩
def hi2667 : CheckedMoment :=
  CheckedMoment.ofBessel hi2667b1 hi2667b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2667 : meanBracketCheck (49789/50000) lo2667 hi2667=true := by decide +kernel
def bracket2667 : MeanBracket := meanBracketOfMoments (49789/50000) lo2667 hi2667 accepted2667
def lo2668b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨56,by decide⟩
def lo2668b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨57,by decide⟩
def lo2668 : CheckedMoment :=
  CheckedMoment.ofBessel lo2668b1 lo2668b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2668b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨61,by decide⟩
def hi2668b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨62,by decide⟩
def hi2668 : CheckedMoment :=
  CheckedMoment.ofBessel hi2668b1 hi2668b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2668 : meanBracketCheck (4979/5000) lo2668 hi2668=true := by decide +kernel
def bracket2668 : MeanBracket := meanBracketOfMoments (4979/5000) lo2668 hi2668 accepted2668
def lo2669b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨2,by decide⟩
def lo2669b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨3,by decide⟩
def lo2669 : CheckedMoment :=
  CheckedMoment.ofBessel lo2669b1 lo2669b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2669b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨7,by decide⟩
def hi2669b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨8,by decide⟩
def hi2669 : CheckedMoment :=
  CheckedMoment.ofBessel hi2669b1 hi2669b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2669 : meanBracketCheck (49791/50000) lo2669 hi2669=true := by decide +kernel
def bracket2669 : MeanBracket := meanBracketOfMoments (49791/50000) lo2669 hi2669 accepted2669
def lo2670b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨12,by decide⟩
def lo2670b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨13,by decide⟩
def lo2670 : CheckedMoment :=
  CheckedMoment.ofBessel lo2670b1 lo2670b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2670b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨17,by decide⟩
def hi2670b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨18,by decide⟩
def hi2670 : CheckedMoment :=
  CheckedMoment.ofBessel hi2670b1 hi2670b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2670 : meanBracketCheck (3112/3125) lo2670 hi2670=true := by decide +kernel
def bracket2670 : MeanBracket := meanBracketOfMoments (3112/3125) lo2670 hi2670 accepted2670
def lo2671b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨22,by decide⟩
def lo2671b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨23,by decide⟩
def lo2671 : CheckedMoment :=
  CheckedMoment.ofBessel lo2671b1 lo2671b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2671b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨27,by decide⟩
def hi2671b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨28,by decide⟩
def hi2671 : CheckedMoment :=
  CheckedMoment.ofBessel hi2671b1 hi2671b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2671 : meanBracketCheck (49793/50000) lo2671 hi2671=true := by decide +kernel
def bracket2671 : MeanBracket := meanBracketOfMoments (49793/50000) lo2671 hi2671 accepted2671
#print axioms bracket2656
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0166
