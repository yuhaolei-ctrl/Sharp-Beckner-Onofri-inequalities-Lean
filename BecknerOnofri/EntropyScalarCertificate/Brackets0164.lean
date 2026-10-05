import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0410
import BecknerOnofri.EntropyScalarCertificate.Bessel0411
import BecknerOnofri.EntropyScalarCertificate.Bessel0412
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0164
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2624b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨0,by decide⟩
def lo2624b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨1,by decide⟩
def lo2624 : CheckedMoment :=
  CheckedMoment.ofBessel lo2624b1 lo2624b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2624b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨5,by decide⟩
def hi2624b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨6,by decide⟩
def hi2624 : CheckedMoment :=
  CheckedMoment.ofBessel hi2624b1 hi2624b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2624 : meanBracketCheck (24873/25000) lo2624 hi2624=true := by decide +kernel
def bracket2624 : MeanBracket := meanBracketOfMoments (24873/25000) lo2624 hi2624 accepted2624
def lo2625b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨10,by decide⟩
def lo2625b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨11,by decide⟩
def lo2625 : CheckedMoment :=
  CheckedMoment.ofBessel lo2625b1 lo2625b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2625b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨15,by decide⟩
def hi2625b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨16,by decide⟩
def hi2625 : CheckedMoment :=
  CheckedMoment.ofBessel hi2625b1 hi2625b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2625 : meanBracketCheck (49747/50000) lo2625 hi2625=true := by decide +kernel
def bracket2625 : MeanBracket := meanBracketOfMoments (49747/50000) lo2625 hi2625 accepted2625
def lo2626b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨20,by decide⟩
def lo2626b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨21,by decide⟩
def lo2626 : CheckedMoment :=
  CheckedMoment.ofBessel lo2626b1 lo2626b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2626b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨25,by decide⟩
def hi2626b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨26,by decide⟩
def hi2626 : CheckedMoment :=
  CheckedMoment.ofBessel hi2626b1 hi2626b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2626 : meanBracketCheck (12437/12500) lo2626 hi2626=true := by decide +kernel
def bracket2626 : MeanBracket := meanBracketOfMoments (12437/12500) lo2626 hi2626 accepted2626
def lo2627b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨30,by decide⟩
def lo2627b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨31,by decide⟩
def lo2627 : CheckedMoment :=
  CheckedMoment.ofBessel lo2627b1 lo2627b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2627b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨35,by decide⟩
def hi2627b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨36,by decide⟩
def hi2627 : CheckedMoment :=
  CheckedMoment.ofBessel hi2627b1 hi2627b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2627 : meanBracketCheck (49749/50000) lo2627 hi2627=true := by decide +kernel
def bracket2627 : MeanBracket := meanBracketOfMoments (49749/50000) lo2627 hi2627 accepted2627
def lo2628b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨40,by decide⟩
def lo2628b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨41,by decide⟩
def lo2628 : CheckedMoment :=
  CheckedMoment.ofBessel lo2628b1 lo2628b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2628b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨45,by decide⟩
def hi2628b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨46,by decide⟩
def hi2628 : CheckedMoment :=
  CheckedMoment.ofBessel hi2628b1 hi2628b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2628 : meanBracketCheck (199/200) lo2628 hi2628=true := by decide +kernel
def bracket2628 : MeanBracket := meanBracketOfMoments (199/200) lo2628 hi2628 accepted2628
def lo2629b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨50,by decide⟩
def lo2629b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨51,by decide⟩
def lo2629 : CheckedMoment :=
  CheckedMoment.ofBessel lo2629b1 lo2629b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2629b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨55,by decide⟩
def hi2629b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨56,by decide⟩
def hi2629 : CheckedMoment :=
  CheckedMoment.ofBessel hi2629b1 hi2629b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2629 : meanBracketCheck (49751/50000) lo2629 hi2629=true := by decide +kernel
def bracket2629 : MeanBracket := meanBracketOfMoments (49751/50000) lo2629 hi2629 accepted2629
def lo2630b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨60,by decide⟩
def lo2630b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨61,by decide⟩
def lo2630 : CheckedMoment :=
  CheckedMoment.ofBessel lo2630b1 lo2630b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2630b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨1,by decide⟩
def hi2630b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨2,by decide⟩
def hi2630 : CheckedMoment :=
  CheckedMoment.ofBessel hi2630b1 hi2630b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2630 : meanBracketCheck (6219/6250) lo2630 hi2630=true := by decide +kernel
def bracket2630 : MeanBracket := meanBracketOfMoments (6219/6250) lo2630 hi2630 accepted2630
def lo2631b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨6,by decide⟩
def lo2631b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨7,by decide⟩
def lo2631 : CheckedMoment :=
  CheckedMoment.ofBessel lo2631b1 lo2631b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2631b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨11,by decide⟩
def hi2631b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨12,by decide⟩
def hi2631 : CheckedMoment :=
  CheckedMoment.ofBessel hi2631b1 hi2631b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2631 : meanBracketCheck (49753/50000) lo2631 hi2631=true := by decide +kernel
def bracket2631 : MeanBracket := meanBracketOfMoments (49753/50000) lo2631 hi2631 accepted2631
def lo2632b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨16,by decide⟩
def lo2632b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨17,by decide⟩
def lo2632 : CheckedMoment :=
  CheckedMoment.ofBessel lo2632b1 lo2632b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2632b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨21,by decide⟩
def hi2632b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨22,by decide⟩
def hi2632 : CheckedMoment :=
  CheckedMoment.ofBessel hi2632b1 hi2632b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2632 : meanBracketCheck (24877/25000) lo2632 hi2632=true := by decide +kernel
def bracket2632 : MeanBracket := meanBracketOfMoments (24877/25000) lo2632 hi2632 accepted2632
def lo2633b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨26,by decide⟩
def lo2633b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨27,by decide⟩
def lo2633 : CheckedMoment :=
  CheckedMoment.ofBessel lo2633b1 lo2633b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2633b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨31,by decide⟩
def hi2633b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨32,by decide⟩
def hi2633 : CheckedMoment :=
  CheckedMoment.ofBessel hi2633b1 hi2633b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2633 : meanBracketCheck (9951/10000) lo2633 hi2633=true := by decide +kernel
def bracket2633 : MeanBracket := meanBracketOfMoments (9951/10000) lo2633 hi2633 accepted2633
def lo2634b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨36,by decide⟩
def lo2634b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨37,by decide⟩
def lo2634 : CheckedMoment :=
  CheckedMoment.ofBessel lo2634b1 lo2634b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2634b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨41,by decide⟩
def hi2634b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨42,by decide⟩
def hi2634 : CheckedMoment :=
  CheckedMoment.ofBessel hi2634b1 hi2634b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2634 : meanBracketCheck (12439/12500) lo2634 hi2634=true := by decide +kernel
def bracket2634 : MeanBracket := meanBracketOfMoments (12439/12500) lo2634 hi2634 accepted2634
def lo2635b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨46,by decide⟩
def lo2635b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨47,by decide⟩
def lo2635 : CheckedMoment :=
  CheckedMoment.ofBessel lo2635b1 lo2635b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2635b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨51,by decide⟩
def hi2635b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨52,by decide⟩
def hi2635 : CheckedMoment :=
  CheckedMoment.ofBessel hi2635b1 hi2635b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2635 : meanBracketCheck (49757/50000) lo2635 hi2635=true := by decide +kernel
def bracket2635 : MeanBracket := meanBracketOfMoments (49757/50000) lo2635 hi2635 accepted2635
def lo2636b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨56,by decide⟩
def lo2636b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨57,by decide⟩
def lo2636 : CheckedMoment :=
  CheckedMoment.ofBessel lo2636b1 lo2636b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2636b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨61,by decide⟩
def hi2636b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨62,by decide⟩
def hi2636 : CheckedMoment :=
  CheckedMoment.ofBessel hi2636b1 hi2636b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2636 : meanBracketCheck (24879/25000) lo2636 hi2636=true := by decide +kernel
def bracket2636 : MeanBracket := meanBracketOfMoments (24879/25000) lo2636 hi2636 accepted2636
def lo2637b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨2,by decide⟩
def lo2637b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨3,by decide⟩
def lo2637 : CheckedMoment :=
  CheckedMoment.ofBessel lo2637b1 lo2637b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2637b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨7,by decide⟩
def hi2637b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨8,by decide⟩
def hi2637 : CheckedMoment :=
  CheckedMoment.ofBessel hi2637b1 hi2637b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2637 : meanBracketCheck (49759/50000) lo2637 hi2637=true := by decide +kernel
def bracket2637 : MeanBracket := meanBracketOfMoments (49759/50000) lo2637 hi2637 accepted2637
def lo2638b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨12,by decide⟩
def lo2638b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨13,by decide⟩
def lo2638 : CheckedMoment :=
  CheckedMoment.ofBessel lo2638b1 lo2638b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2638b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨17,by decide⟩
def hi2638b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨18,by decide⟩
def hi2638 : CheckedMoment :=
  CheckedMoment.ofBessel hi2638b1 hi2638b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2638 : meanBracketCheck (622/625) lo2638 hi2638=true := by decide +kernel
def bracket2638 : MeanBracket := meanBracketOfMoments (622/625) lo2638 hi2638 accepted2638
def lo2639b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨22,by decide⟩
def lo2639b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨23,by decide⟩
def lo2639 : CheckedMoment :=
  CheckedMoment.ofBessel lo2639b1 lo2639b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2639b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨27,by decide⟩
def hi2639b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨28,by decide⟩
def hi2639 : CheckedMoment :=
  CheckedMoment.ofBessel hi2639b1 hi2639b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2639 : meanBracketCheck (49761/50000) lo2639 hi2639=true := by decide +kernel
def bracket2639 : MeanBracket := meanBracketOfMoments (49761/50000) lo2639 hi2639 accepted2639
#print axioms bracket2624
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0164
