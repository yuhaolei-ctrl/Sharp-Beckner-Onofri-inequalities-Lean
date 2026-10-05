module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0425
public import BecknerOnofri.EntropyScalarCertificate.Bessel0426
public import BecknerOnofri.EntropyScalarCertificate.Bessel0427

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0170
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2720b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨0,by decide⟩
def lo2720b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨1,by decide⟩
def lo2720 : CheckedMoment :=
  CheckedMoment.ofBessel lo2720b1 lo2720b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2720b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨5,by decide⟩
def hi2720b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨6,by decide⟩
def hi2720 : CheckedMoment :=
  CheckedMoment.ofBessel hi2720b1 hi2720b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2720 : meanBracketCheck (24921/25000) lo2720 hi2720=true := by decide +kernel
def bracket2720 : MeanBracket := meanBracketOfMoments (24921/25000) lo2720 hi2720 accepted2720
def lo2721b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨10,by decide⟩
def lo2721b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨11,by decide⟩
def lo2721 : CheckedMoment :=
  CheckedMoment.ofBessel lo2721b1 lo2721b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2721b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨15,by decide⟩
def hi2721b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨16,by decide⟩
def hi2721 : CheckedMoment :=
  CheckedMoment.ofBessel hi2721b1 hi2721b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2721 : meanBracketCheck (49843/50000) lo2721 hi2721=true := by decide +kernel
def bracket2721 : MeanBracket := meanBracketOfMoments (49843/50000) lo2721 hi2721 accepted2721
def lo2722b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨20,by decide⟩
def lo2722b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨21,by decide⟩
def lo2722 : CheckedMoment :=
  CheckedMoment.ofBessel lo2722b1 lo2722b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2722b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨25,by decide⟩
def hi2722b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨26,by decide⟩
def hi2722 : CheckedMoment :=
  CheckedMoment.ofBessel hi2722b1 hi2722b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2722 : meanBracketCheck (12461/12500) lo2722 hi2722=true := by decide +kernel
def bracket2722 : MeanBracket := meanBracketOfMoments (12461/12500) lo2722 hi2722 accepted2722
def lo2723b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨30,by decide⟩
def lo2723b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨31,by decide⟩
def lo2723 : CheckedMoment :=
  CheckedMoment.ofBessel lo2723b1 lo2723b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2723b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨35,by decide⟩
def hi2723b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨36,by decide⟩
def hi2723 : CheckedMoment :=
  CheckedMoment.ofBessel hi2723b1 hi2723b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2723 : meanBracketCheck (9969/10000) lo2723 hi2723=true := by decide +kernel
def bracket2723 : MeanBracket := meanBracketOfMoments (9969/10000) lo2723 hi2723 accepted2723
def lo2724b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨40,by decide⟩
def lo2724b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨41,by decide⟩
def lo2724 : CheckedMoment :=
  CheckedMoment.ofBessel lo2724b1 lo2724b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2724b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨45,by decide⟩
def hi2724b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨46,by decide⟩
def hi2724 : CheckedMoment :=
  CheckedMoment.ofBessel hi2724b1 hi2724b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2724 : meanBracketCheck (24923/25000) lo2724 hi2724=true := by decide +kernel
def bracket2724 : MeanBracket := meanBracketOfMoments (24923/25000) lo2724 hi2724 accepted2724
def lo2725b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨50,by decide⟩
def lo2725b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨51,by decide⟩
def lo2725 : CheckedMoment :=
  CheckedMoment.ofBessel lo2725b1 lo2725b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2725b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨55,by decide⟩
def hi2725b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨56,by decide⟩
def hi2725 : CheckedMoment :=
  CheckedMoment.ofBessel hi2725b1 hi2725b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2725 : meanBracketCheck (49847/50000) lo2725 hi2725=true := by decide +kernel
def bracket2725 : MeanBracket := meanBracketOfMoments (49847/50000) lo2725 hi2725 accepted2725
def lo2726b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨60,by decide⟩
def lo2726b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨61,by decide⟩
def lo2726 : CheckedMoment :=
  CheckedMoment.ofBessel lo2726b1 lo2726b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2726b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨1,by decide⟩
def hi2726b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨2,by decide⟩
def hi2726 : CheckedMoment :=
  CheckedMoment.ofBessel hi2726b1 hi2726b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2726 : meanBracketCheck (6231/6250) lo2726 hi2726=true := by decide +kernel
def bracket2726 : MeanBracket := meanBracketOfMoments (6231/6250) lo2726 hi2726 accepted2726
def lo2727b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨6,by decide⟩
def lo2727b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨7,by decide⟩
def lo2727 : CheckedMoment :=
  CheckedMoment.ofBessel lo2727b1 lo2727b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2727b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨11,by decide⟩
def hi2727b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨12,by decide⟩
def hi2727 : CheckedMoment :=
  CheckedMoment.ofBessel hi2727b1 hi2727b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2727 : meanBracketCheck (49849/50000) lo2727 hi2727=true := by decide +kernel
def bracket2727 : MeanBracket := meanBracketOfMoments (49849/50000) lo2727 hi2727 accepted2727
def lo2728b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨16,by decide⟩
def lo2728b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨17,by decide⟩
def lo2728 : CheckedMoment :=
  CheckedMoment.ofBessel lo2728b1 lo2728b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2728b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨21,by decide⟩
def hi2728b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨22,by decide⟩
def hi2728 : CheckedMoment :=
  CheckedMoment.ofBessel hi2728b1 hi2728b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2728 : meanBracketCheck (997/1000) lo2728 hi2728=true := by decide +kernel
def bracket2728 : MeanBracket := meanBracketOfMoments (997/1000) lo2728 hi2728 accepted2728
def lo2729b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨26,by decide⟩
def lo2729b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨27,by decide⟩
def lo2729 : CheckedMoment :=
  CheckedMoment.ofBessel lo2729b1 lo2729b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2729b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨31,by decide⟩
def hi2729b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨32,by decide⟩
def hi2729 : CheckedMoment :=
  CheckedMoment.ofBessel hi2729b1 hi2729b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2729 : meanBracketCheck (199401/200000) lo2729 hi2729=true := by decide +kernel
def bracket2729 : MeanBracket := meanBracketOfMoments (199401/200000) lo2729 hi2729 accepted2729
def lo2730b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨36,by decide⟩
def lo2730b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨37,by decide⟩
def lo2730 : CheckedMoment :=
  CheckedMoment.ofBessel lo2730b1 lo2730b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2730b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨41,by decide⟩
def hi2730b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨42,by decide⟩
def hi2730 : CheckedMoment :=
  CheckedMoment.ofBessel hi2730b1 hi2730b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2730 : meanBracketCheck (99701/100000) lo2730 hi2730=true := by decide +kernel
def bracket2730 : MeanBracket := meanBracketOfMoments (99701/100000) lo2730 hi2730 accepted2730
def lo2731b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨46,by decide⟩
def lo2731b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨47,by decide⟩
def lo2731 : CheckedMoment :=
  CheckedMoment.ofBessel lo2731b1 lo2731b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2731b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨51,by decide⟩
def hi2731b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨52,by decide⟩
def hi2731 : CheckedMoment :=
  CheckedMoment.ofBessel hi2731b1 hi2731b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2731 : meanBracketCheck (199403/200000) lo2731 hi2731=true := by decide +kernel
def bracket2731 : MeanBracket := meanBracketOfMoments (199403/200000) lo2731 hi2731 accepted2731
def lo2732b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨56,by decide⟩
def lo2732b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨57,by decide⟩
def lo2732 : CheckedMoment :=
  CheckedMoment.ofBessel lo2732b1 lo2732b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2732b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨61,by decide⟩
def hi2732b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0426.rows BesselBatch0426.accepted ⟨62,by decide⟩
def hi2732 : CheckedMoment :=
  CheckedMoment.ofBessel hi2732b1 hi2732b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2732 : meanBracketCheck (49851/50000) lo2732 hi2732=true := by decide +kernel
def bracket2732 : MeanBracket := meanBracketOfMoments (49851/50000) lo2732 hi2732 accepted2732
def lo2733b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨2,by decide⟩
def lo2733b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨3,by decide⟩
def lo2733 : CheckedMoment :=
  CheckedMoment.ofBessel lo2733b1 lo2733b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2733b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨7,by decide⟩
def hi2733b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨8,by decide⟩
def hi2733 : CheckedMoment :=
  CheckedMoment.ofBessel hi2733b1 hi2733b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2733 : meanBracketCheck (39881/40000) lo2733 hi2733=true := by decide +kernel
def bracket2733 : MeanBracket := meanBracketOfMoments (39881/40000) lo2733 hi2733 accepted2733
def lo2734b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨12,by decide⟩
def lo2734b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨13,by decide⟩
def lo2734 : CheckedMoment :=
  CheckedMoment.ofBessel lo2734b1 lo2734b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2734b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨17,by decide⟩
def hi2734b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨18,by decide⟩
def hi2734 : CheckedMoment :=
  CheckedMoment.ofBessel hi2734b1 hi2734b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2734 : meanBracketCheck (99703/100000) lo2734 hi2734=true := by decide +kernel
def bracket2734 : MeanBracket := meanBracketOfMoments (99703/100000) lo2734 hi2734 accepted2734
def lo2735b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨22,by decide⟩
def lo2735b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨23,by decide⟩
def lo2735 : CheckedMoment :=
  CheckedMoment.ofBessel lo2735b1 lo2735b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2735b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨27,by decide⟩
def hi2735b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨28,by decide⟩
def hi2735 : CheckedMoment :=
  CheckedMoment.ofBessel hi2735b1 hi2735b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2735 : meanBracketCheck (199407/200000) lo2735 hi2735=true := by decide +kernel
def bracket2735 : MeanBracket := meanBracketOfMoments (199407/200000) lo2735 hi2735 accepted2735
#print axioms bracket2720
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0170
