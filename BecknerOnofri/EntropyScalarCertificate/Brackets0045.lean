module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0112
public import BecknerOnofri.EntropyScalarCertificate.Bessel0113
public import BecknerOnofri.EntropyScalarCertificate.Bessel0114

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0045
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0720b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨32,by decide⟩
def lo0720b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨33,by decide⟩
def lo0720 : CheckedMoment :=
  CheckedMoment.ofBessel lo0720b1 lo0720b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0720b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨37,by decide⟩
def hi0720b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨38,by decide⟩
def hi0720 : CheckedMoment :=
  CheckedMoment.ofBessel hi0720b1 hi0720b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0720 : meanBracketCheck (101/500) lo0720 hi0720=true := by decide +kernel
def bracket0720 : MeanBracket := meanBracketOfMoments (101/500) lo0720 hi0720 accepted0720
def lo0721b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨42,by decide⟩
def lo0721b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨43,by decide⟩
def lo0721 : CheckedMoment :=
  CheckedMoment.ofBessel lo0721b1 lo0721b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0721b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨47,by decide⟩
def hi0721b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨48,by decide⟩
def hi0721 : CheckedMoment :=
  CheckedMoment.ofBessel hi0721b1 hi0721b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0721 : meanBracketCheck (203/1000) lo0721 hi0721=true := by decide +kernel
def bracket0721 : MeanBracket := meanBracketOfMoments (203/1000) lo0721 hi0721 accepted0721
def lo0722b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨52,by decide⟩
def lo0722b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨53,by decide⟩
def lo0722 : CheckedMoment :=
  CheckedMoment.ofBessel lo0722b1 lo0722b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0722b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨57,by decide⟩
def hi0722b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨58,by decide⟩
def hi0722 : CheckedMoment :=
  CheckedMoment.ofBessel hi0722b1 hi0722b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0722 : meanBracketCheck (51/250) lo0722 hi0722=true := by decide +kernel
def bracket0722 : MeanBracket := meanBracketOfMoments (51/250) lo0722 hi0722 accepted0722
def lo0723b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨62,by decide⟩
def lo0723b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨63,by decide⟩
def lo0723 : CheckedMoment :=
  CheckedMoment.ofBessel lo0723b1 lo0723b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0723b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨3,by decide⟩
def hi0723b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨4,by decide⟩
def hi0723 : CheckedMoment :=
  CheckedMoment.ofBessel hi0723b1 hi0723b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0723 : meanBracketCheck (41/200) lo0723 hi0723=true := by decide +kernel
def bracket0723 : MeanBracket := meanBracketOfMoments (41/200) lo0723 hi0723 accepted0723
def lo0724b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨8,by decide⟩
def lo0724b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨9,by decide⟩
def lo0724 : CheckedMoment :=
  CheckedMoment.ofBessel lo0724b1 lo0724b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0724b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨13,by decide⟩
def hi0724b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨14,by decide⟩
def hi0724 : CheckedMoment :=
  CheckedMoment.ofBessel hi0724b1 hi0724b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0724 : meanBracketCheck (103/500) lo0724 hi0724=true := by decide +kernel
def bracket0724 : MeanBracket := meanBracketOfMoments (103/500) lo0724 hi0724 accepted0724
def lo0725b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨18,by decide⟩
def lo0725b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨19,by decide⟩
def lo0725 : CheckedMoment :=
  CheckedMoment.ofBessel lo0725b1 lo0725b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0725b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨23,by decide⟩
def hi0725b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨24,by decide⟩
def hi0725 : CheckedMoment :=
  CheckedMoment.ofBessel hi0725b1 hi0725b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0725 : meanBracketCheck (207/1000) lo0725 hi0725=true := by decide +kernel
def bracket0725 : MeanBracket := meanBracketOfMoments (207/1000) lo0725 hi0725 accepted0725
def lo0726b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨28,by decide⟩
def lo0726b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨29,by decide⟩
def lo0726 : CheckedMoment :=
  CheckedMoment.ofBessel lo0726b1 lo0726b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0726b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨33,by decide⟩
def hi0726b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨34,by decide⟩
def hi0726 : CheckedMoment :=
  CheckedMoment.ofBessel hi0726b1 hi0726b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0726 : meanBracketCheck (26/125) lo0726 hi0726=true := by decide +kernel
def bracket0726 : MeanBracket := meanBracketOfMoments (26/125) lo0726 hi0726 accepted0726
def lo0727b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨38,by decide⟩
def lo0727b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨39,by decide⟩
def lo0727 : CheckedMoment :=
  CheckedMoment.ofBessel lo0727b1 lo0727b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0727b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨43,by decide⟩
def hi0727b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨44,by decide⟩
def hi0727 : CheckedMoment :=
  CheckedMoment.ofBessel hi0727b1 hi0727b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0727 : meanBracketCheck (209/1000) lo0727 hi0727=true := by decide +kernel
def bracket0727 : MeanBracket := meanBracketOfMoments (209/1000) lo0727 hi0727 accepted0727
def lo0728b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨48,by decide⟩
def lo0728b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨49,by decide⟩
def lo0728 : CheckedMoment :=
  CheckedMoment.ofBessel lo0728b1 lo0728b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0728b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨53,by decide⟩
def hi0728b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨54,by decide⟩
def hi0728 : CheckedMoment :=
  CheckedMoment.ofBessel hi0728b1 hi0728b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0728 : meanBracketCheck (21/100) lo0728 hi0728=true := by decide +kernel
def bracket0728 : MeanBracket := meanBracketOfMoments (21/100) lo0728 hi0728 accepted0728
def lo0729b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨58,by decide⟩
def lo0729b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨59,by decide⟩
def lo0729 : CheckedMoment :=
  CheckedMoment.ofBessel lo0729b1 lo0729b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0729b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨63,by decide⟩
def hi0729b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨0,by decide⟩
def hi0729 : CheckedMoment :=
  CheckedMoment.ofBessel hi0729b1 hi0729b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0729 : meanBracketCheck (211/1000) lo0729 hi0729=true := by decide +kernel
def bracket0729 : MeanBracket := meanBracketOfMoments (211/1000) lo0729 hi0729 accepted0729
def lo0730b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨4,by decide⟩
def lo0730b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨5,by decide⟩
def lo0730 : CheckedMoment :=
  CheckedMoment.ofBessel lo0730b1 lo0730b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0730b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨9,by decide⟩
def hi0730b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨10,by decide⟩
def hi0730 : CheckedMoment :=
  CheckedMoment.ofBessel hi0730b1 hi0730b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0730 : meanBracketCheck (53/250) lo0730 hi0730=true := by decide +kernel
def bracket0730 : MeanBracket := meanBracketOfMoments (53/250) lo0730 hi0730 accepted0730
def lo0731b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨14,by decide⟩
def lo0731b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨15,by decide⟩
def lo0731 : CheckedMoment :=
  CheckedMoment.ofBessel lo0731b1 lo0731b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0731b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨19,by decide⟩
def hi0731b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨20,by decide⟩
def hi0731 : CheckedMoment :=
  CheckedMoment.ofBessel hi0731b1 hi0731b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0731 : meanBracketCheck (213/1000) lo0731 hi0731=true := by decide +kernel
def bracket0731 : MeanBracket := meanBracketOfMoments (213/1000) lo0731 hi0731 accepted0731
def lo0732b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨24,by decide⟩
def lo0732b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨25,by decide⟩
def lo0732 : CheckedMoment :=
  CheckedMoment.ofBessel lo0732b1 lo0732b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0732b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨29,by decide⟩
def hi0732b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨30,by decide⟩
def hi0732 : CheckedMoment :=
  CheckedMoment.ofBessel hi0732b1 hi0732b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0732 : meanBracketCheck (107/500) lo0732 hi0732=true := by decide +kernel
def bracket0732 : MeanBracket := meanBracketOfMoments (107/500) lo0732 hi0732 accepted0732
def lo0733b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨34,by decide⟩
def lo0733b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨35,by decide⟩
def lo0733 : CheckedMoment :=
  CheckedMoment.ofBessel lo0733b1 lo0733b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0733b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨39,by decide⟩
def hi0733b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨40,by decide⟩
def hi0733 : CheckedMoment :=
  CheckedMoment.ofBessel hi0733b1 hi0733b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0733 : meanBracketCheck (43/200) lo0733 hi0733=true := by decide +kernel
def bracket0733 : MeanBracket := meanBracketOfMoments (43/200) lo0733 hi0733 accepted0733
def lo0734b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨44,by decide⟩
def lo0734b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨45,by decide⟩
def lo0734 : CheckedMoment :=
  CheckedMoment.ofBessel lo0734b1 lo0734b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0734b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨49,by decide⟩
def hi0734b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨50,by decide⟩
def hi0734 : CheckedMoment :=
  CheckedMoment.ofBessel hi0734b1 hi0734b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0734 : meanBracketCheck (27/125) lo0734 hi0734=true := by decide +kernel
def bracket0734 : MeanBracket := meanBracketOfMoments (27/125) lo0734 hi0734 accepted0734
def lo0735b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨54,by decide⟩
def lo0735b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨55,by decide⟩
def lo0735 : CheckedMoment :=
  CheckedMoment.ofBessel lo0735b1 lo0735b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0735b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨59,by decide⟩
def hi0735b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨60,by decide⟩
def hi0735 : CheckedMoment :=
  CheckedMoment.ofBessel hi0735b1 hi0735b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0735 : meanBracketCheck (217/1000) lo0735 hi0735=true := by decide +kernel
def bracket0735 : MeanBracket := meanBracketOfMoments (217/1000) lo0735 hi0735 accepted0735
#print axioms bracket0720
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0045
