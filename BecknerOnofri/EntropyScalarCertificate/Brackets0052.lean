import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0130
import BecknerOnofri.EntropyScalarCertificate.Bessel0131
import BecknerOnofri.EntropyScalarCertificate.Bessel0132
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0052
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0832b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨0,by decide⟩
def lo0832b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨1,by decide⟩
def lo0832 : CheckedMoment :=
  CheckedMoment.ofBessel lo0832b1 lo0832b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0832b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨5,by decide⟩
def hi0832b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨6,by decide⟩
def hi0832 : CheckedMoment :=
  CheckedMoment.ofBessel hi0832b1 hi0832b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0832 : meanBracketCheck (157/500) lo0832 hi0832=true := by decide +kernel
def bracket0832 : MeanBracket := meanBracketOfMoments (157/500) lo0832 hi0832 accepted0832
def lo0833b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨10,by decide⟩
def lo0833b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨11,by decide⟩
def lo0833 : CheckedMoment :=
  CheckedMoment.ofBessel lo0833b1 lo0833b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0833b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨15,by decide⟩
def hi0833b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨16,by decide⟩
def hi0833 : CheckedMoment :=
  CheckedMoment.ofBessel hi0833b1 hi0833b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0833 : meanBracketCheck (63/200) lo0833 hi0833=true := by decide +kernel
def bracket0833 : MeanBracket := meanBracketOfMoments (63/200) lo0833 hi0833 accepted0833
def lo0834b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨20,by decide⟩
def lo0834b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨21,by decide⟩
def lo0834 : CheckedMoment :=
  CheckedMoment.ofBessel lo0834b1 lo0834b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0834b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨25,by decide⟩
def hi0834b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨26,by decide⟩
def hi0834 : CheckedMoment :=
  CheckedMoment.ofBessel hi0834b1 hi0834b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0834 : meanBracketCheck (79/250) lo0834 hi0834=true := by decide +kernel
def bracket0834 : MeanBracket := meanBracketOfMoments (79/250) lo0834 hi0834 accepted0834
def lo0835b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨30,by decide⟩
def lo0835b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨31,by decide⟩
def lo0835 : CheckedMoment :=
  CheckedMoment.ofBessel lo0835b1 lo0835b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0835b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨35,by decide⟩
def hi0835b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨36,by decide⟩
def hi0835 : CheckedMoment :=
  CheckedMoment.ofBessel hi0835b1 hi0835b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0835 : meanBracketCheck (317/1000) lo0835 hi0835=true := by decide +kernel
def bracket0835 : MeanBracket := meanBracketOfMoments (317/1000) lo0835 hi0835 accepted0835
def lo0836b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨40,by decide⟩
def lo0836b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨41,by decide⟩
def lo0836 : CheckedMoment :=
  CheckedMoment.ofBessel lo0836b1 lo0836b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0836b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨45,by decide⟩
def hi0836b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨46,by decide⟩
def hi0836 : CheckedMoment :=
  CheckedMoment.ofBessel hi0836b1 hi0836b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0836 : meanBracketCheck (159/500) lo0836 hi0836=true := by decide +kernel
def bracket0836 : MeanBracket := meanBracketOfMoments (159/500) lo0836 hi0836 accepted0836
def lo0837b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨50,by decide⟩
def lo0837b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨51,by decide⟩
def lo0837 : CheckedMoment :=
  CheckedMoment.ofBessel lo0837b1 lo0837b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0837b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨55,by decide⟩
def hi0837b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨56,by decide⟩
def hi0837 : CheckedMoment :=
  CheckedMoment.ofBessel hi0837b1 hi0837b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0837 : meanBracketCheck (319/1000) lo0837 hi0837=true := by decide +kernel
def bracket0837 : MeanBracket := meanBracketOfMoments (319/1000) lo0837 hi0837 accepted0837
def lo0838b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨60,by decide⟩
def lo0838b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨61,by decide⟩
def lo0838 : CheckedMoment :=
  CheckedMoment.ofBessel lo0838b1 lo0838b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0838b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨1,by decide⟩
def hi0838b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨2,by decide⟩
def hi0838 : CheckedMoment :=
  CheckedMoment.ofBessel hi0838b1 hi0838b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0838 : meanBracketCheck (8/25) lo0838 hi0838=true := by decide +kernel
def bracket0838 : MeanBracket := meanBracketOfMoments (8/25) lo0838 hi0838 accepted0838
def lo0839b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨6,by decide⟩
def lo0839b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨7,by decide⟩
def lo0839 : CheckedMoment :=
  CheckedMoment.ofBessel lo0839b1 lo0839b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0839b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨11,by decide⟩
def hi0839b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨12,by decide⟩
def hi0839 : CheckedMoment :=
  CheckedMoment.ofBessel hi0839b1 hi0839b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0839 : meanBracketCheck (321/1000) lo0839 hi0839=true := by decide +kernel
def bracket0839 : MeanBracket := meanBracketOfMoments (321/1000) lo0839 hi0839 accepted0839
def lo0840b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨16,by decide⟩
def lo0840b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨17,by decide⟩
def lo0840 : CheckedMoment :=
  CheckedMoment.ofBessel lo0840b1 lo0840b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0840b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨21,by decide⟩
def hi0840b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨22,by decide⟩
def hi0840 : CheckedMoment :=
  CheckedMoment.ofBessel hi0840b1 hi0840b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0840 : meanBracketCheck (161/500) lo0840 hi0840=true := by decide +kernel
def bracket0840 : MeanBracket := meanBracketOfMoments (161/500) lo0840 hi0840 accepted0840
def lo0841b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨26,by decide⟩
def lo0841b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨27,by decide⟩
def lo0841 : CheckedMoment :=
  CheckedMoment.ofBessel lo0841b1 lo0841b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0841b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨31,by decide⟩
def hi0841b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨32,by decide⟩
def hi0841 : CheckedMoment :=
  CheckedMoment.ofBessel hi0841b1 hi0841b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0841 : meanBracketCheck (323/1000) lo0841 hi0841=true := by decide +kernel
def bracket0841 : MeanBracket := meanBracketOfMoments (323/1000) lo0841 hi0841 accepted0841
def lo0842b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨36,by decide⟩
def lo0842b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨37,by decide⟩
def lo0842 : CheckedMoment :=
  CheckedMoment.ofBessel lo0842b1 lo0842b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0842b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨41,by decide⟩
def hi0842b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨42,by decide⟩
def hi0842 : CheckedMoment :=
  CheckedMoment.ofBessel hi0842b1 hi0842b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0842 : meanBracketCheck (81/250) lo0842 hi0842=true := by decide +kernel
def bracket0842 : MeanBracket := meanBracketOfMoments (81/250) lo0842 hi0842 accepted0842
def lo0843b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨46,by decide⟩
def lo0843b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨47,by decide⟩
def lo0843 : CheckedMoment :=
  CheckedMoment.ofBessel lo0843b1 lo0843b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0843b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨51,by decide⟩
def hi0843b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨52,by decide⟩
def hi0843 : CheckedMoment :=
  CheckedMoment.ofBessel hi0843b1 hi0843b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0843 : meanBracketCheck (13/40) lo0843 hi0843=true := by decide +kernel
def bracket0843 : MeanBracket := meanBracketOfMoments (13/40) lo0843 hi0843 accepted0843
def lo0844b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨56,by decide⟩
def lo0844b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨57,by decide⟩
def lo0844 : CheckedMoment :=
  CheckedMoment.ofBessel lo0844b1 lo0844b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0844b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨61,by decide⟩
def hi0844b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨62,by decide⟩
def hi0844 : CheckedMoment :=
  CheckedMoment.ofBessel hi0844b1 hi0844b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0844 : meanBracketCheck (163/500) lo0844 hi0844=true := by decide +kernel
def bracket0844 : MeanBracket := meanBracketOfMoments (163/500) lo0844 hi0844 accepted0844
def lo0845b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨2,by decide⟩
def lo0845b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨3,by decide⟩
def lo0845 : CheckedMoment :=
  CheckedMoment.ofBessel lo0845b1 lo0845b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0845b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨7,by decide⟩
def hi0845b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨8,by decide⟩
def hi0845 : CheckedMoment :=
  CheckedMoment.ofBessel hi0845b1 hi0845b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0845 : meanBracketCheck (327/1000) lo0845 hi0845=true := by decide +kernel
def bracket0845 : MeanBracket := meanBracketOfMoments (327/1000) lo0845 hi0845 accepted0845
def lo0846b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨12,by decide⟩
def lo0846b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨13,by decide⟩
def lo0846 : CheckedMoment :=
  CheckedMoment.ofBessel lo0846b1 lo0846b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0846b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨17,by decide⟩
def hi0846b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨18,by decide⟩
def hi0846 : CheckedMoment :=
  CheckedMoment.ofBessel hi0846b1 hi0846b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0846 : meanBracketCheck (41/125) lo0846 hi0846=true := by decide +kernel
def bracket0846 : MeanBracket := meanBracketOfMoments (41/125) lo0846 hi0846 accepted0846
def lo0847b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨22,by decide⟩
def lo0847b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨23,by decide⟩
def lo0847 : CheckedMoment :=
  CheckedMoment.ofBessel lo0847b1 lo0847b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0847b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨27,by decide⟩
def hi0847b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨28,by decide⟩
def hi0847 : CheckedMoment :=
  CheckedMoment.ofBessel hi0847b1 hi0847b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0847 : meanBracketCheck (329/1000) lo0847 hi0847=true := by decide +kernel
def bracket0847 : MeanBracket := meanBracketOfMoments (329/1000) lo0847 hi0847 accepted0847
#print axioms bracket0832
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0052
