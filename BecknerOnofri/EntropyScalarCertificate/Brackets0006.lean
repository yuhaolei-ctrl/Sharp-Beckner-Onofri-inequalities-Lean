import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0015
import BecknerOnofri.EntropyScalarCertificate.Bessel0016
import BecknerOnofri.EntropyScalarCertificate.Bessel0017
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0006
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0096b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨0,by decide⟩
def lo0096b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨1,by decide⟩
def lo0096 : CheckedMoment :=
  CheckedMoment.ofBessel lo0096b1 lo0096b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0096b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨5,by decide⟩
def hi0096b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨6,by decide⟩
def hi0096 : CheckedMoment :=
  CheckedMoment.ofBessel hi0096b1 hi0096b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0096 : meanBracketCheck (757/10000) lo0096 hi0096=true := by decide +kernel
def bracket0096 : MeanBracket := meanBracketOfMoments (757/10000) lo0096 hi0096 accepted0096
def lo0097b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨10,by decide⟩
def lo0097b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨11,by decide⟩
def lo0097 : CheckedMoment :=
  CheckedMoment.ofBessel lo0097b1 lo0097b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0097b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨15,by decide⟩
def hi0097b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨16,by decide⟩
def hi0097 : CheckedMoment :=
  CheckedMoment.ofBessel hi0097b1 hi0097b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0097 : meanBracketCheck (759/10000) lo0097 hi0097=true := by decide +kernel
def bracket0097 : MeanBracket := meanBracketOfMoments (759/10000) lo0097 hi0097 accepted0097
def lo0098b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨20,by decide⟩
def lo0098b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨21,by decide⟩
def lo0098 : CheckedMoment :=
  CheckedMoment.ofBessel lo0098b1 lo0098b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0098b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨25,by decide⟩
def hi0098b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨26,by decide⟩
def hi0098 : CheckedMoment :=
  CheckedMoment.ofBessel hi0098b1 hi0098b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0098 : meanBracketCheck (761/10000) lo0098 hi0098=true := by decide +kernel
def bracket0098 : MeanBracket := meanBracketOfMoments (761/10000) lo0098 hi0098 accepted0098
def lo0099b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨30,by decide⟩
def lo0099b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨31,by decide⟩
def lo0099 : CheckedMoment :=
  CheckedMoment.ofBessel lo0099b1 lo0099b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0099b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨35,by decide⟩
def hi0099b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨36,by decide⟩
def hi0099 : CheckedMoment :=
  CheckedMoment.ofBessel hi0099b1 hi0099b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0099 : meanBracketCheck (763/10000) lo0099 hi0099=true := by decide +kernel
def bracket0099 : MeanBracket := meanBracketOfMoments (763/10000) lo0099 hi0099 accepted0099
def lo0100b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨40,by decide⟩
def lo0100b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨41,by decide⟩
def lo0100 : CheckedMoment :=
  CheckedMoment.ofBessel lo0100b1 lo0100b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0100b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨45,by decide⟩
def hi0100b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨46,by decide⟩
def hi0100 : CheckedMoment :=
  CheckedMoment.ofBessel hi0100b1 hi0100b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0100 : meanBracketCheck (153/2000) lo0100 hi0100=true := by decide +kernel
def bracket0100 : MeanBracket := meanBracketOfMoments (153/2000) lo0100 hi0100 accepted0100
def lo0101b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨50,by decide⟩
def lo0101b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨51,by decide⟩
def lo0101 : CheckedMoment :=
  CheckedMoment.ofBessel lo0101b1 lo0101b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0101b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨55,by decide⟩
def hi0101b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨56,by decide⟩
def hi0101 : CheckedMoment :=
  CheckedMoment.ofBessel hi0101b1 hi0101b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0101 : meanBracketCheck (767/10000) lo0101 hi0101=true := by decide +kernel
def bracket0101 : MeanBracket := meanBracketOfMoments (767/10000) lo0101 hi0101 accepted0101
def lo0102b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨60,by decide⟩
def lo0102b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨61,by decide⟩
def lo0102 : CheckedMoment :=
  CheckedMoment.ofBessel lo0102b1 lo0102b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0102b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨1,by decide⟩
def hi0102b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨2,by decide⟩
def hi0102 : CheckedMoment :=
  CheckedMoment.ofBessel hi0102b1 hi0102b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0102 : meanBracketCheck (769/10000) lo0102 hi0102=true := by decide +kernel
def bracket0102 : MeanBracket := meanBracketOfMoments (769/10000) lo0102 hi0102 accepted0102
def lo0103b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨6,by decide⟩
def lo0103b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨7,by decide⟩
def lo0103 : CheckedMoment :=
  CheckedMoment.ofBessel lo0103b1 lo0103b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0103b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨11,by decide⟩
def hi0103b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨12,by decide⟩
def hi0103 : CheckedMoment :=
  CheckedMoment.ofBessel hi0103b1 hi0103b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0103 : meanBracketCheck (771/10000) lo0103 hi0103=true := by decide +kernel
def bracket0103 : MeanBracket := meanBracketOfMoments (771/10000) lo0103 hi0103 accepted0103
def lo0104b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨16,by decide⟩
def lo0104b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨17,by decide⟩
def lo0104 : CheckedMoment :=
  CheckedMoment.ofBessel lo0104b1 lo0104b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0104b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨21,by decide⟩
def hi0104b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨22,by decide⟩
def hi0104 : CheckedMoment :=
  CheckedMoment.ofBessel hi0104b1 hi0104b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0104 : meanBracketCheck (773/10000) lo0104 hi0104=true := by decide +kernel
def bracket0104 : MeanBracket := meanBracketOfMoments (773/10000) lo0104 hi0104 accepted0104
def lo0105b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨26,by decide⟩
def lo0105b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨27,by decide⟩
def lo0105 : CheckedMoment :=
  CheckedMoment.ofBessel lo0105b1 lo0105b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0105b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨31,by decide⟩
def hi0105b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨32,by decide⟩
def hi0105 : CheckedMoment :=
  CheckedMoment.ofBessel hi0105b1 hi0105b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0105 : meanBracketCheck (31/400) lo0105 hi0105=true := by decide +kernel
def bracket0105 : MeanBracket := meanBracketOfMoments (31/400) lo0105 hi0105 accepted0105
def lo0106b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨36,by decide⟩
def lo0106b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨37,by decide⟩
def lo0106 : CheckedMoment :=
  CheckedMoment.ofBessel lo0106b1 lo0106b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0106b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨41,by decide⟩
def hi0106b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨42,by decide⟩
def hi0106 : CheckedMoment :=
  CheckedMoment.ofBessel hi0106b1 hi0106b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0106 : meanBracketCheck (777/10000) lo0106 hi0106=true := by decide +kernel
def bracket0106 : MeanBracket := meanBracketOfMoments (777/10000) lo0106 hi0106 accepted0106
def lo0107b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨46,by decide⟩
def lo0107b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨47,by decide⟩
def lo0107 : CheckedMoment :=
  CheckedMoment.ofBessel lo0107b1 lo0107b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0107b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨51,by decide⟩
def hi0107b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨52,by decide⟩
def hi0107 : CheckedMoment :=
  CheckedMoment.ofBessel hi0107b1 hi0107b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0107 : meanBracketCheck (779/10000) lo0107 hi0107=true := by decide +kernel
def bracket0107 : MeanBracket := meanBracketOfMoments (779/10000) lo0107 hi0107 accepted0107
def lo0108b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨56,by decide⟩
def lo0108b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨57,by decide⟩
def lo0108 : CheckedMoment :=
  CheckedMoment.ofBessel lo0108b1 lo0108b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0108b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨61,by decide⟩
def hi0108b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨62,by decide⟩
def hi0108 : CheckedMoment :=
  CheckedMoment.ofBessel hi0108b1 hi0108b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0108 : meanBracketCheck (781/10000) lo0108 hi0108=true := by decide +kernel
def bracket0108 : MeanBracket := meanBracketOfMoments (781/10000) lo0108 hi0108 accepted0108
def lo0109b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨2,by decide⟩
def lo0109b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨3,by decide⟩
def lo0109 : CheckedMoment :=
  CheckedMoment.ofBessel lo0109b1 lo0109b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0109b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨7,by decide⟩
def hi0109b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨8,by decide⟩
def hi0109 : CheckedMoment :=
  CheckedMoment.ofBessel hi0109b1 hi0109b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0109 : meanBracketCheck (783/10000) lo0109 hi0109=true := by decide +kernel
def bracket0109 : MeanBracket := meanBracketOfMoments (783/10000) lo0109 hi0109 accepted0109
def lo0110b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨12,by decide⟩
def lo0110b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨13,by decide⟩
def lo0110 : CheckedMoment :=
  CheckedMoment.ofBessel lo0110b1 lo0110b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0110b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨17,by decide⟩
def hi0110b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨18,by decide⟩
def hi0110 : CheckedMoment :=
  CheckedMoment.ofBessel hi0110b1 hi0110b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0110 : meanBracketCheck (157/2000) lo0110 hi0110=true := by decide +kernel
def bracket0110 : MeanBracket := meanBracketOfMoments (157/2000) lo0110 hi0110 accepted0110
def lo0111b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨22,by decide⟩
def lo0111b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨23,by decide⟩
def lo0111 : CheckedMoment :=
  CheckedMoment.ofBessel lo0111b1 lo0111b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0111b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨27,by decide⟩
def hi0111b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨28,by decide⟩
def hi0111 : CheckedMoment :=
  CheckedMoment.ofBessel hi0111b1 hi0111b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0111 : meanBracketCheck (787/10000) lo0111 hi0111=true := by decide +kernel
def bracket0111 : MeanBracket := meanBracketOfMoments (787/10000) lo0111 hi0111 accepted0111
#print axioms bracket0096
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0006
