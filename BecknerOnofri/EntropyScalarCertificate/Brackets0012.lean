import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0030
import BecknerOnofri.EntropyScalarCertificate.Bessel0031
import BecknerOnofri.EntropyScalarCertificate.Bessel0032
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0012
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0192b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨0,by decide⟩
def lo0192b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨1,by decide⟩
def lo0192 : CheckedMoment :=
  CheckedMoment.ofBessel lo0192b1 lo0192b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0192b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨5,by decide⟩
def hi0192b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨6,by decide⟩
def hi0192 : CheckedMoment :=
  CheckedMoment.ofBessel hi0192b1 hi0192b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0192 : meanBracketCheck (949/10000) lo0192 hi0192=true := by decide +kernel
def bracket0192 : MeanBracket := meanBracketOfMoments (949/10000) lo0192 hi0192 accepted0192
def lo0193b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨10,by decide⟩
def lo0193b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨11,by decide⟩
def lo0193 : CheckedMoment :=
  CheckedMoment.ofBessel lo0193b1 lo0193b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0193b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨15,by decide⟩
def hi0193b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨16,by decide⟩
def hi0193 : CheckedMoment :=
  CheckedMoment.ofBessel hi0193b1 hi0193b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0193 : meanBracketCheck (951/10000) lo0193 hi0193=true := by decide +kernel
def bracket0193 : MeanBracket := meanBracketOfMoments (951/10000) lo0193 hi0193 accepted0193
def lo0194b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨20,by decide⟩
def lo0194b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨21,by decide⟩
def lo0194 : CheckedMoment :=
  CheckedMoment.ofBessel lo0194b1 lo0194b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0194b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨25,by decide⟩
def hi0194b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨26,by decide⟩
def hi0194 : CheckedMoment :=
  CheckedMoment.ofBessel hi0194b1 hi0194b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0194 : meanBracketCheck (953/10000) lo0194 hi0194=true := by decide +kernel
def bracket0194 : MeanBracket := meanBracketOfMoments (953/10000) lo0194 hi0194 accepted0194
def lo0195b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨30,by decide⟩
def lo0195b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨31,by decide⟩
def lo0195 : CheckedMoment :=
  CheckedMoment.ofBessel lo0195b1 lo0195b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0195b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨35,by decide⟩
def hi0195b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨36,by decide⟩
def hi0195 : CheckedMoment :=
  CheckedMoment.ofBessel hi0195b1 hi0195b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0195 : meanBracketCheck (191/2000) lo0195 hi0195=true := by decide +kernel
def bracket0195 : MeanBracket := meanBracketOfMoments (191/2000) lo0195 hi0195 accepted0195
def lo0196b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨40,by decide⟩
def lo0196b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨41,by decide⟩
def lo0196 : CheckedMoment :=
  CheckedMoment.ofBessel lo0196b1 lo0196b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0196b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨45,by decide⟩
def hi0196b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨46,by decide⟩
def hi0196 : CheckedMoment :=
  CheckedMoment.ofBessel hi0196b1 hi0196b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0196 : meanBracketCheck (957/10000) lo0196 hi0196=true := by decide +kernel
def bracket0196 : MeanBracket := meanBracketOfMoments (957/10000) lo0196 hi0196 accepted0196
def lo0197b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨50,by decide⟩
def lo0197b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨51,by decide⟩
def lo0197 : CheckedMoment :=
  CheckedMoment.ofBessel lo0197b1 lo0197b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0197b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨55,by decide⟩
def hi0197b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨56,by decide⟩
def hi0197 : CheckedMoment :=
  CheckedMoment.ofBessel hi0197b1 hi0197b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0197 : meanBracketCheck (959/10000) lo0197 hi0197=true := by decide +kernel
def bracket0197 : MeanBracket := meanBracketOfMoments (959/10000) lo0197 hi0197 accepted0197
def lo0198b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨60,by decide⟩
def lo0198b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨61,by decide⟩
def lo0198 : CheckedMoment :=
  CheckedMoment.ofBessel lo0198b1 lo0198b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0198b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨1,by decide⟩
def hi0198b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨2,by decide⟩
def hi0198 : CheckedMoment :=
  CheckedMoment.ofBessel hi0198b1 hi0198b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0198 : meanBracketCheck (961/10000) lo0198 hi0198=true := by decide +kernel
def bracket0198 : MeanBracket := meanBracketOfMoments (961/10000) lo0198 hi0198 accepted0198
def lo0199b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨6,by decide⟩
def lo0199b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨7,by decide⟩
def lo0199 : CheckedMoment :=
  CheckedMoment.ofBessel lo0199b1 lo0199b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0199b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨11,by decide⟩
def hi0199b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨12,by decide⟩
def hi0199 : CheckedMoment :=
  CheckedMoment.ofBessel hi0199b1 hi0199b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0199 : meanBracketCheck (963/10000) lo0199 hi0199=true := by decide +kernel
def bracket0199 : MeanBracket := meanBracketOfMoments (963/10000) lo0199 hi0199 accepted0199
def lo0200b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨16,by decide⟩
def lo0200b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨17,by decide⟩
def lo0200 : CheckedMoment :=
  CheckedMoment.ofBessel lo0200b1 lo0200b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0200b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨21,by decide⟩
def hi0200b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨22,by decide⟩
def hi0200 : CheckedMoment :=
  CheckedMoment.ofBessel hi0200b1 hi0200b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0200 : meanBracketCheck (193/2000) lo0200 hi0200=true := by decide +kernel
def bracket0200 : MeanBracket := meanBracketOfMoments (193/2000) lo0200 hi0200 accepted0200
def lo0201b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨26,by decide⟩
def lo0201b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨27,by decide⟩
def lo0201 : CheckedMoment :=
  CheckedMoment.ofBessel lo0201b1 lo0201b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0201b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨31,by decide⟩
def hi0201b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨32,by decide⟩
def hi0201 : CheckedMoment :=
  CheckedMoment.ofBessel hi0201b1 hi0201b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0201 : meanBracketCheck (967/10000) lo0201 hi0201=true := by decide +kernel
def bracket0201 : MeanBracket := meanBracketOfMoments (967/10000) lo0201 hi0201 accepted0201
def lo0202b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨36,by decide⟩
def lo0202b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨37,by decide⟩
def lo0202 : CheckedMoment :=
  CheckedMoment.ofBessel lo0202b1 lo0202b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0202b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨41,by decide⟩
def hi0202b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨42,by decide⟩
def hi0202 : CheckedMoment :=
  CheckedMoment.ofBessel hi0202b1 hi0202b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0202 : meanBracketCheck (969/10000) lo0202 hi0202=true := by decide +kernel
def bracket0202 : MeanBracket := meanBracketOfMoments (969/10000) lo0202 hi0202 accepted0202
def lo0203b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨46,by decide⟩
def lo0203b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨47,by decide⟩
def lo0203 : CheckedMoment :=
  CheckedMoment.ofBessel lo0203b1 lo0203b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0203b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨51,by decide⟩
def hi0203b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨52,by decide⟩
def hi0203 : CheckedMoment :=
  CheckedMoment.ofBessel hi0203b1 hi0203b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0203 : meanBracketCheck (971/10000) lo0203 hi0203=true := by decide +kernel
def bracket0203 : MeanBracket := meanBracketOfMoments (971/10000) lo0203 hi0203 accepted0203
def lo0204b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨56,by decide⟩
def lo0204b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨57,by decide⟩
def lo0204 : CheckedMoment :=
  CheckedMoment.ofBessel lo0204b1 lo0204b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0204b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨61,by decide⟩
def hi0204b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0031.rows BesselBatch0031.accepted ⟨62,by decide⟩
def hi0204 : CheckedMoment :=
  CheckedMoment.ofBessel hi0204b1 hi0204b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0204 : meanBracketCheck (973/10000) lo0204 hi0204=true := by decide +kernel
def bracket0204 : MeanBracket := meanBracketOfMoments (973/10000) lo0204 hi0204 accepted0204
def lo0205b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨2,by decide⟩
def lo0205b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨3,by decide⟩
def lo0205 : CheckedMoment :=
  CheckedMoment.ofBessel lo0205b1 lo0205b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0205b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨7,by decide⟩
def hi0205b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨8,by decide⟩
def hi0205 : CheckedMoment :=
  CheckedMoment.ofBessel hi0205b1 hi0205b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0205 : meanBracketCheck (39/400) lo0205 hi0205=true := by decide +kernel
def bracket0205 : MeanBracket := meanBracketOfMoments (39/400) lo0205 hi0205 accepted0205
def lo0206b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨12,by decide⟩
def lo0206b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨13,by decide⟩
def lo0206 : CheckedMoment :=
  CheckedMoment.ofBessel lo0206b1 lo0206b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0206b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨17,by decide⟩
def hi0206b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨18,by decide⟩
def hi0206 : CheckedMoment :=
  CheckedMoment.ofBessel hi0206b1 hi0206b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0206 : meanBracketCheck (977/10000) lo0206 hi0206=true := by decide +kernel
def bracket0206 : MeanBracket := meanBracketOfMoments (977/10000) lo0206 hi0206 accepted0206
def lo0207b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨22,by decide⟩
def lo0207b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨23,by decide⟩
def lo0207 : CheckedMoment :=
  CheckedMoment.ofBessel lo0207b1 lo0207b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0207b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨27,by decide⟩
def hi0207b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨28,by decide⟩
def hi0207 : CheckedMoment :=
  CheckedMoment.ofBessel hi0207b1 hi0207b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0207 : meanBracketCheck (979/10000) lo0207 hi0207=true := by decide +kernel
def bracket0207 : MeanBracket := meanBracketOfMoments (979/10000) lo0207 hi0207 accepted0207
#print axioms bracket0192
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0012
