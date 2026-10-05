import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0025
import BecknerOnofri.EntropyScalarCertificate.Bessel0026
import BecknerOnofri.EntropyScalarCertificate.Bessel0027
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0010
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0160b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨0,by decide⟩
def lo0160b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨1,by decide⟩
def lo0160 : CheckedMoment :=
  CheckedMoment.ofBessel lo0160b1 lo0160b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0160b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨5,by decide⟩
def hi0160b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨6,by decide⟩
def hi0160 : CheckedMoment :=
  CheckedMoment.ofBessel hi0160b1 hi0160b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0160 : meanBracketCheck (177/2000) lo0160 hi0160=true := by decide +kernel
def bracket0160 : MeanBracket := meanBracketOfMoments (177/2000) lo0160 hi0160 accepted0160
def lo0161b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨10,by decide⟩
def lo0161b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨11,by decide⟩
def lo0161 : CheckedMoment :=
  CheckedMoment.ofBessel lo0161b1 lo0161b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0161b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨15,by decide⟩
def hi0161b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨16,by decide⟩
def hi0161 : CheckedMoment :=
  CheckedMoment.ofBessel hi0161b1 hi0161b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0161 : meanBracketCheck (887/10000) lo0161 hi0161=true := by decide +kernel
def bracket0161 : MeanBracket := meanBracketOfMoments (887/10000) lo0161 hi0161 accepted0161
def lo0162b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨20,by decide⟩
def lo0162b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨21,by decide⟩
def lo0162 : CheckedMoment :=
  CheckedMoment.ofBessel lo0162b1 lo0162b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0162b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨25,by decide⟩
def hi0162b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨26,by decide⟩
def hi0162 : CheckedMoment :=
  CheckedMoment.ofBessel hi0162b1 hi0162b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0162 : meanBracketCheck (889/10000) lo0162 hi0162=true := by decide +kernel
def bracket0162 : MeanBracket := meanBracketOfMoments (889/10000) lo0162 hi0162 accepted0162
def lo0163b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨30,by decide⟩
def lo0163b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨31,by decide⟩
def lo0163 : CheckedMoment :=
  CheckedMoment.ofBessel lo0163b1 lo0163b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0163b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨35,by decide⟩
def hi0163b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨36,by decide⟩
def hi0163 : CheckedMoment :=
  CheckedMoment.ofBessel hi0163b1 hi0163b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0163 : meanBracketCheck (891/10000) lo0163 hi0163=true := by decide +kernel
def bracket0163 : MeanBracket := meanBracketOfMoments (891/10000) lo0163 hi0163 accepted0163
def lo0164b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨40,by decide⟩
def lo0164b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨41,by decide⟩
def lo0164 : CheckedMoment :=
  CheckedMoment.ofBessel lo0164b1 lo0164b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0164b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨45,by decide⟩
def hi0164b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨46,by decide⟩
def hi0164 : CheckedMoment :=
  CheckedMoment.ofBessel hi0164b1 hi0164b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0164 : meanBracketCheck (893/10000) lo0164 hi0164=true := by decide +kernel
def bracket0164 : MeanBracket := meanBracketOfMoments (893/10000) lo0164 hi0164 accepted0164
def lo0165b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨50,by decide⟩
def lo0165b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨51,by decide⟩
def lo0165 : CheckedMoment :=
  CheckedMoment.ofBessel lo0165b1 lo0165b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0165b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨55,by decide⟩
def hi0165b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨56,by decide⟩
def hi0165 : CheckedMoment :=
  CheckedMoment.ofBessel hi0165b1 hi0165b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0165 : meanBracketCheck (179/2000) lo0165 hi0165=true := by decide +kernel
def bracket0165 : MeanBracket := meanBracketOfMoments (179/2000) lo0165 hi0165 accepted0165
def lo0166b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨60,by decide⟩
def lo0166b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨61,by decide⟩
def lo0166 : CheckedMoment :=
  CheckedMoment.ofBessel lo0166b1 lo0166b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0166b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨1,by decide⟩
def hi0166b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨2,by decide⟩
def hi0166 : CheckedMoment :=
  CheckedMoment.ofBessel hi0166b1 hi0166b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0166 : meanBracketCheck (897/10000) lo0166 hi0166=true := by decide +kernel
def bracket0166 : MeanBracket := meanBracketOfMoments (897/10000) lo0166 hi0166 accepted0166
def lo0167b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨6,by decide⟩
def lo0167b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨7,by decide⟩
def lo0167 : CheckedMoment :=
  CheckedMoment.ofBessel lo0167b1 lo0167b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0167b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨11,by decide⟩
def hi0167b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨12,by decide⟩
def hi0167 : CheckedMoment :=
  CheckedMoment.ofBessel hi0167b1 hi0167b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0167 : meanBracketCheck (899/10000) lo0167 hi0167=true := by decide +kernel
def bracket0167 : MeanBracket := meanBracketOfMoments (899/10000) lo0167 hi0167 accepted0167
def lo0168b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨16,by decide⟩
def lo0168b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨17,by decide⟩
def lo0168 : CheckedMoment :=
  CheckedMoment.ofBessel lo0168b1 lo0168b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0168b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨21,by decide⟩
def hi0168b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨22,by decide⟩
def hi0168 : CheckedMoment :=
  CheckedMoment.ofBessel hi0168b1 hi0168b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0168 : meanBracketCheck (901/10000) lo0168 hi0168=true := by decide +kernel
def bracket0168 : MeanBracket := meanBracketOfMoments (901/10000) lo0168 hi0168 accepted0168
def lo0169b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨26,by decide⟩
def lo0169b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨27,by decide⟩
def lo0169 : CheckedMoment :=
  CheckedMoment.ofBessel lo0169b1 lo0169b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0169b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨31,by decide⟩
def hi0169b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨32,by decide⟩
def hi0169 : CheckedMoment :=
  CheckedMoment.ofBessel hi0169b1 hi0169b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0169 : meanBracketCheck (903/10000) lo0169 hi0169=true := by decide +kernel
def bracket0169 : MeanBracket := meanBracketOfMoments (903/10000) lo0169 hi0169 accepted0169
def lo0170b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨36,by decide⟩
def lo0170b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨37,by decide⟩
def lo0170 : CheckedMoment :=
  CheckedMoment.ofBessel lo0170b1 lo0170b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0170b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨41,by decide⟩
def hi0170b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨42,by decide⟩
def hi0170 : CheckedMoment :=
  CheckedMoment.ofBessel hi0170b1 hi0170b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0170 : meanBracketCheck (181/2000) lo0170 hi0170=true := by decide +kernel
def bracket0170 : MeanBracket := meanBracketOfMoments (181/2000) lo0170 hi0170 accepted0170
def lo0171b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨46,by decide⟩
def lo0171b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨47,by decide⟩
def lo0171 : CheckedMoment :=
  CheckedMoment.ofBessel lo0171b1 lo0171b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0171b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨51,by decide⟩
def hi0171b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨52,by decide⟩
def hi0171 : CheckedMoment :=
  CheckedMoment.ofBessel hi0171b1 hi0171b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0171 : meanBracketCheck (907/10000) lo0171 hi0171=true := by decide +kernel
def bracket0171 : MeanBracket := meanBracketOfMoments (907/10000) lo0171 hi0171 accepted0171
def lo0172b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨56,by decide⟩
def lo0172b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨57,by decide⟩
def lo0172 : CheckedMoment :=
  CheckedMoment.ofBessel lo0172b1 lo0172b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0172b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨61,by decide⟩
def hi0172b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨62,by decide⟩
def hi0172 : CheckedMoment :=
  CheckedMoment.ofBessel hi0172b1 hi0172b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0172 : meanBracketCheck (909/10000) lo0172 hi0172=true := by decide +kernel
def bracket0172 : MeanBracket := meanBracketOfMoments (909/10000) lo0172 hi0172 accepted0172
def lo0173b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨2,by decide⟩
def lo0173b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨3,by decide⟩
def lo0173 : CheckedMoment :=
  CheckedMoment.ofBessel lo0173b1 lo0173b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0173b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨7,by decide⟩
def hi0173b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨8,by decide⟩
def hi0173 : CheckedMoment :=
  CheckedMoment.ofBessel hi0173b1 hi0173b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0173 : meanBracketCheck (911/10000) lo0173 hi0173=true := by decide +kernel
def bracket0173 : MeanBracket := meanBracketOfMoments (911/10000) lo0173 hi0173 accepted0173
def lo0174b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨12,by decide⟩
def lo0174b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨13,by decide⟩
def lo0174 : CheckedMoment :=
  CheckedMoment.ofBessel lo0174b1 lo0174b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0174b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨17,by decide⟩
def hi0174b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨18,by decide⟩
def hi0174 : CheckedMoment :=
  CheckedMoment.ofBessel hi0174b1 hi0174b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0174 : meanBracketCheck (913/10000) lo0174 hi0174=true := by decide +kernel
def bracket0174 : MeanBracket := meanBracketOfMoments (913/10000) lo0174 hi0174 accepted0174
def lo0175b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨22,by decide⟩
def lo0175b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨23,by decide⟩
def lo0175 : CheckedMoment :=
  CheckedMoment.ofBessel lo0175b1 lo0175b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0175b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨27,by decide⟩
def hi0175b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨28,by decide⟩
def hi0175 : CheckedMoment :=
  CheckedMoment.ofBessel hi0175b1 hi0175b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0175 : meanBracketCheck (183/2000) lo0175 hi0175=true := by decide +kernel
def bracket0175 : MeanBracket := meanBracketOfMoments (183/2000) lo0175 hi0175 accepted0175
#print axioms bracket0160
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0010
