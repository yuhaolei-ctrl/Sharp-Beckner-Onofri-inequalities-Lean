module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0180
public import BecknerOnofri.EntropyScalarCertificate.Bessel0181
public import BecknerOnofri.EntropyScalarCertificate.Bessel0182

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0072
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1152b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨0,by decide⟩
def lo1152b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨1,by decide⟩
def lo1152 : CheckedMoment :=
  CheckedMoment.ofBessel lo1152b1 lo1152b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1152b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨5,by decide⟩
def hi1152b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨6,by decide⟩
def hi1152 : CheckedMoment :=
  CheckedMoment.ofBessel hi1152b1 hi1152b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1152 : meanBracketCheck (317/500) lo1152 hi1152=true := by decide +kernel
def bracket1152 : MeanBracket := meanBracketOfMoments (317/500) lo1152 hi1152 accepted1152
def lo1153b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨10,by decide⟩
def lo1153b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨11,by decide⟩
def lo1153 : CheckedMoment :=
  CheckedMoment.ofBessel lo1153b1 lo1153b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1153b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨15,by decide⟩
def hi1153b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨16,by decide⟩
def hi1153 : CheckedMoment :=
  CheckedMoment.ofBessel hi1153b1 hi1153b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1153 : meanBracketCheck (127/200) lo1153 hi1153=true := by decide +kernel
def bracket1153 : MeanBracket := meanBracketOfMoments (127/200) lo1153 hi1153 accepted1153
def lo1154b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨20,by decide⟩
def lo1154b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨21,by decide⟩
def lo1154 : CheckedMoment :=
  CheckedMoment.ofBessel lo1154b1 lo1154b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1154b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨25,by decide⟩
def hi1154b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨26,by decide⟩
def hi1154 : CheckedMoment :=
  CheckedMoment.ofBessel hi1154b1 hi1154b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1154 : meanBracketCheck (159/250) lo1154 hi1154=true := by decide +kernel
def bracket1154 : MeanBracket := meanBracketOfMoments (159/250) lo1154 hi1154 accepted1154
def lo1155b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨30,by decide⟩
def lo1155b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨31,by decide⟩
def lo1155 : CheckedMoment :=
  CheckedMoment.ofBessel lo1155b1 lo1155b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1155b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨35,by decide⟩
def hi1155b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨36,by decide⟩
def hi1155 : CheckedMoment :=
  CheckedMoment.ofBessel hi1155b1 hi1155b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1155 : meanBracketCheck (637/1000) lo1155 hi1155=true := by decide +kernel
def bracket1155 : MeanBracket := meanBracketOfMoments (637/1000) lo1155 hi1155 accepted1155
def lo1156b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨40,by decide⟩
def lo1156b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨41,by decide⟩
def lo1156 : CheckedMoment :=
  CheckedMoment.ofBessel lo1156b1 lo1156b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1156b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨45,by decide⟩
def hi1156b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨46,by decide⟩
def hi1156 : CheckedMoment :=
  CheckedMoment.ofBessel hi1156b1 hi1156b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1156 : meanBracketCheck (319/500) lo1156 hi1156=true := by decide +kernel
def bracket1156 : MeanBracket := meanBracketOfMoments (319/500) lo1156 hi1156 accepted1156
def lo1157b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨50,by decide⟩
def lo1157b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨51,by decide⟩
def lo1157 : CheckedMoment :=
  CheckedMoment.ofBessel lo1157b1 lo1157b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1157b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨55,by decide⟩
def hi1157b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨56,by decide⟩
def hi1157 : CheckedMoment :=
  CheckedMoment.ofBessel hi1157b1 hi1157b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1157 : meanBracketCheck (639/1000) lo1157 hi1157=true := by decide +kernel
def bracket1157 : MeanBracket := meanBracketOfMoments (639/1000) lo1157 hi1157 accepted1157
def lo1158b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨60,by decide⟩
def lo1158b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨61,by decide⟩
def lo1158 : CheckedMoment :=
  CheckedMoment.ofBessel lo1158b1 lo1158b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1158b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨1,by decide⟩
def hi1158b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨2,by decide⟩
def hi1158 : CheckedMoment :=
  CheckedMoment.ofBessel hi1158b1 hi1158b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1158 : meanBracketCheck (16/25) lo1158 hi1158=true := by decide +kernel
def bracket1158 : MeanBracket := meanBracketOfMoments (16/25) lo1158 hi1158 accepted1158
def lo1159b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨6,by decide⟩
def lo1159b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨7,by decide⟩
def lo1159 : CheckedMoment :=
  CheckedMoment.ofBessel lo1159b1 lo1159b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1159b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨11,by decide⟩
def hi1159b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨12,by decide⟩
def hi1159 : CheckedMoment :=
  CheckedMoment.ofBessel hi1159b1 hi1159b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1159 : meanBracketCheck (641/1000) lo1159 hi1159=true := by decide +kernel
def bracket1159 : MeanBracket := meanBracketOfMoments (641/1000) lo1159 hi1159 accepted1159
def lo1160b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨16,by decide⟩
def lo1160b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨17,by decide⟩
def lo1160 : CheckedMoment :=
  CheckedMoment.ofBessel lo1160b1 lo1160b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1160b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨21,by decide⟩
def hi1160b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨22,by decide⟩
def hi1160 : CheckedMoment :=
  CheckedMoment.ofBessel hi1160b1 hi1160b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1160 : meanBracketCheck (321/500) lo1160 hi1160=true := by decide +kernel
def bracket1160 : MeanBracket := meanBracketOfMoments (321/500) lo1160 hi1160 accepted1160
def lo1161b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨26,by decide⟩
def lo1161b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨27,by decide⟩
def lo1161 : CheckedMoment :=
  CheckedMoment.ofBessel lo1161b1 lo1161b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1161b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨31,by decide⟩
def hi1161b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨32,by decide⟩
def hi1161 : CheckedMoment :=
  CheckedMoment.ofBessel hi1161b1 hi1161b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1161 : meanBracketCheck (643/1000) lo1161 hi1161=true := by decide +kernel
def bracket1161 : MeanBracket := meanBracketOfMoments (643/1000) lo1161 hi1161 accepted1161
def lo1162b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨36,by decide⟩
def lo1162b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨37,by decide⟩
def lo1162 : CheckedMoment :=
  CheckedMoment.ofBessel lo1162b1 lo1162b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1162b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨41,by decide⟩
def hi1162b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨42,by decide⟩
def hi1162 : CheckedMoment :=
  CheckedMoment.ofBessel hi1162b1 hi1162b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1162 : meanBracketCheck (161/250) lo1162 hi1162=true := by decide +kernel
def bracket1162 : MeanBracket := meanBracketOfMoments (161/250) lo1162 hi1162 accepted1162
def lo1163b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨46,by decide⟩
def lo1163b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨47,by decide⟩
def lo1163 : CheckedMoment :=
  CheckedMoment.ofBessel lo1163b1 lo1163b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1163b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨51,by decide⟩
def hi1163b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨52,by decide⟩
def hi1163 : CheckedMoment :=
  CheckedMoment.ofBessel hi1163b1 hi1163b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1163 : meanBracketCheck (129/200) lo1163 hi1163=true := by decide +kernel
def bracket1163 : MeanBracket := meanBracketOfMoments (129/200) lo1163 hi1163 accepted1163
def lo1164b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨56,by decide⟩
def lo1164b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨57,by decide⟩
def lo1164 : CheckedMoment :=
  CheckedMoment.ofBessel lo1164b1 lo1164b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1164b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨61,by decide⟩
def hi1164b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨62,by decide⟩
def hi1164 : CheckedMoment :=
  CheckedMoment.ofBessel hi1164b1 hi1164b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1164 : meanBracketCheck (323/500) lo1164 hi1164=true := by decide +kernel
def bracket1164 : MeanBracket := meanBracketOfMoments (323/500) lo1164 hi1164 accepted1164
def lo1165b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨2,by decide⟩
def lo1165b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨3,by decide⟩
def lo1165 : CheckedMoment :=
  CheckedMoment.ofBessel lo1165b1 lo1165b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1165b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨7,by decide⟩
def hi1165b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨8,by decide⟩
def hi1165 : CheckedMoment :=
  CheckedMoment.ofBessel hi1165b1 hi1165b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1165 : meanBracketCheck (647/1000) lo1165 hi1165=true := by decide +kernel
def bracket1165 : MeanBracket := meanBracketOfMoments (647/1000) lo1165 hi1165 accepted1165
def lo1166b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨12,by decide⟩
def lo1166b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨13,by decide⟩
def lo1166 : CheckedMoment :=
  CheckedMoment.ofBessel lo1166b1 lo1166b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1166b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨17,by decide⟩
def hi1166b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨18,by decide⟩
def hi1166 : CheckedMoment :=
  CheckedMoment.ofBessel hi1166b1 hi1166b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1166 : meanBracketCheck (81/125) lo1166 hi1166=true := by decide +kernel
def bracket1166 : MeanBracket := meanBracketOfMoments (81/125) lo1166 hi1166 accepted1166
def lo1167b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨22,by decide⟩
def lo1167b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨23,by decide⟩
def lo1167 : CheckedMoment :=
  CheckedMoment.ofBessel lo1167b1 lo1167b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1167b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨27,by decide⟩
def hi1167b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨28,by decide⟩
def hi1167 : CheckedMoment :=
  CheckedMoment.ofBessel hi1167b1 hi1167b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1167 : meanBracketCheck (649/1000) lo1167 hi1167=true := by decide +kernel
def bracket1167 : MeanBracket := meanBracketOfMoments (649/1000) lo1167 hi1167 accepted1167
#print axioms bracket1152
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0072
