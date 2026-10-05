module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0182
public import BecknerOnofri.EntropyScalarCertificate.Bessel0183
public import BecknerOnofri.EntropyScalarCertificate.Bessel0184

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0073
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1168b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨32,by decide⟩
def lo1168b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨33,by decide⟩
def lo1168 : CheckedMoment :=
  CheckedMoment.ofBessel lo1168b1 lo1168b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1168b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨37,by decide⟩
def hi1168b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨38,by decide⟩
def hi1168 : CheckedMoment :=
  CheckedMoment.ofBessel hi1168b1 hi1168b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1168 : meanBracketCheck (13/20) lo1168 hi1168=true := by decide +kernel
def bracket1168 : MeanBracket := meanBracketOfMoments (13/20) lo1168 hi1168 accepted1168
def lo1169b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨42,by decide⟩
def lo1169b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨43,by decide⟩
def lo1169 : CheckedMoment :=
  CheckedMoment.ofBessel lo1169b1 lo1169b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1169b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨47,by decide⟩
def hi1169b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨48,by decide⟩
def hi1169 : CheckedMoment :=
  CheckedMoment.ofBessel hi1169b1 hi1169b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1169 : meanBracketCheck (651/1000) lo1169 hi1169=true := by decide +kernel
def bracket1169 : MeanBracket := meanBracketOfMoments (651/1000) lo1169 hi1169 accepted1169
def lo1170b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨52,by decide⟩
def lo1170b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨53,by decide⟩
def lo1170 : CheckedMoment :=
  CheckedMoment.ofBessel lo1170b1 lo1170b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1170b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨57,by decide⟩
def hi1170b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨58,by decide⟩
def hi1170 : CheckedMoment :=
  CheckedMoment.ofBessel hi1170b1 hi1170b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1170 : meanBracketCheck (163/250) lo1170 hi1170=true := by decide +kernel
def bracket1170 : MeanBracket := meanBracketOfMoments (163/250) lo1170 hi1170 accepted1170
def lo1171b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨62,by decide⟩
def lo1171b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0182.rows BesselBatch0182.accepted ⟨63,by decide⟩
def lo1171 : CheckedMoment :=
  CheckedMoment.ofBessel lo1171b1 lo1171b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1171b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨3,by decide⟩
def hi1171b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨4,by decide⟩
def hi1171 : CheckedMoment :=
  CheckedMoment.ofBessel hi1171b1 hi1171b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1171 : meanBracketCheck (653/1000) lo1171 hi1171=true := by decide +kernel
def bracket1171 : MeanBracket := meanBracketOfMoments (653/1000) lo1171 hi1171 accepted1171
def lo1172b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨8,by decide⟩
def lo1172b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨9,by decide⟩
def lo1172 : CheckedMoment :=
  CheckedMoment.ofBessel lo1172b1 lo1172b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1172b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨13,by decide⟩
def hi1172b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨14,by decide⟩
def hi1172 : CheckedMoment :=
  CheckedMoment.ofBessel hi1172b1 hi1172b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1172 : meanBracketCheck (327/500) lo1172 hi1172=true := by decide +kernel
def bracket1172 : MeanBracket := meanBracketOfMoments (327/500) lo1172 hi1172 accepted1172
def lo1173b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨18,by decide⟩
def lo1173b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨19,by decide⟩
def lo1173 : CheckedMoment :=
  CheckedMoment.ofBessel lo1173b1 lo1173b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1173b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨23,by decide⟩
def hi1173b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨24,by decide⟩
def hi1173 : CheckedMoment :=
  CheckedMoment.ofBessel hi1173b1 hi1173b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1173 : meanBracketCheck (131/200) lo1173 hi1173=true := by decide +kernel
def bracket1173 : MeanBracket := meanBracketOfMoments (131/200) lo1173 hi1173 accepted1173
def lo1174b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨28,by decide⟩
def lo1174b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨29,by decide⟩
def lo1174 : CheckedMoment :=
  CheckedMoment.ofBessel lo1174b1 lo1174b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1174b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨33,by decide⟩
def hi1174b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨34,by decide⟩
def hi1174 : CheckedMoment :=
  CheckedMoment.ofBessel hi1174b1 hi1174b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1174 : meanBracketCheck (82/125) lo1174 hi1174=true := by decide +kernel
def bracket1174 : MeanBracket := meanBracketOfMoments (82/125) lo1174 hi1174 accepted1174
def lo1175b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨38,by decide⟩
def lo1175b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨39,by decide⟩
def lo1175 : CheckedMoment :=
  CheckedMoment.ofBessel lo1175b1 lo1175b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1175b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨43,by decide⟩
def hi1175b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨44,by decide⟩
def hi1175 : CheckedMoment :=
  CheckedMoment.ofBessel hi1175b1 hi1175b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1175 : meanBracketCheck (657/1000) lo1175 hi1175=true := by decide +kernel
def bracket1175 : MeanBracket := meanBracketOfMoments (657/1000) lo1175 hi1175 accepted1175
def lo1176b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨48,by decide⟩
def lo1176b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨49,by decide⟩
def lo1176 : CheckedMoment :=
  CheckedMoment.ofBessel lo1176b1 lo1176b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1176b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨53,by decide⟩
def hi1176b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨54,by decide⟩
def hi1176 : CheckedMoment :=
  CheckedMoment.ofBessel hi1176b1 hi1176b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1176 : meanBracketCheck (329/500) lo1176 hi1176=true := by decide +kernel
def bracket1176 : MeanBracket := meanBracketOfMoments (329/500) lo1176 hi1176 accepted1176
def lo1177b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨58,by decide⟩
def lo1177b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨59,by decide⟩
def lo1177 : CheckedMoment :=
  CheckedMoment.ofBessel lo1177b1 lo1177b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1177b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0183.rows BesselBatch0183.accepted ⟨63,by decide⟩
def hi1177b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨0,by decide⟩
def hi1177 : CheckedMoment :=
  CheckedMoment.ofBessel hi1177b1 hi1177b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1177 : meanBracketCheck (659/1000) lo1177 hi1177=true := by decide +kernel
def bracket1177 : MeanBracket := meanBracketOfMoments (659/1000) lo1177 hi1177 accepted1177
def lo1178b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨4,by decide⟩
def lo1178b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨5,by decide⟩
def lo1178 : CheckedMoment :=
  CheckedMoment.ofBessel lo1178b1 lo1178b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1178b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨9,by decide⟩
def hi1178b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨10,by decide⟩
def hi1178 : CheckedMoment :=
  CheckedMoment.ofBessel hi1178b1 hi1178b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1178 : meanBracketCheck (33/50) lo1178 hi1178=true := by decide +kernel
def bracket1178 : MeanBracket := meanBracketOfMoments (33/50) lo1178 hi1178 accepted1178
def lo1179b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨14,by decide⟩
def lo1179b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨15,by decide⟩
def lo1179 : CheckedMoment :=
  CheckedMoment.ofBessel lo1179b1 lo1179b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1179b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨19,by decide⟩
def hi1179b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨20,by decide⟩
def hi1179 : CheckedMoment :=
  CheckedMoment.ofBessel hi1179b1 hi1179b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1179 : meanBracketCheck (661/1000) lo1179 hi1179=true := by decide +kernel
def bracket1179 : MeanBracket := meanBracketOfMoments (661/1000) lo1179 hi1179 accepted1179
def lo1180b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨24,by decide⟩
def lo1180b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨25,by decide⟩
def lo1180 : CheckedMoment :=
  CheckedMoment.ofBessel lo1180b1 lo1180b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1180b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨29,by decide⟩
def hi1180b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨30,by decide⟩
def hi1180 : CheckedMoment :=
  CheckedMoment.ofBessel hi1180b1 hi1180b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1180 : meanBracketCheck (331/500) lo1180 hi1180=true := by decide +kernel
def bracket1180 : MeanBracket := meanBracketOfMoments (331/500) lo1180 hi1180 accepted1180
def lo1181b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨34,by decide⟩
def lo1181b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨35,by decide⟩
def lo1181 : CheckedMoment :=
  CheckedMoment.ofBessel lo1181b1 lo1181b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1181b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨39,by decide⟩
def hi1181b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨40,by decide⟩
def hi1181 : CheckedMoment :=
  CheckedMoment.ofBessel hi1181b1 hi1181b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1181 : meanBracketCheck (663/1000) lo1181 hi1181=true := by decide +kernel
def bracket1181 : MeanBracket := meanBracketOfMoments (663/1000) lo1181 hi1181 accepted1181
def lo1182b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨44,by decide⟩
def lo1182b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨45,by decide⟩
def lo1182 : CheckedMoment :=
  CheckedMoment.ofBessel lo1182b1 lo1182b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1182b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨49,by decide⟩
def hi1182b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨50,by decide⟩
def hi1182 : CheckedMoment :=
  CheckedMoment.ofBessel hi1182b1 hi1182b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1182 : meanBracketCheck (83/125) lo1182 hi1182=true := by decide +kernel
def bracket1182 : MeanBracket := meanBracketOfMoments (83/125) lo1182 hi1182 accepted1182
def lo1183b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨54,by decide⟩
def lo1183b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨55,by decide⟩
def lo1183 : CheckedMoment :=
  CheckedMoment.ofBessel lo1183b1 lo1183b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1183b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨59,by decide⟩
def hi1183b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0184.rows BesselBatch0184.accepted ⟨60,by decide⟩
def hi1183 : CheckedMoment :=
  CheckedMoment.ofBessel hi1183b1 hi1183b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1183 : meanBracketCheck (133/200) lo1183 hi1183=true := by decide +kernel
def bracket1183 : MeanBracket := meanBracketOfMoments (133/200) lo1183 hi1183 accepted1183
#print axioms bracket1168
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0073
