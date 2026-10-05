module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0190
public import BecknerOnofri.EntropyScalarCertificate.Bessel0191
public import BecknerOnofri.EntropyScalarCertificate.Bessel0192

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0076
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1216b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨0,by decide⟩
def lo1216b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨1,by decide⟩
def lo1216 : CheckedMoment :=
  CheckedMoment.ofBessel lo1216b1 lo1216b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1216b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨5,by decide⟩
def hi1216b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨6,by decide⟩
def hi1216 : CheckedMoment :=
  CheckedMoment.ofBessel hi1216b1 hi1216b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1216 : meanBracketCheck (349/500) lo1216 hi1216=true := by decide +kernel
def bracket1216 : MeanBracket := meanBracketOfMoments (349/500) lo1216 hi1216 accepted1216
def lo1217b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨10,by decide⟩
def lo1217b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨11,by decide⟩
def lo1217 : CheckedMoment :=
  CheckedMoment.ofBessel lo1217b1 lo1217b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1217b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨15,by decide⟩
def hi1217b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨16,by decide⟩
def hi1217 : CheckedMoment :=
  CheckedMoment.ofBessel hi1217b1 hi1217b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1217 : meanBracketCheck (699/1000) lo1217 hi1217=true := by decide +kernel
def bracket1217 : MeanBracket := meanBracketOfMoments (699/1000) lo1217 hi1217 accepted1217
def lo1218b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨20,by decide⟩
def lo1218b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨21,by decide⟩
def lo1218 : CheckedMoment :=
  CheckedMoment.ofBessel lo1218b1 lo1218b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1218b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨25,by decide⟩
def hi1218b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨26,by decide⟩
def hi1218 : CheckedMoment :=
  CheckedMoment.ofBessel hi1218b1 hi1218b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1218 : meanBracketCheck (7/10) lo1218 hi1218=true := by decide +kernel
def bracket1218 : MeanBracket := meanBracketOfMoments (7/10) lo1218 hi1218 accepted1218
def lo1219b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨30,by decide⟩
def lo1219b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨31,by decide⟩
def lo1219 : CheckedMoment :=
  CheckedMoment.ofBessel lo1219b1 lo1219b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1219b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨35,by decide⟩
def hi1219b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨36,by decide⟩
def hi1219 : CheckedMoment :=
  CheckedMoment.ofBessel hi1219b1 hi1219b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1219 : meanBracketCheck (701/1000) lo1219 hi1219=true := by decide +kernel
def bracket1219 : MeanBracket := meanBracketOfMoments (701/1000) lo1219 hi1219 accepted1219
def lo1220b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨40,by decide⟩
def lo1220b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨41,by decide⟩
def lo1220 : CheckedMoment :=
  CheckedMoment.ofBessel lo1220b1 lo1220b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1220b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨45,by decide⟩
def hi1220b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨46,by decide⟩
def hi1220 : CheckedMoment :=
  CheckedMoment.ofBessel hi1220b1 hi1220b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1220 : meanBracketCheck (351/500) lo1220 hi1220=true := by decide +kernel
def bracket1220 : MeanBracket := meanBracketOfMoments (351/500) lo1220 hi1220 accepted1220
def lo1221b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨50,by decide⟩
def lo1221b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨51,by decide⟩
def lo1221 : CheckedMoment :=
  CheckedMoment.ofBessel lo1221b1 lo1221b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1221b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨55,by decide⟩
def hi1221b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨56,by decide⟩
def hi1221 : CheckedMoment :=
  CheckedMoment.ofBessel hi1221b1 hi1221b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1221 : meanBracketCheck (703/1000) lo1221 hi1221=true := by decide +kernel
def bracket1221 : MeanBracket := meanBracketOfMoments (703/1000) lo1221 hi1221 accepted1221
def lo1222b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨60,by decide⟩
def lo1222b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0190.rows BesselBatch0190.accepted ⟨61,by decide⟩
def lo1222 : CheckedMoment :=
  CheckedMoment.ofBessel lo1222b1 lo1222b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1222b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨1,by decide⟩
def hi1222b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨2,by decide⟩
def hi1222 : CheckedMoment :=
  CheckedMoment.ofBessel hi1222b1 hi1222b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1222 : meanBracketCheck (88/125) lo1222 hi1222=true := by decide +kernel
def bracket1222 : MeanBracket := meanBracketOfMoments (88/125) lo1222 hi1222 accepted1222
def lo1223b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨6,by decide⟩
def lo1223b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨7,by decide⟩
def lo1223 : CheckedMoment :=
  CheckedMoment.ofBessel lo1223b1 lo1223b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1223b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨11,by decide⟩
def hi1223b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨12,by decide⟩
def hi1223 : CheckedMoment :=
  CheckedMoment.ofBessel hi1223b1 hi1223b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1223 : meanBracketCheck (141/200) lo1223 hi1223=true := by decide +kernel
def bracket1223 : MeanBracket := meanBracketOfMoments (141/200) lo1223 hi1223 accepted1223
def lo1224b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨16,by decide⟩
def lo1224b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨17,by decide⟩
def lo1224 : CheckedMoment :=
  CheckedMoment.ofBessel lo1224b1 lo1224b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1224b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨21,by decide⟩
def hi1224b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨22,by decide⟩
def hi1224 : CheckedMoment :=
  CheckedMoment.ofBessel hi1224b1 hi1224b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1224 : meanBracketCheck (353/500) lo1224 hi1224=true := by decide +kernel
def bracket1224 : MeanBracket := meanBracketOfMoments (353/500) lo1224 hi1224 accepted1224
def lo1225b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨26,by decide⟩
def lo1225b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨27,by decide⟩
def lo1225 : CheckedMoment :=
  CheckedMoment.ofBessel lo1225b1 lo1225b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1225b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨31,by decide⟩
def hi1225b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨32,by decide⟩
def hi1225 : CheckedMoment :=
  CheckedMoment.ofBessel hi1225b1 hi1225b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1225 : meanBracketCheck (707/1000) lo1225 hi1225=true := by decide +kernel
def bracket1225 : MeanBracket := meanBracketOfMoments (707/1000) lo1225 hi1225 accepted1225
def lo1226b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨36,by decide⟩
def lo1226b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨37,by decide⟩
def lo1226 : CheckedMoment :=
  CheckedMoment.ofBessel lo1226b1 lo1226b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1226b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨41,by decide⟩
def hi1226b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨42,by decide⟩
def hi1226 : CheckedMoment :=
  CheckedMoment.ofBessel hi1226b1 hi1226b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1226 : meanBracketCheck (177/250) lo1226 hi1226=true := by decide +kernel
def bracket1226 : MeanBracket := meanBracketOfMoments (177/250) lo1226 hi1226 accepted1226
def lo1227b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨46,by decide⟩
def lo1227b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨47,by decide⟩
def lo1227 : CheckedMoment :=
  CheckedMoment.ofBessel lo1227b1 lo1227b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1227b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨51,by decide⟩
def hi1227b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨52,by decide⟩
def hi1227 : CheckedMoment :=
  CheckedMoment.ofBessel hi1227b1 hi1227b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1227 : meanBracketCheck (709/1000) lo1227 hi1227=true := by decide +kernel
def bracket1227 : MeanBracket := meanBracketOfMoments (709/1000) lo1227 hi1227 accepted1227
def lo1228b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨56,by decide⟩
def lo1228b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨57,by decide⟩
def lo1228 : CheckedMoment :=
  CheckedMoment.ofBessel lo1228b1 lo1228b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1228b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨61,by decide⟩
def hi1228b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨62,by decide⟩
def hi1228 : CheckedMoment :=
  CheckedMoment.ofBessel hi1228b1 hi1228b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1228 : meanBracketCheck (71/100) lo1228 hi1228=true := by decide +kernel
def bracket1228 : MeanBracket := meanBracketOfMoments (71/100) lo1228 hi1228 accepted1228
def lo1229b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨2,by decide⟩
def lo1229b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨3,by decide⟩
def lo1229 : CheckedMoment :=
  CheckedMoment.ofBessel lo1229b1 lo1229b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1229b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨7,by decide⟩
def hi1229b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨8,by decide⟩
def hi1229 : CheckedMoment :=
  CheckedMoment.ofBessel hi1229b1 hi1229b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1229 : meanBracketCheck (711/1000) lo1229 hi1229=true := by decide +kernel
def bracket1229 : MeanBracket := meanBracketOfMoments (711/1000) lo1229 hi1229 accepted1229
def lo1230b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨12,by decide⟩
def lo1230b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨13,by decide⟩
def lo1230 : CheckedMoment :=
  CheckedMoment.ofBessel lo1230b1 lo1230b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1230b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨17,by decide⟩
def hi1230b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨18,by decide⟩
def hi1230 : CheckedMoment :=
  CheckedMoment.ofBessel hi1230b1 hi1230b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1230 : meanBracketCheck (89/125) lo1230 hi1230=true := by decide +kernel
def bracket1230 : MeanBracket := meanBracketOfMoments (89/125) lo1230 hi1230 accepted1230
def lo1231b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨22,by decide⟩
def lo1231b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨23,by decide⟩
def lo1231 : CheckedMoment :=
  CheckedMoment.ofBessel lo1231b1 lo1231b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1231b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨27,by decide⟩
def hi1231b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨28,by decide⟩
def hi1231 : CheckedMoment :=
  CheckedMoment.ofBessel hi1231b1 hi1231b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1231 : meanBracketCheck (713/1000) lo1231 hi1231=true := by decide +kernel
def bracket1231 : MeanBracket := meanBracketOfMoments (713/1000) lo1231 hi1231 accepted1231
#print axioms bracket1216
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0076
