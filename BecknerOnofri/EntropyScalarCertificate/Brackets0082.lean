import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0205
import BecknerOnofri.EntropyScalarCertificate.Bessel0206
import BecknerOnofri.EntropyScalarCertificate.Bessel0207
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0082
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1312b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨0,by decide⟩
def lo1312b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨1,by decide⟩
def lo1312 : CheckedMoment :=
  CheckedMoment.ofBessel lo1312b1 lo1312b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1312b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨5,by decide⟩
def hi1312b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨6,by decide⟩
def hi1312 : CheckedMoment :=
  CheckedMoment.ofBessel hi1312b1 hi1312b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1312 : meanBracketCheck (397/500) lo1312 hi1312=true := by decide +kernel
def bracket1312 : MeanBracket := meanBracketOfMoments (397/500) lo1312 hi1312 accepted1312
def lo1313b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨10,by decide⟩
def lo1313b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨11,by decide⟩
def lo1313 : CheckedMoment :=
  CheckedMoment.ofBessel lo1313b1 lo1313b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1313b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨15,by decide⟩
def hi1313b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨16,by decide⟩
def hi1313 : CheckedMoment :=
  CheckedMoment.ofBessel hi1313b1 hi1313b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1313 : meanBracketCheck (159/200) lo1313 hi1313=true := by decide +kernel
def bracket1313 : MeanBracket := meanBracketOfMoments (159/200) lo1313 hi1313 accepted1313
def lo1314b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨20,by decide⟩
def lo1314b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨21,by decide⟩
def lo1314 : CheckedMoment :=
  CheckedMoment.ofBessel lo1314b1 lo1314b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1314b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨25,by decide⟩
def hi1314b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨26,by decide⟩
def hi1314 : CheckedMoment :=
  CheckedMoment.ofBessel hi1314b1 hi1314b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1314 : meanBracketCheck (199/250) lo1314 hi1314=true := by decide +kernel
def bracket1314 : MeanBracket := meanBracketOfMoments (199/250) lo1314 hi1314 accepted1314
def lo1315b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨30,by decide⟩
def lo1315b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨31,by decide⟩
def lo1315 : CheckedMoment :=
  CheckedMoment.ofBessel lo1315b1 lo1315b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1315b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨35,by decide⟩
def hi1315b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨36,by decide⟩
def hi1315 : CheckedMoment :=
  CheckedMoment.ofBessel hi1315b1 hi1315b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1315 : meanBracketCheck (797/1000) lo1315 hi1315=true := by decide +kernel
def bracket1315 : MeanBracket := meanBracketOfMoments (797/1000) lo1315 hi1315 accepted1315
def lo1316b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨40,by decide⟩
def lo1316b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨41,by decide⟩
def lo1316 : CheckedMoment :=
  CheckedMoment.ofBessel lo1316b1 lo1316b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1316b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨45,by decide⟩
def hi1316b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨46,by decide⟩
def hi1316 : CheckedMoment :=
  CheckedMoment.ofBessel hi1316b1 hi1316b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1316 : meanBracketCheck (399/500) lo1316 hi1316=true := by decide +kernel
def bracket1316 : MeanBracket := meanBracketOfMoments (399/500) lo1316 hi1316 accepted1316
def lo1317b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨50,by decide⟩
def lo1317b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨51,by decide⟩
def lo1317 : CheckedMoment :=
  CheckedMoment.ofBessel lo1317b1 lo1317b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1317b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨55,by decide⟩
def hi1317b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨56,by decide⟩
def hi1317 : CheckedMoment :=
  CheckedMoment.ofBessel hi1317b1 hi1317b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1317 : meanBracketCheck (799/1000) lo1317 hi1317=true := by decide +kernel
def bracket1317 : MeanBracket := meanBracketOfMoments (799/1000) lo1317 hi1317 accepted1317
def lo1318b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨60,by decide⟩
def lo1318b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨61,by decide⟩
def lo1318 : CheckedMoment :=
  CheckedMoment.ofBessel lo1318b1 lo1318b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1318b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨1,by decide⟩
def hi1318b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨2,by decide⟩
def hi1318 : CheckedMoment :=
  CheckedMoment.ofBessel hi1318b1 hi1318b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1318 : meanBracketCheck (4/5) lo1318 hi1318=true := by decide +kernel
def bracket1318 : MeanBracket := meanBracketOfMoments (4/5) lo1318 hi1318 accepted1318
def lo1319b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨6,by decide⟩
def lo1319b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨7,by decide⟩
def lo1319 : CheckedMoment :=
  CheckedMoment.ofBessel lo1319b1 lo1319b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1319b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨11,by decide⟩
def hi1319b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨12,by decide⟩
def hi1319 : CheckedMoment :=
  CheckedMoment.ofBessel hi1319b1 hi1319b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1319 : meanBracketCheck (1601/2000) lo1319 hi1319=true := by decide +kernel
def bracket1319 : MeanBracket := meanBracketOfMoments (1601/2000) lo1319 hi1319 accepted1319
def lo1320b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨16,by decide⟩
def lo1320b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨17,by decide⟩
def lo1320 : CheckedMoment :=
  CheckedMoment.ofBessel lo1320b1 lo1320b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1320b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨21,by decide⟩
def hi1320b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨22,by decide⟩
def hi1320 : CheckedMoment :=
  CheckedMoment.ofBessel hi1320b1 hi1320b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1320 : meanBracketCheck (801/1000) lo1320 hi1320=true := by decide +kernel
def bracket1320 : MeanBracket := meanBracketOfMoments (801/1000) lo1320 hi1320 accepted1320
def lo1321b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨26,by decide⟩
def lo1321b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨27,by decide⟩
def lo1321 : CheckedMoment :=
  CheckedMoment.ofBessel lo1321b1 lo1321b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1321b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨31,by decide⟩
def hi1321b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨32,by decide⟩
def hi1321 : CheckedMoment :=
  CheckedMoment.ofBessel hi1321b1 hi1321b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1321 : meanBracketCheck (1603/2000) lo1321 hi1321=true := by decide +kernel
def bracket1321 : MeanBracket := meanBracketOfMoments (1603/2000) lo1321 hi1321 accepted1321
def lo1322b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨36,by decide⟩
def lo1322b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨37,by decide⟩
def lo1322 : CheckedMoment :=
  CheckedMoment.ofBessel lo1322b1 lo1322b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1322b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨41,by decide⟩
def hi1322b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨42,by decide⟩
def hi1322 : CheckedMoment :=
  CheckedMoment.ofBessel hi1322b1 hi1322b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1322 : meanBracketCheck (401/500) lo1322 hi1322=true := by decide +kernel
def bracket1322 : MeanBracket := meanBracketOfMoments (401/500) lo1322 hi1322 accepted1322
def lo1323b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨46,by decide⟩
def lo1323b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨47,by decide⟩
def lo1323 : CheckedMoment :=
  CheckedMoment.ofBessel lo1323b1 lo1323b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1323b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨51,by decide⟩
def hi1323b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨52,by decide⟩
def hi1323 : CheckedMoment :=
  CheckedMoment.ofBessel hi1323b1 hi1323b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1323 : meanBracketCheck (321/400) lo1323 hi1323=true := by decide +kernel
def bracket1323 : MeanBracket := meanBracketOfMoments (321/400) lo1323 hi1323 accepted1323
def lo1324b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨56,by decide⟩
def lo1324b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨57,by decide⟩
def lo1324 : CheckedMoment :=
  CheckedMoment.ofBessel lo1324b1 lo1324b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1324b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨61,by decide⟩
def hi1324b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨62,by decide⟩
def hi1324 : CheckedMoment :=
  CheckedMoment.ofBessel hi1324b1 hi1324b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1324 : meanBracketCheck (803/1000) lo1324 hi1324=true := by decide +kernel
def bracket1324 : MeanBracket := meanBracketOfMoments (803/1000) lo1324 hi1324 accepted1324
def lo1325b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨2,by decide⟩
def lo1325b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨3,by decide⟩
def lo1325 : CheckedMoment :=
  CheckedMoment.ofBessel lo1325b1 lo1325b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1325b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨7,by decide⟩
def hi1325b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨8,by decide⟩
def hi1325 : CheckedMoment :=
  CheckedMoment.ofBessel hi1325b1 hi1325b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1325 : meanBracketCheck (1607/2000) lo1325 hi1325=true := by decide +kernel
def bracket1325 : MeanBracket := meanBracketOfMoments (1607/2000) lo1325 hi1325 accepted1325
def lo1326b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨12,by decide⟩
def lo1326b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨13,by decide⟩
def lo1326 : CheckedMoment :=
  CheckedMoment.ofBessel lo1326b1 lo1326b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1326b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨17,by decide⟩
def hi1326b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨18,by decide⟩
def hi1326 : CheckedMoment :=
  CheckedMoment.ofBessel hi1326b1 hi1326b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1326 : meanBracketCheck (201/250) lo1326 hi1326=true := by decide +kernel
def bracket1326 : MeanBracket := meanBracketOfMoments (201/250) lo1326 hi1326 accepted1326
def lo1327b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨22,by decide⟩
def lo1327b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨23,by decide⟩
def lo1327 : CheckedMoment :=
  CheckedMoment.ofBessel lo1327b1 lo1327b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1327b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨27,by decide⟩
def hi1327b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨28,by decide⟩
def hi1327 : CheckedMoment :=
  CheckedMoment.ofBessel hi1327b1 hi1327b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1327 : meanBracketCheck (1609/2000) lo1327 hi1327=true := by decide +kernel
def bracket1327 : MeanBracket := meanBracketOfMoments (1609/2000) lo1327 hi1327 accepted1327
#print axioms bracket1312
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0082
