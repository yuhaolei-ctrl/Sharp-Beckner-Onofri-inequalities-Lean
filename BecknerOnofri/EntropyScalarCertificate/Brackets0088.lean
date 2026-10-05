import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0220
import BecknerOnofri.EntropyScalarCertificate.Bessel0221
import BecknerOnofri.EntropyScalarCertificate.Bessel0222
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0088
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1408b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨0,by decide⟩
def lo1408b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨1,by decide⟩
def lo1408 : CheckedMoment :=
  CheckedMoment.ofBessel lo1408b1 lo1408b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1408b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨5,by decide⟩
def hi1408b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨6,by decide⟩
def hi1408 : CheckedMoment :=
  CheckedMoment.ofBessel hi1408b1 hi1408b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1408 : meanBracketCheck (833/1000) lo1408 hi1408=true := by decide +kernel
def bracket1408 : MeanBracket := meanBracketOfMoments (833/1000) lo1408 hi1408 accepted1408
def lo1409b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨10,by decide⟩
def lo1409b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨11,by decide⟩
def lo1409 : CheckedMoment :=
  CheckedMoment.ofBessel lo1409b1 lo1409b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1409b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨15,by decide⟩
def hi1409b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨16,by decide⟩
def hi1409 : CheckedMoment :=
  CheckedMoment.ofBessel hi1409b1 hi1409b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1409 : meanBracketCheck (8331/10000) lo1409 hi1409=true := by decide +kernel
def bracket1409 : MeanBracket := meanBracketOfMoments (8331/10000) lo1409 hi1409 accepted1409
def lo1410b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨20,by decide⟩
def lo1410b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨21,by decide⟩
def lo1410 : CheckedMoment :=
  CheckedMoment.ofBessel lo1410b1 lo1410b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1410b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨25,by decide⟩
def hi1410b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨26,by decide⟩
def hi1410 : CheckedMoment :=
  CheckedMoment.ofBessel hi1410b1 hi1410b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1410 : meanBracketCheck (2083/2500) lo1410 hi1410=true := by decide +kernel
def bracket1410 : MeanBracket := meanBracketOfMoments (2083/2500) lo1410 hi1410 accepted1410
def lo1411b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨30,by decide⟩
def lo1411b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨31,by decide⟩
def lo1411 : CheckedMoment :=
  CheckedMoment.ofBessel lo1411b1 lo1411b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1411b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨35,by decide⟩
def hi1411b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨36,by decide⟩
def hi1411 : CheckedMoment :=
  CheckedMoment.ofBessel hi1411b1 hi1411b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1411 : meanBracketCheck (8333/10000) lo1411 hi1411=true := by decide +kernel
def bracket1411 : MeanBracket := meanBracketOfMoments (8333/10000) lo1411 hi1411 accepted1411
def lo1412b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨40,by decide⟩
def lo1412b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨41,by decide⟩
def lo1412 : CheckedMoment :=
  CheckedMoment.ofBessel lo1412b1 lo1412b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1412b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨45,by decide⟩
def hi1412b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨46,by decide⟩
def hi1412 : CheckedMoment :=
  CheckedMoment.ofBessel hi1412b1 hi1412b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1412 : meanBracketCheck (4167/5000) lo1412 hi1412=true := by decide +kernel
def bracket1412 : MeanBracket := meanBracketOfMoments (4167/5000) lo1412 hi1412 accepted1412
def lo1413b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨50,by decide⟩
def lo1413b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨51,by decide⟩
def lo1413 : CheckedMoment :=
  CheckedMoment.ofBessel lo1413b1 lo1413b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1413b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨55,by decide⟩
def hi1413b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨56,by decide⟩
def hi1413 : CheckedMoment :=
  CheckedMoment.ofBessel hi1413b1 hi1413b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1413 : meanBracketCheck (1667/2000) lo1413 hi1413=true := by decide +kernel
def bracket1413 : MeanBracket := meanBracketOfMoments (1667/2000) lo1413 hi1413 accepted1413
def lo1414b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨60,by decide⟩
def lo1414b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨61,by decide⟩
def lo1414 : CheckedMoment :=
  CheckedMoment.ofBessel lo1414b1 lo1414b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1414b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨1,by decide⟩
def hi1414b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨2,by decide⟩
def hi1414 : CheckedMoment :=
  CheckedMoment.ofBessel hi1414b1 hi1414b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1414 : meanBracketCheck (521/625) lo1414 hi1414=true := by decide +kernel
def bracket1414 : MeanBracket := meanBracketOfMoments (521/625) lo1414 hi1414 accepted1414
def lo1415b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨6,by decide⟩
def lo1415b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨7,by decide⟩
def lo1415 : CheckedMoment :=
  CheckedMoment.ofBessel lo1415b1 lo1415b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1415b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨11,by decide⟩
def hi1415b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨12,by decide⟩
def hi1415 : CheckedMoment :=
  CheckedMoment.ofBessel hi1415b1 hi1415b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1415 : meanBracketCheck (8337/10000) lo1415 hi1415=true := by decide +kernel
def bracket1415 : MeanBracket := meanBracketOfMoments (8337/10000) lo1415 hi1415 accepted1415
def lo1416b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨16,by decide⟩
def lo1416b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨17,by decide⟩
def lo1416 : CheckedMoment :=
  CheckedMoment.ofBessel lo1416b1 lo1416b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1416b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨21,by decide⟩
def hi1416b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨22,by decide⟩
def hi1416 : CheckedMoment :=
  CheckedMoment.ofBessel hi1416b1 hi1416b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1416 : meanBracketCheck (4169/5000) lo1416 hi1416=true := by decide +kernel
def bracket1416 : MeanBracket := meanBracketOfMoments (4169/5000) lo1416 hi1416 accepted1416
def lo1417b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨26,by decide⟩
def lo1417b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨27,by decide⟩
def lo1417 : CheckedMoment :=
  CheckedMoment.ofBessel lo1417b1 lo1417b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1417b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨31,by decide⟩
def hi1417b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨32,by decide⟩
def hi1417 : CheckedMoment :=
  CheckedMoment.ofBessel hi1417b1 hi1417b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1417 : meanBracketCheck (8339/10000) lo1417 hi1417=true := by decide +kernel
def bracket1417 : MeanBracket := meanBracketOfMoments (8339/10000) lo1417 hi1417 accepted1417
def lo1418b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨36,by decide⟩
def lo1418b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨37,by decide⟩
def lo1418 : CheckedMoment :=
  CheckedMoment.ofBessel lo1418b1 lo1418b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1418b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨41,by decide⟩
def hi1418b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨42,by decide⟩
def hi1418 : CheckedMoment :=
  CheckedMoment.ofBessel hi1418b1 hi1418b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1418 : meanBracketCheck (417/500) lo1418 hi1418=true := by decide +kernel
def bracket1418 : MeanBracket := meanBracketOfMoments (417/500) lo1418 hi1418 accepted1418
def lo1419b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨46,by decide⟩
def lo1419b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨47,by decide⟩
def lo1419 : CheckedMoment :=
  CheckedMoment.ofBessel lo1419b1 lo1419b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1419b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨51,by decide⟩
def hi1419b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨52,by decide⟩
def hi1419 : CheckedMoment :=
  CheckedMoment.ofBessel hi1419b1 hi1419b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1419 : meanBracketCheck (8341/10000) lo1419 hi1419=true := by decide +kernel
def bracket1419 : MeanBracket := meanBracketOfMoments (8341/10000) lo1419 hi1419 accepted1419
def lo1420b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨56,by decide⟩
def lo1420b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨57,by decide⟩
def lo1420 : CheckedMoment :=
  CheckedMoment.ofBessel lo1420b1 lo1420b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1420b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨61,by decide⟩
def hi1420b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨62,by decide⟩
def hi1420 : CheckedMoment :=
  CheckedMoment.ofBessel hi1420b1 hi1420b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1420 : meanBracketCheck (4171/5000) lo1420 hi1420=true := by decide +kernel
def bracket1420 : MeanBracket := meanBracketOfMoments (4171/5000) lo1420 hi1420 accepted1420
def lo1421b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨2,by decide⟩
def lo1421b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨3,by decide⟩
def lo1421 : CheckedMoment :=
  CheckedMoment.ofBessel lo1421b1 lo1421b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1421b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨7,by decide⟩
def hi1421b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨8,by decide⟩
def hi1421 : CheckedMoment :=
  CheckedMoment.ofBessel hi1421b1 hi1421b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1421 : meanBracketCheck (8343/10000) lo1421 hi1421=true := by decide +kernel
def bracket1421 : MeanBracket := meanBracketOfMoments (8343/10000) lo1421 hi1421 accepted1421
def lo1422b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨12,by decide⟩
def lo1422b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨13,by decide⟩
def lo1422 : CheckedMoment :=
  CheckedMoment.ofBessel lo1422b1 lo1422b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1422b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨17,by decide⟩
def hi1422b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨18,by decide⟩
def hi1422 : CheckedMoment :=
  CheckedMoment.ofBessel hi1422b1 hi1422b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1422 : meanBracketCheck (1043/1250) lo1422 hi1422=true := by decide +kernel
def bracket1422 : MeanBracket := meanBracketOfMoments (1043/1250) lo1422 hi1422 accepted1422
def lo1423b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨22,by decide⟩
def lo1423b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨23,by decide⟩
def lo1423 : CheckedMoment :=
  CheckedMoment.ofBessel lo1423b1 lo1423b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1423b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨27,by decide⟩
def hi1423b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨28,by decide⟩
def hi1423 : CheckedMoment :=
  CheckedMoment.ofBessel hi1423b1 hi1423b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1423 : meanBracketCheck (1669/2000) lo1423 hi1423=true := by decide +kernel
def bracket1423 : MeanBracket := meanBracketOfMoments (1669/2000) lo1423 hi1423 accepted1423
#print axioms bracket1408
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0088
