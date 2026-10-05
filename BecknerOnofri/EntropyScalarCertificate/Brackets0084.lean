module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0210
public import BecknerOnofri.EntropyScalarCertificate.Bessel0211
public import BecknerOnofri.EntropyScalarCertificate.Bessel0212

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0084
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1344b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨0,by decide⟩
def lo1344b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨1,by decide⟩
def lo1344 : CheckedMoment :=
  CheckedMoment.ofBessel lo1344b1 lo1344b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1344b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨5,by decide⟩
def hi1344b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨6,by decide⟩
def hi1344 : CheckedMoment :=
  CheckedMoment.ofBessel hi1344b1 hi1344b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1344 : meanBracketCheck (813/1000) lo1344 hi1344=true := by decide +kernel
def bracket1344 : MeanBracket := meanBracketOfMoments (813/1000) lo1344 hi1344 accepted1344
def lo1345b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨10,by decide⟩
def lo1345b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨11,by decide⟩
def lo1345 : CheckedMoment :=
  CheckedMoment.ofBessel lo1345b1 lo1345b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1345b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨15,by decide⟩
def hi1345b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨16,by decide⟩
def hi1345 : CheckedMoment :=
  CheckedMoment.ofBessel hi1345b1 hi1345b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1345 : meanBracketCheck (1627/2000) lo1345 hi1345=true := by decide +kernel
def bracket1345 : MeanBracket := meanBracketOfMoments (1627/2000) lo1345 hi1345 accepted1345
def lo1346b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨20,by decide⟩
def lo1346b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨21,by decide⟩
def lo1346 : CheckedMoment :=
  CheckedMoment.ofBessel lo1346b1 lo1346b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1346b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨25,by decide⟩
def hi1346b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨26,by decide⟩
def hi1346 : CheckedMoment :=
  CheckedMoment.ofBessel hi1346b1 hi1346b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1346 : meanBracketCheck (407/500) lo1346 hi1346=true := by decide +kernel
def bracket1346 : MeanBracket := meanBracketOfMoments (407/500) lo1346 hi1346 accepted1346
def lo1347b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨30,by decide⟩
def lo1347b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨31,by decide⟩
def lo1347 : CheckedMoment :=
  CheckedMoment.ofBessel lo1347b1 lo1347b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1347b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨35,by decide⟩
def hi1347b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨36,by decide⟩
def hi1347 : CheckedMoment :=
  CheckedMoment.ofBessel hi1347b1 hi1347b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1347 : meanBracketCheck (1629/2000) lo1347 hi1347=true := by decide +kernel
def bracket1347 : MeanBracket := meanBracketOfMoments (1629/2000) lo1347 hi1347 accepted1347
def lo1348b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨40,by decide⟩
def lo1348b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨41,by decide⟩
def lo1348 : CheckedMoment :=
  CheckedMoment.ofBessel lo1348b1 lo1348b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1348b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨45,by decide⟩
def hi1348b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨46,by decide⟩
def hi1348 : CheckedMoment :=
  CheckedMoment.ofBessel hi1348b1 hi1348b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1348 : meanBracketCheck (163/200) lo1348 hi1348=true := by decide +kernel
def bracket1348 : MeanBracket := meanBracketOfMoments (163/200) lo1348 hi1348 accepted1348
def lo1349b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨50,by decide⟩
def lo1349b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨51,by decide⟩
def lo1349 : CheckedMoment :=
  CheckedMoment.ofBessel lo1349b1 lo1349b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1349b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨55,by decide⟩
def hi1349b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨56,by decide⟩
def hi1349 : CheckedMoment :=
  CheckedMoment.ofBessel hi1349b1 hi1349b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1349 : meanBracketCheck (1631/2000) lo1349 hi1349=true := by decide +kernel
def bracket1349 : MeanBracket := meanBracketOfMoments (1631/2000) lo1349 hi1349 accepted1349
def lo1350b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨60,by decide⟩
def lo1350b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨61,by decide⟩
def lo1350 : CheckedMoment :=
  CheckedMoment.ofBessel lo1350b1 lo1350b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1350b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨1,by decide⟩
def hi1350b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨2,by decide⟩
def hi1350 : CheckedMoment :=
  CheckedMoment.ofBessel hi1350b1 hi1350b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1350 : meanBracketCheck (102/125) lo1350 hi1350=true := by decide +kernel
def bracket1350 : MeanBracket := meanBracketOfMoments (102/125) lo1350 hi1350 accepted1350
def lo1351b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨6,by decide⟩
def lo1351b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨7,by decide⟩
def lo1351 : CheckedMoment :=
  CheckedMoment.ofBessel lo1351b1 lo1351b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1351b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨11,by decide⟩
def hi1351b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨12,by decide⟩
def hi1351 : CheckedMoment :=
  CheckedMoment.ofBessel hi1351b1 hi1351b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1351 : meanBracketCheck (1633/2000) lo1351 hi1351=true := by decide +kernel
def bracket1351 : MeanBracket := meanBracketOfMoments (1633/2000) lo1351 hi1351 accepted1351
def lo1352b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨16,by decide⟩
def lo1352b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨17,by decide⟩
def lo1352 : CheckedMoment :=
  CheckedMoment.ofBessel lo1352b1 lo1352b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1352b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨21,by decide⟩
def hi1352b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨22,by decide⟩
def hi1352 : CheckedMoment :=
  CheckedMoment.ofBessel hi1352b1 hi1352b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1352 : meanBracketCheck (817/1000) lo1352 hi1352=true := by decide +kernel
def bracket1352 : MeanBracket := meanBracketOfMoments (817/1000) lo1352 hi1352 accepted1352
def lo1353b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨26,by decide⟩
def lo1353b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨27,by decide⟩
def lo1353 : CheckedMoment :=
  CheckedMoment.ofBessel lo1353b1 lo1353b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1353b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨31,by decide⟩
def hi1353b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨32,by decide⟩
def hi1353 : CheckedMoment :=
  CheckedMoment.ofBessel hi1353b1 hi1353b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1353 : meanBracketCheck (327/400) lo1353 hi1353=true := by decide +kernel
def bracket1353 : MeanBracket := meanBracketOfMoments (327/400) lo1353 hi1353 accepted1353
def lo1354b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨36,by decide⟩
def lo1354b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨37,by decide⟩
def lo1354 : CheckedMoment :=
  CheckedMoment.ofBessel lo1354b1 lo1354b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1354b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨41,by decide⟩
def hi1354b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨42,by decide⟩
def hi1354 : CheckedMoment :=
  CheckedMoment.ofBessel hi1354b1 hi1354b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1354 : meanBracketCheck (409/500) lo1354 hi1354=true := by decide +kernel
def bracket1354 : MeanBracket := meanBracketOfMoments (409/500) lo1354 hi1354 accepted1354
def lo1355b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨46,by decide⟩
def lo1355b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨47,by decide⟩
def lo1355 : CheckedMoment :=
  CheckedMoment.ofBessel lo1355b1 lo1355b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1355b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨51,by decide⟩
def hi1355b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨52,by decide⟩
def hi1355 : CheckedMoment :=
  CheckedMoment.ofBessel hi1355b1 hi1355b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1355 : meanBracketCheck (1637/2000) lo1355 hi1355=true := by decide +kernel
def bracket1355 : MeanBracket := meanBracketOfMoments (1637/2000) lo1355 hi1355 accepted1355
def lo1356b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨56,by decide⟩
def lo1356b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨57,by decide⟩
def lo1356 : CheckedMoment :=
  CheckedMoment.ofBessel lo1356b1 lo1356b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1356b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨61,by decide⟩
def hi1356b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨62,by decide⟩
def hi1356 : CheckedMoment :=
  CheckedMoment.ofBessel hi1356b1 hi1356b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1356 : meanBracketCheck (819/1000) lo1356 hi1356=true := by decide +kernel
def bracket1356 : MeanBracket := meanBracketOfMoments (819/1000) lo1356 hi1356 accepted1356
def lo1357b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨2,by decide⟩
def lo1357b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨3,by decide⟩
def lo1357 : CheckedMoment :=
  CheckedMoment.ofBessel lo1357b1 lo1357b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1357b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨7,by decide⟩
def hi1357b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨8,by decide⟩
def hi1357 : CheckedMoment :=
  CheckedMoment.ofBessel hi1357b1 hi1357b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1357 : meanBracketCheck (1639/2000) lo1357 hi1357=true := by decide +kernel
def bracket1357 : MeanBracket := meanBracketOfMoments (1639/2000) lo1357 hi1357 accepted1357
def lo1358b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨12,by decide⟩
def lo1358b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨13,by decide⟩
def lo1358 : CheckedMoment :=
  CheckedMoment.ofBessel lo1358b1 lo1358b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1358b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨17,by decide⟩
def hi1358b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨18,by decide⟩
def hi1358 : CheckedMoment :=
  CheckedMoment.ofBessel hi1358b1 hi1358b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1358 : meanBracketCheck (41/50) lo1358 hi1358=true := by decide +kernel
def bracket1358 : MeanBracket := meanBracketOfMoments (41/50) lo1358 hi1358 accepted1358
def lo1359b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨22,by decide⟩
def lo1359b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨23,by decide⟩
def lo1359 : CheckedMoment :=
  CheckedMoment.ofBessel lo1359b1 lo1359b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1359b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨27,by decide⟩
def hi1359b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨28,by decide⟩
def hi1359 : CheckedMoment :=
  CheckedMoment.ofBessel hi1359b1 hi1359b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1359 : meanBracketCheck (1641/2000) lo1359 hi1359=true := by decide +kernel
def bracket1359 : MeanBracket := meanBracketOfMoments (1641/2000) lo1359 hi1359 accepted1359
#print axioms bracket1344
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0084
