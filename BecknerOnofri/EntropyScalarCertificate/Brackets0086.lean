module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0215
public import BecknerOnofri.EntropyScalarCertificate.Bessel0216
public import BecknerOnofri.EntropyScalarCertificate.Bessel0217

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0086
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1376b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨0,by decide⟩
def lo1376b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨1,by decide⟩
def lo1376 : CheckedMoment :=
  CheckedMoment.ofBessel lo1376b1 lo1376b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1376b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨5,by decide⟩
def hi1376b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨6,by decide⟩
def hi1376 : CheckedMoment :=
  CheckedMoment.ofBessel hi1376b1 hi1376b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1376 : meanBracketCheck (829/1000) lo1376 hi1376=true := by decide +kernel
def bracket1376 : MeanBracket := meanBracketOfMoments (829/1000) lo1376 hi1376 accepted1376
def lo1377b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨10,by decide⟩
def lo1377b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨11,by decide⟩
def lo1377 : CheckedMoment :=
  CheckedMoment.ofBessel lo1377b1 lo1377b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1377b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨15,by decide⟩
def hi1377b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨16,by decide⟩
def hi1377 : CheckedMoment :=
  CheckedMoment.ofBessel hi1377b1 hi1377b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1377 : meanBracketCheck (1659/2000) lo1377 hi1377=true := by decide +kernel
def bracket1377 : MeanBracket := meanBracketOfMoments (1659/2000) lo1377 hi1377 accepted1377
def lo1378b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨20,by decide⟩
def lo1378b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨21,by decide⟩
def lo1378 : CheckedMoment :=
  CheckedMoment.ofBessel lo1378b1 lo1378b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1378b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨25,by decide⟩
def hi1378b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨26,by decide⟩
def hi1378 : CheckedMoment :=
  CheckedMoment.ofBessel hi1378b1 hi1378b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1378 : meanBracketCheck (83/100) lo1378 hi1378=true := by decide +kernel
def bracket1378 : MeanBracket := meanBracketOfMoments (83/100) lo1378 hi1378 accepted1378
def lo1379b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨30,by decide⟩
def lo1379b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨31,by decide⟩
def lo1379 : CheckedMoment :=
  CheckedMoment.ofBessel lo1379b1 lo1379b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1379b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨35,by decide⟩
def hi1379b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨36,by decide⟩
def hi1379 : CheckedMoment :=
  CheckedMoment.ofBessel hi1379b1 hi1379b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1379 : meanBracketCheck (8301/10000) lo1379 hi1379=true := by decide +kernel
def bracket1379 : MeanBracket := meanBracketOfMoments (8301/10000) lo1379 hi1379 accepted1379
def lo1380b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨40,by decide⟩
def lo1380b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨41,by decide⟩
def lo1380 : CheckedMoment :=
  CheckedMoment.ofBessel lo1380b1 lo1380b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1380b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨45,by decide⟩
def hi1380b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨46,by decide⟩
def hi1380 : CheckedMoment :=
  CheckedMoment.ofBessel hi1380b1 hi1380b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1380 : meanBracketCheck (4151/5000) lo1380 hi1380=true := by decide +kernel
def bracket1380 : MeanBracket := meanBracketOfMoments (4151/5000) lo1380 hi1380 accepted1380
def lo1381b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨50,by decide⟩
def lo1381b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨51,by decide⟩
def lo1381 : CheckedMoment :=
  CheckedMoment.ofBessel lo1381b1 lo1381b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1381b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨55,by decide⟩
def hi1381b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨56,by decide⟩
def hi1381 : CheckedMoment :=
  CheckedMoment.ofBessel hi1381b1 hi1381b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1381 : meanBracketCheck (8303/10000) lo1381 hi1381=true := by decide +kernel
def bracket1381 : MeanBracket := meanBracketOfMoments (8303/10000) lo1381 hi1381 accepted1381
def lo1382b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨60,by decide⟩
def lo1382b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨61,by decide⟩
def lo1382 : CheckedMoment :=
  CheckedMoment.ofBessel lo1382b1 lo1382b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1382b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨1,by decide⟩
def hi1382b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨2,by decide⟩
def hi1382 : CheckedMoment :=
  CheckedMoment.ofBessel hi1382b1 hi1382b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1382 : meanBracketCheck (519/625) lo1382 hi1382=true := by decide +kernel
def bracket1382 : MeanBracket := meanBracketOfMoments (519/625) lo1382 hi1382 accepted1382
def lo1383b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨6,by decide⟩
def lo1383b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨7,by decide⟩
def lo1383 : CheckedMoment :=
  CheckedMoment.ofBessel lo1383b1 lo1383b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1383b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨11,by decide⟩
def hi1383b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨12,by decide⟩
def hi1383 : CheckedMoment :=
  CheckedMoment.ofBessel hi1383b1 hi1383b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1383 : meanBracketCheck (1661/2000) lo1383 hi1383=true := by decide +kernel
def bracket1383 : MeanBracket := meanBracketOfMoments (1661/2000) lo1383 hi1383 accepted1383
def lo1384b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨16,by decide⟩
def lo1384b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨17,by decide⟩
def lo1384 : CheckedMoment :=
  CheckedMoment.ofBessel lo1384b1 lo1384b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1384b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨21,by decide⟩
def hi1384b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨22,by decide⟩
def hi1384 : CheckedMoment :=
  CheckedMoment.ofBessel hi1384b1 hi1384b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1384 : meanBracketCheck (4153/5000) lo1384 hi1384=true := by decide +kernel
def bracket1384 : MeanBracket := meanBracketOfMoments (4153/5000) lo1384 hi1384 accepted1384
def lo1385b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨26,by decide⟩
def lo1385b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨27,by decide⟩
def lo1385 : CheckedMoment :=
  CheckedMoment.ofBessel lo1385b1 lo1385b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1385b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨31,by decide⟩
def hi1385b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨32,by decide⟩
def hi1385 : CheckedMoment :=
  CheckedMoment.ofBessel hi1385b1 hi1385b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1385 : meanBracketCheck (8307/10000) lo1385 hi1385=true := by decide +kernel
def bracket1385 : MeanBracket := meanBracketOfMoments (8307/10000) lo1385 hi1385 accepted1385
def lo1386b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨36,by decide⟩
def lo1386b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨37,by decide⟩
def lo1386 : CheckedMoment :=
  CheckedMoment.ofBessel lo1386b1 lo1386b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1386b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨41,by decide⟩
def hi1386b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨42,by decide⟩
def hi1386 : CheckedMoment :=
  CheckedMoment.ofBessel hi1386b1 hi1386b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1386 : meanBracketCheck (2077/2500) lo1386 hi1386=true := by decide +kernel
def bracket1386 : MeanBracket := meanBracketOfMoments (2077/2500) lo1386 hi1386 accepted1386
def lo1387b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨46,by decide⟩
def lo1387b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨47,by decide⟩
def lo1387 : CheckedMoment :=
  CheckedMoment.ofBessel lo1387b1 lo1387b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1387b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨51,by decide⟩
def hi1387b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨52,by decide⟩
def hi1387 : CheckedMoment :=
  CheckedMoment.ofBessel hi1387b1 hi1387b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1387 : meanBracketCheck (8309/10000) lo1387 hi1387=true := by decide +kernel
def bracket1387 : MeanBracket := meanBracketOfMoments (8309/10000) lo1387 hi1387 accepted1387
def lo1388b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨56,by decide⟩
def lo1388b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨57,by decide⟩
def lo1388 : CheckedMoment :=
  CheckedMoment.ofBessel lo1388b1 lo1388b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1388b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨61,by decide⟩
def hi1388b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨62,by decide⟩
def hi1388 : CheckedMoment :=
  CheckedMoment.ofBessel hi1388b1 hi1388b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1388 : meanBracketCheck (831/1000) lo1388 hi1388=true := by decide +kernel
def bracket1388 : MeanBracket := meanBracketOfMoments (831/1000) lo1388 hi1388 accepted1388
def lo1389b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨2,by decide⟩
def lo1389b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨3,by decide⟩
def lo1389 : CheckedMoment :=
  CheckedMoment.ofBessel lo1389b1 lo1389b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1389b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨7,by decide⟩
def hi1389b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨8,by decide⟩
def hi1389 : CheckedMoment :=
  CheckedMoment.ofBessel hi1389b1 hi1389b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1389 : meanBracketCheck (8311/10000) lo1389 hi1389=true := by decide +kernel
def bracket1389 : MeanBracket := meanBracketOfMoments (8311/10000) lo1389 hi1389 accepted1389
def lo1390b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨12,by decide⟩
def lo1390b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨13,by decide⟩
def lo1390 : CheckedMoment :=
  CheckedMoment.ofBessel lo1390b1 lo1390b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1390b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨17,by decide⟩
def hi1390b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨18,by decide⟩
def hi1390 : CheckedMoment :=
  CheckedMoment.ofBessel hi1390b1 hi1390b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1390 : meanBracketCheck (1039/1250) lo1390 hi1390=true := by decide +kernel
def bracket1390 : MeanBracket := meanBracketOfMoments (1039/1250) lo1390 hi1390 accepted1390
def lo1391b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨22,by decide⟩
def lo1391b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨23,by decide⟩
def lo1391 : CheckedMoment :=
  CheckedMoment.ofBessel lo1391b1 lo1391b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1391b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨27,by decide⟩
def hi1391b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨28,by decide⟩
def hi1391 : CheckedMoment :=
  CheckedMoment.ofBessel hi1391b1 hi1391b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1391 : meanBracketCheck (8313/10000) lo1391 hi1391=true := by decide +kernel
def bracket1391 : MeanBracket := meanBracketOfMoments (8313/10000) lo1391 hi1391 accepted1391
#print axioms bracket1376
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0086
