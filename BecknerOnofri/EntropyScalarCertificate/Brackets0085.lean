import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0212
import BecknerOnofri.EntropyScalarCertificate.Bessel0213
import BecknerOnofri.EntropyScalarCertificate.Bessel0214
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0085
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1360b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨32,by decide⟩
def lo1360b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨33,by decide⟩
def lo1360 : CheckedMoment :=
  CheckedMoment.ofBessel lo1360b1 lo1360b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1360b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨37,by decide⟩
def hi1360b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨38,by decide⟩
def hi1360 : CheckedMoment :=
  CheckedMoment.ofBessel hi1360b1 hi1360b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1360 : meanBracketCheck (821/1000) lo1360 hi1360=true := by decide +kernel
def bracket1360 : MeanBracket := meanBracketOfMoments (821/1000) lo1360 hi1360 accepted1360
def lo1361b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨42,by decide⟩
def lo1361b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨43,by decide⟩
def lo1361 : CheckedMoment :=
  CheckedMoment.ofBessel lo1361b1 lo1361b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1361b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨47,by decide⟩
def hi1361b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨48,by decide⟩
def hi1361 : CheckedMoment :=
  CheckedMoment.ofBessel hi1361b1 hi1361b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1361 : meanBracketCheck (1643/2000) lo1361 hi1361=true := by decide +kernel
def bracket1361 : MeanBracket := meanBracketOfMoments (1643/2000) lo1361 hi1361 accepted1361
def lo1362b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨52,by decide⟩
def lo1362b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨53,by decide⟩
def lo1362 : CheckedMoment :=
  CheckedMoment.ofBessel lo1362b1 lo1362b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1362b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨57,by decide⟩
def hi1362b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨58,by decide⟩
def hi1362 : CheckedMoment :=
  CheckedMoment.ofBessel hi1362b1 hi1362b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1362 : meanBracketCheck (411/500) lo1362 hi1362=true := by decide +kernel
def bracket1362 : MeanBracket := meanBracketOfMoments (411/500) lo1362 hi1362 accepted1362
def lo1363b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨62,by decide⟩
def lo1363b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨63,by decide⟩
def lo1363 : CheckedMoment :=
  CheckedMoment.ofBessel lo1363b1 lo1363b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1363b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨3,by decide⟩
def hi1363b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨4,by decide⟩
def hi1363 : CheckedMoment :=
  CheckedMoment.ofBessel hi1363b1 hi1363b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1363 : meanBracketCheck (329/400) lo1363 hi1363=true := by decide +kernel
def bracket1363 : MeanBracket := meanBracketOfMoments (329/400) lo1363 hi1363 accepted1363
def lo1364b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨8,by decide⟩
def lo1364b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨9,by decide⟩
def lo1364 : CheckedMoment :=
  CheckedMoment.ofBessel lo1364b1 lo1364b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1364b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨13,by decide⟩
def hi1364b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨14,by decide⟩
def hi1364 : CheckedMoment :=
  CheckedMoment.ofBessel hi1364b1 hi1364b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1364 : meanBracketCheck (823/1000) lo1364 hi1364=true := by decide +kernel
def bracket1364 : MeanBracket := meanBracketOfMoments (823/1000) lo1364 hi1364 accepted1364
def lo1365b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨18,by decide⟩
def lo1365b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨19,by decide⟩
def lo1365 : CheckedMoment :=
  CheckedMoment.ofBessel lo1365b1 lo1365b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1365b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨23,by decide⟩
def hi1365b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨24,by decide⟩
def hi1365 : CheckedMoment :=
  CheckedMoment.ofBessel hi1365b1 hi1365b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1365 : meanBracketCheck (1647/2000) lo1365 hi1365=true := by decide +kernel
def bracket1365 : MeanBracket := meanBracketOfMoments (1647/2000) lo1365 hi1365 accepted1365
def lo1366b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨28,by decide⟩
def lo1366b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨29,by decide⟩
def lo1366 : CheckedMoment :=
  CheckedMoment.ofBessel lo1366b1 lo1366b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1366b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨33,by decide⟩
def hi1366b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨34,by decide⟩
def hi1366 : CheckedMoment :=
  CheckedMoment.ofBessel hi1366b1 hi1366b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1366 : meanBracketCheck (103/125) lo1366 hi1366=true := by decide +kernel
def bracket1366 : MeanBracket := meanBracketOfMoments (103/125) lo1366 hi1366 accepted1366
def lo1367b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨38,by decide⟩
def lo1367b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨39,by decide⟩
def lo1367 : CheckedMoment :=
  CheckedMoment.ofBessel lo1367b1 lo1367b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1367b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨43,by decide⟩
def hi1367b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨44,by decide⟩
def hi1367 : CheckedMoment :=
  CheckedMoment.ofBessel hi1367b1 hi1367b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1367 : meanBracketCheck (1649/2000) lo1367 hi1367=true := by decide +kernel
def bracket1367 : MeanBracket := meanBracketOfMoments (1649/2000) lo1367 hi1367 accepted1367
def lo1368b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨48,by decide⟩
def lo1368b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨49,by decide⟩
def lo1368 : CheckedMoment :=
  CheckedMoment.ofBessel lo1368b1 lo1368b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1368b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨53,by decide⟩
def hi1368b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨54,by decide⟩
def hi1368 : CheckedMoment :=
  CheckedMoment.ofBessel hi1368b1 hi1368b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1368 : meanBracketCheck (33/40) lo1368 hi1368=true := by decide +kernel
def bracket1368 : MeanBracket := meanBracketOfMoments (33/40) lo1368 hi1368 accepted1368
def lo1369b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨58,by decide⟩
def lo1369b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨59,by decide⟩
def lo1369 : CheckedMoment :=
  CheckedMoment.ofBessel lo1369b1 lo1369b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1369b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨63,by decide⟩
def hi1369b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨0,by decide⟩
def hi1369 : CheckedMoment :=
  CheckedMoment.ofBessel hi1369b1 hi1369b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1369 : meanBracketCheck (1651/2000) lo1369 hi1369=true := by decide +kernel
def bracket1369 : MeanBracket := meanBracketOfMoments (1651/2000) lo1369 hi1369 accepted1369
def lo1370b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨4,by decide⟩
def lo1370b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨5,by decide⟩
def lo1370 : CheckedMoment :=
  CheckedMoment.ofBessel lo1370b1 lo1370b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1370b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨9,by decide⟩
def hi1370b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨10,by decide⟩
def hi1370 : CheckedMoment :=
  CheckedMoment.ofBessel hi1370b1 hi1370b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1370 : meanBracketCheck (413/500) lo1370 hi1370=true := by decide +kernel
def bracket1370 : MeanBracket := meanBracketOfMoments (413/500) lo1370 hi1370 accepted1370
def lo1371b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨14,by decide⟩
def lo1371b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨15,by decide⟩
def lo1371 : CheckedMoment :=
  CheckedMoment.ofBessel lo1371b1 lo1371b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1371b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨19,by decide⟩
def hi1371b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨20,by decide⟩
def hi1371 : CheckedMoment :=
  CheckedMoment.ofBessel hi1371b1 hi1371b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1371 : meanBracketCheck (1653/2000) lo1371 hi1371=true := by decide +kernel
def bracket1371 : MeanBracket := meanBracketOfMoments (1653/2000) lo1371 hi1371 accepted1371
def lo1372b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨24,by decide⟩
def lo1372b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨25,by decide⟩
def lo1372 : CheckedMoment :=
  CheckedMoment.ofBessel lo1372b1 lo1372b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1372b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨29,by decide⟩
def hi1372b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨30,by decide⟩
def hi1372 : CheckedMoment :=
  CheckedMoment.ofBessel hi1372b1 hi1372b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1372 : meanBracketCheck (827/1000) lo1372 hi1372=true := by decide +kernel
def bracket1372 : MeanBracket := meanBracketOfMoments (827/1000) lo1372 hi1372 accepted1372
def lo1373b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨34,by decide⟩
def lo1373b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨35,by decide⟩
def lo1373 : CheckedMoment :=
  CheckedMoment.ofBessel lo1373b1 lo1373b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1373b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨39,by decide⟩
def hi1373b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨40,by decide⟩
def hi1373 : CheckedMoment :=
  CheckedMoment.ofBessel hi1373b1 hi1373b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1373 : meanBracketCheck (331/400) lo1373 hi1373=true := by decide +kernel
def bracket1373 : MeanBracket := meanBracketOfMoments (331/400) lo1373 hi1373 accepted1373
def lo1374b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨44,by decide⟩
def lo1374b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨45,by decide⟩
def lo1374 : CheckedMoment :=
  CheckedMoment.ofBessel lo1374b1 lo1374b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1374b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨49,by decide⟩
def hi1374b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨50,by decide⟩
def hi1374 : CheckedMoment :=
  CheckedMoment.ofBessel hi1374b1 hi1374b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1374 : meanBracketCheck (207/250) lo1374 hi1374=true := by decide +kernel
def bracket1374 : MeanBracket := meanBracketOfMoments (207/250) lo1374 hi1374 accepted1374
def lo1375b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨54,by decide⟩
def lo1375b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨55,by decide⟩
def lo1375 : CheckedMoment :=
  CheckedMoment.ofBessel lo1375b1 lo1375b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1375b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨59,by decide⟩
def hi1375b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨60,by decide⟩
def hi1375 : CheckedMoment :=
  CheckedMoment.ofBessel hi1375b1 hi1375b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1375 : meanBracketCheck (1657/2000) lo1375 hi1375=true := by decide +kernel
def bracket1375 : MeanBracket := meanBracketOfMoments (1657/2000) lo1375 hi1375 accepted1375
#print axioms bracket1360
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0085
