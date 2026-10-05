module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0207
public import BecknerOnofri.EntropyScalarCertificate.Bessel0208
public import BecknerOnofri.EntropyScalarCertificate.Bessel0209

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0083
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1328b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨32,by decide⟩
def lo1328b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨33,by decide⟩
def lo1328 : CheckedMoment :=
  CheckedMoment.ofBessel lo1328b1 lo1328b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1328b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨37,by decide⟩
def hi1328b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨38,by decide⟩
def hi1328 : CheckedMoment :=
  CheckedMoment.ofBessel hi1328b1 hi1328b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1328 : meanBracketCheck (161/200) lo1328 hi1328=true := by decide +kernel
def bracket1328 : MeanBracket := meanBracketOfMoments (161/200) lo1328 hi1328 accepted1328
def lo1329b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨42,by decide⟩
def lo1329b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨43,by decide⟩
def lo1329 : CheckedMoment :=
  CheckedMoment.ofBessel lo1329b1 lo1329b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1329b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨47,by decide⟩
def hi1329b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨48,by decide⟩
def hi1329 : CheckedMoment :=
  CheckedMoment.ofBessel hi1329b1 hi1329b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1329 : meanBracketCheck (1611/2000) lo1329 hi1329=true := by decide +kernel
def bracket1329 : MeanBracket := meanBracketOfMoments (1611/2000) lo1329 hi1329 accepted1329
def lo1330b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨52,by decide⟩
def lo1330b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨53,by decide⟩
def lo1330 : CheckedMoment :=
  CheckedMoment.ofBessel lo1330b1 lo1330b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1330b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨57,by decide⟩
def hi1330b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨58,by decide⟩
def hi1330 : CheckedMoment :=
  CheckedMoment.ofBessel hi1330b1 hi1330b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1330 : meanBracketCheck (403/500) lo1330 hi1330=true := by decide +kernel
def bracket1330 : MeanBracket := meanBracketOfMoments (403/500) lo1330 hi1330 accepted1330
def lo1331b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨62,by decide⟩
def lo1331b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨63,by decide⟩
def lo1331 : CheckedMoment :=
  CheckedMoment.ofBessel lo1331b1 lo1331b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1331b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨3,by decide⟩
def hi1331b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨4,by decide⟩
def hi1331 : CheckedMoment :=
  CheckedMoment.ofBessel hi1331b1 hi1331b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1331 : meanBracketCheck (1613/2000) lo1331 hi1331=true := by decide +kernel
def bracket1331 : MeanBracket := meanBracketOfMoments (1613/2000) lo1331 hi1331 accepted1331
def lo1332b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨8,by decide⟩
def lo1332b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨9,by decide⟩
def lo1332 : CheckedMoment :=
  CheckedMoment.ofBessel lo1332b1 lo1332b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1332b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨13,by decide⟩
def hi1332b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨14,by decide⟩
def hi1332 : CheckedMoment :=
  CheckedMoment.ofBessel hi1332b1 hi1332b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1332 : meanBracketCheck (807/1000) lo1332 hi1332=true := by decide +kernel
def bracket1332 : MeanBracket := meanBracketOfMoments (807/1000) lo1332 hi1332 accepted1332
def lo1333b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨18,by decide⟩
def lo1333b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨19,by decide⟩
def lo1333 : CheckedMoment :=
  CheckedMoment.ofBessel lo1333b1 lo1333b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1333b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨23,by decide⟩
def hi1333b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨24,by decide⟩
def hi1333 : CheckedMoment :=
  CheckedMoment.ofBessel hi1333b1 hi1333b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1333 : meanBracketCheck (323/400) lo1333 hi1333=true := by decide +kernel
def bracket1333 : MeanBracket := meanBracketOfMoments (323/400) lo1333 hi1333 accepted1333
def lo1334b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨28,by decide⟩
def lo1334b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨29,by decide⟩
def lo1334 : CheckedMoment :=
  CheckedMoment.ofBessel lo1334b1 lo1334b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1334b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨33,by decide⟩
def hi1334b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨34,by decide⟩
def hi1334 : CheckedMoment :=
  CheckedMoment.ofBessel hi1334b1 hi1334b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1334 : meanBracketCheck (101/125) lo1334 hi1334=true := by decide +kernel
def bracket1334 : MeanBracket := meanBracketOfMoments (101/125) lo1334 hi1334 accepted1334
def lo1335b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨38,by decide⟩
def lo1335b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨39,by decide⟩
def lo1335 : CheckedMoment :=
  CheckedMoment.ofBessel lo1335b1 lo1335b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1335b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨43,by decide⟩
def hi1335b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨44,by decide⟩
def hi1335 : CheckedMoment :=
  CheckedMoment.ofBessel hi1335b1 hi1335b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1335 : meanBracketCheck (1617/2000) lo1335 hi1335=true := by decide +kernel
def bracket1335 : MeanBracket := meanBracketOfMoments (1617/2000) lo1335 hi1335 accepted1335
def lo1336b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨48,by decide⟩
def lo1336b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨49,by decide⟩
def lo1336 : CheckedMoment :=
  CheckedMoment.ofBessel lo1336b1 lo1336b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1336b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨53,by decide⟩
def hi1336b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨54,by decide⟩
def hi1336 : CheckedMoment :=
  CheckedMoment.ofBessel hi1336b1 hi1336b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1336 : meanBracketCheck (809/1000) lo1336 hi1336=true := by decide +kernel
def bracket1336 : MeanBracket := meanBracketOfMoments (809/1000) lo1336 hi1336 accepted1336
def lo1337b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨58,by decide⟩
def lo1337b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨59,by decide⟩
def lo1337 : CheckedMoment :=
  CheckedMoment.ofBessel lo1337b1 lo1337b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1337b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨63,by decide⟩
def hi1337b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨0,by decide⟩
def hi1337 : CheckedMoment :=
  CheckedMoment.ofBessel hi1337b1 hi1337b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1337 : meanBracketCheck (1619/2000) lo1337 hi1337=true := by decide +kernel
def bracket1337 : MeanBracket := meanBracketOfMoments (1619/2000) lo1337 hi1337 accepted1337
def lo1338b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨4,by decide⟩
def lo1338b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨5,by decide⟩
def lo1338 : CheckedMoment :=
  CheckedMoment.ofBessel lo1338b1 lo1338b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1338b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨9,by decide⟩
def hi1338b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨10,by decide⟩
def hi1338 : CheckedMoment :=
  CheckedMoment.ofBessel hi1338b1 hi1338b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1338 : meanBracketCheck (81/100) lo1338 hi1338=true := by decide +kernel
def bracket1338 : MeanBracket := meanBracketOfMoments (81/100) lo1338 hi1338 accepted1338
def lo1339b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨14,by decide⟩
def lo1339b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨15,by decide⟩
def lo1339 : CheckedMoment :=
  CheckedMoment.ofBessel lo1339b1 lo1339b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1339b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨19,by decide⟩
def hi1339b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨20,by decide⟩
def hi1339 : CheckedMoment :=
  CheckedMoment.ofBessel hi1339b1 hi1339b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1339 : meanBracketCheck (1621/2000) lo1339 hi1339=true := by decide +kernel
def bracket1339 : MeanBracket := meanBracketOfMoments (1621/2000) lo1339 hi1339 accepted1339
def lo1340b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨24,by decide⟩
def lo1340b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨25,by decide⟩
def lo1340 : CheckedMoment :=
  CheckedMoment.ofBessel lo1340b1 lo1340b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1340b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨29,by decide⟩
def hi1340b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨30,by decide⟩
def hi1340 : CheckedMoment :=
  CheckedMoment.ofBessel hi1340b1 hi1340b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1340 : meanBracketCheck (811/1000) lo1340 hi1340=true := by decide +kernel
def bracket1340 : MeanBracket := meanBracketOfMoments (811/1000) lo1340 hi1340 accepted1340
def lo1341b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨34,by decide⟩
def lo1341b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨35,by decide⟩
def lo1341 : CheckedMoment :=
  CheckedMoment.ofBessel lo1341b1 lo1341b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1341b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨39,by decide⟩
def hi1341b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨40,by decide⟩
def hi1341 : CheckedMoment :=
  CheckedMoment.ofBessel hi1341b1 hi1341b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1341 : meanBracketCheck (1623/2000) lo1341 hi1341=true := by decide +kernel
def bracket1341 : MeanBracket := meanBracketOfMoments (1623/2000) lo1341 hi1341 accepted1341
def lo1342b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨44,by decide⟩
def lo1342b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨45,by decide⟩
def lo1342 : CheckedMoment :=
  CheckedMoment.ofBessel lo1342b1 lo1342b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1342b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨49,by decide⟩
def hi1342b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨50,by decide⟩
def hi1342 : CheckedMoment :=
  CheckedMoment.ofBessel hi1342b1 hi1342b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1342 : meanBracketCheck (203/250) lo1342 hi1342=true := by decide +kernel
def bracket1342 : MeanBracket := meanBracketOfMoments (203/250) lo1342 hi1342 accepted1342
def lo1343b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨54,by decide⟩
def lo1343b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨55,by decide⟩
def lo1343 : CheckedMoment :=
  CheckedMoment.ofBessel lo1343b1 lo1343b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1343b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨59,by decide⟩
def hi1343b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨60,by decide⟩
def hi1343 : CheckedMoment :=
  CheckedMoment.ofBessel hi1343b1 hi1343b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1343 : meanBracketCheck (13/16) lo1343 hi1343=true := by decide +kernel
def bracket1343 : MeanBracket := meanBracketOfMoments (13/16) lo1343 hi1343 accepted1343
#print axioms bracket1328
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0083
