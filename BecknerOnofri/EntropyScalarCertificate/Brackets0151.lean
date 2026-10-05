module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0377
public import BecknerOnofri.EntropyScalarCertificate.Bessel0378
public import BecknerOnofri.EntropyScalarCertificate.Bessel0379

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0151
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2416b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨32,by decide⟩
def lo2416b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨33,by decide⟩
def lo2416 : CheckedMoment :=
  CheckedMoment.ofBessel lo2416b1 lo2416b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2416b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨37,by decide⟩
def hi2416b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨38,by decide⟩
def hi2416 : CheckedMoment :=
  CheckedMoment.ofBessel hi2416b1 hi2416b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2416 : meanBracketCheck (24769/25000) lo2416 hi2416=true := by decide +kernel
def bracket2416 : MeanBracket := meanBracketOfMoments (24769/25000) lo2416 hi2416 accepted2416
def lo2417b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨42,by decide⟩
def lo2417b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨43,by decide⟩
def lo2417 : CheckedMoment :=
  CheckedMoment.ofBessel lo2417b1 lo2417b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2417b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨47,by decide⟩
def hi2417b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨48,by decide⟩
def hi2417 : CheckedMoment :=
  CheckedMoment.ofBessel hi2417b1 hi2417b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2417 : meanBracketCheck (49539/50000) lo2417 hi2417=true := by decide +kernel
def bracket2417 : MeanBracket := meanBracketOfMoments (49539/50000) lo2417 hi2417 accepted2417
def lo2418b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨52,by decide⟩
def lo2418b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨53,by decide⟩
def lo2418 : CheckedMoment :=
  CheckedMoment.ofBessel lo2418b1 lo2418b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2418b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨57,by decide⟩
def hi2418b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨58,by decide⟩
def hi2418 : CheckedMoment :=
  CheckedMoment.ofBessel hi2418b1 hi2418b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2418 : meanBracketCheck (2477/2500) lo2418 hi2418=true := by decide +kernel
def bracket2418 : MeanBracket := meanBracketOfMoments (2477/2500) lo2418 hi2418 accepted2418
def lo2419b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨62,by decide⟩
def lo2419b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨63,by decide⟩
def lo2419 : CheckedMoment :=
  CheckedMoment.ofBessel lo2419b1 lo2419b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2419b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨3,by decide⟩
def hi2419b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨4,by decide⟩
def hi2419 : CheckedMoment :=
  CheckedMoment.ofBessel hi2419b1 hi2419b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2419 : meanBracketCheck (49541/50000) lo2419 hi2419=true := by decide +kernel
def bracket2419 : MeanBracket := meanBracketOfMoments (49541/50000) lo2419 hi2419 accepted2419
def lo2420b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨8,by decide⟩
def lo2420b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨9,by decide⟩
def lo2420 : CheckedMoment :=
  CheckedMoment.ofBessel lo2420b1 lo2420b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2420b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨13,by decide⟩
def hi2420b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨14,by decide⟩
def hi2420 : CheckedMoment :=
  CheckedMoment.ofBessel hi2420b1 hi2420b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2420 : meanBracketCheck (24771/25000) lo2420 hi2420=true := by decide +kernel
def bracket2420 : MeanBracket := meanBracketOfMoments (24771/25000) lo2420 hi2420 accepted2420
def lo2421b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨18,by decide⟩
def lo2421b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨19,by decide⟩
def lo2421 : CheckedMoment :=
  CheckedMoment.ofBessel lo2421b1 lo2421b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2421b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨23,by decide⟩
def hi2421b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨24,by decide⟩
def hi2421 : CheckedMoment :=
  CheckedMoment.ofBessel hi2421b1 hi2421b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2421 : meanBracketCheck (49543/50000) lo2421 hi2421=true := by decide +kernel
def bracket2421 : MeanBracket := meanBracketOfMoments (49543/50000) lo2421 hi2421 accepted2421
def lo2422b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨28,by decide⟩
def lo2422b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨29,by decide⟩
def lo2422 : CheckedMoment :=
  CheckedMoment.ofBessel lo2422b1 lo2422b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2422b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨33,by decide⟩
def hi2422b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨34,by decide⟩
def hi2422 : CheckedMoment :=
  CheckedMoment.ofBessel hi2422b1 hi2422b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2422 : meanBracketCheck (6193/6250) lo2422 hi2422=true := by decide +kernel
def bracket2422 : MeanBracket := meanBracketOfMoments (6193/6250) lo2422 hi2422 accepted2422
def lo2423b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨38,by decide⟩
def lo2423b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨39,by decide⟩
def lo2423 : CheckedMoment :=
  CheckedMoment.ofBessel lo2423b1 lo2423b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2423b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨43,by decide⟩
def hi2423b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨44,by decide⟩
def hi2423 : CheckedMoment :=
  CheckedMoment.ofBessel hi2423b1 hi2423b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2423 : meanBracketCheck (9909/10000) lo2423 hi2423=true := by decide +kernel
def bracket2423 : MeanBracket := meanBracketOfMoments (9909/10000) lo2423 hi2423 accepted2423
def lo2424b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨48,by decide⟩
def lo2424b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨49,by decide⟩
def lo2424 : CheckedMoment :=
  CheckedMoment.ofBessel lo2424b1 lo2424b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2424b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨53,by decide⟩
def hi2424b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨54,by decide⟩
def hi2424 : CheckedMoment :=
  CheckedMoment.ofBessel hi2424b1 hi2424b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2424 : meanBracketCheck (24773/25000) lo2424 hi2424=true := by decide +kernel
def bracket2424 : MeanBracket := meanBracketOfMoments (24773/25000) lo2424 hi2424 accepted2424
def lo2425b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨58,by decide⟩
def lo2425b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨59,by decide⟩
def lo2425 : CheckedMoment :=
  CheckedMoment.ofBessel lo2425b1 lo2425b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2425b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨63,by decide⟩
def hi2425b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨0,by decide⟩
def hi2425 : CheckedMoment :=
  CheckedMoment.ofBessel hi2425b1 hi2425b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2425 : meanBracketCheck (49547/50000) lo2425 hi2425=true := by decide +kernel
def bracket2425 : MeanBracket := meanBracketOfMoments (49547/50000) lo2425 hi2425 accepted2425
def lo2426b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨4,by decide⟩
def lo2426b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨5,by decide⟩
def lo2426 : CheckedMoment :=
  CheckedMoment.ofBessel lo2426b1 lo2426b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2426b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨9,by decide⟩
def hi2426b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨10,by decide⟩
def hi2426 : CheckedMoment :=
  CheckedMoment.ofBessel hi2426b1 hi2426b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2426 : meanBracketCheck (12387/12500) lo2426 hi2426=true := by decide +kernel
def bracket2426 : MeanBracket := meanBracketOfMoments (12387/12500) lo2426 hi2426 accepted2426
def lo2427b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨14,by decide⟩
def lo2427b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨15,by decide⟩
def lo2427 : CheckedMoment :=
  CheckedMoment.ofBessel lo2427b1 lo2427b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2427b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨19,by decide⟩
def hi2427b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨20,by decide⟩
def hi2427 : CheckedMoment :=
  CheckedMoment.ofBessel hi2427b1 hi2427b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2427 : meanBracketCheck (49549/50000) lo2427 hi2427=true := by decide +kernel
def bracket2427 : MeanBracket := meanBracketOfMoments (49549/50000) lo2427 hi2427 accepted2427
def lo2428b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨24,by decide⟩
def lo2428b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨25,by decide⟩
def lo2428 : CheckedMoment :=
  CheckedMoment.ofBessel lo2428b1 lo2428b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2428b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨29,by decide⟩
def hi2428b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨30,by decide⟩
def hi2428 : CheckedMoment :=
  CheckedMoment.ofBessel hi2428b1 hi2428b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2428 : meanBracketCheck (991/1000) lo2428 hi2428=true := by decide +kernel
def bracket2428 : MeanBracket := meanBracketOfMoments (991/1000) lo2428 hi2428 accepted2428
def lo2429b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨34,by decide⟩
def lo2429b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨35,by decide⟩
def lo2429 : CheckedMoment :=
  CheckedMoment.ofBessel lo2429b1 lo2429b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2429b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨39,by decide⟩
def hi2429b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨40,by decide⟩
def hi2429 : CheckedMoment :=
  CheckedMoment.ofBessel hi2429b1 hi2429b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2429 : meanBracketCheck (49551/50000) lo2429 hi2429=true := by decide +kernel
def bracket2429 : MeanBracket := meanBracketOfMoments (49551/50000) lo2429 hi2429 accepted2429
def lo2430b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨44,by decide⟩
def lo2430b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨45,by decide⟩
def lo2430 : CheckedMoment :=
  CheckedMoment.ofBessel lo2430b1 lo2430b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2430b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨49,by decide⟩
def hi2430b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨50,by decide⟩
def hi2430 : CheckedMoment :=
  CheckedMoment.ofBessel hi2430b1 hi2430b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2430 : meanBracketCheck (3097/3125) lo2430 hi2430=true := by decide +kernel
def bracket2430 : MeanBracket := meanBracketOfMoments (3097/3125) lo2430 hi2430 accepted2430
def lo2431b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨54,by decide⟩
def lo2431b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨55,by decide⟩
def lo2431 : CheckedMoment :=
  CheckedMoment.ofBessel lo2431b1 lo2431b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2431b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨59,by decide⟩
def hi2431b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨60,by decide⟩
def hi2431 : CheckedMoment :=
  CheckedMoment.ofBessel hi2431b1 hi2431b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2431 : meanBracketCheck (49553/50000) lo2431 hi2431=true := by decide +kernel
def bracket2431 : MeanBracket := meanBracketOfMoments (49553/50000) lo2431 hi2431 accepted2431
#print axioms bracket2416
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0151
